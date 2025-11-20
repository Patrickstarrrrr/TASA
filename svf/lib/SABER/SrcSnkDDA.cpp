//===- SrcSnkDDA.cpp -- Source-sink analyzer --------------------------------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013->  <Yulei Sui>
//

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.

// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===----------------------------------------------------------------------===//

/*
 * SrcSnkDDA.cpp
 *
 *  Created on: Apr 1, 2014
 *      Author: Yulei Sui
 */


#include "Graphs/ICFG.h"
#include "Graphs/ICFGNode.h"
#include "MSSA/SVFGBuilder.h"
#include "SVFIR/SVFType.h"
#include "Util/Options.h"
#include "Graphs/IRGraph.h"
#include "Graphs/SVFG.h"
#include "Graphs/VFGNode.h"
#include "SABER/SrcSnkDDA.h"
#include "Graphs/SVFGStat.h"
#include "SVFIR/SVFIR.h"
#include "SVFIR/SVFStatements.h"
#include "SVFIR/SVFValue.h"
#include "Util/GeneralType.h"
#include "Util/Options.h"
#include "Util/SVFUtil.h"
#include "WPA/Andersen.h"
#include "Graphs/PTIG.h"
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

using namespace SVF;
using namespace SVFUtil;

/// Initialize analysis
void SrcSnkDDA::initialize(SVFModule* module)
{
    SVFIR* pag = PAG::getPAG();

    AndersenWaveDiff* ander = AndersenWaveDiff::createAndersenWaveDiff(pag);
    memSSA.setSaberCondAllocator(getSaberCondAllocator());
    if(Options::SABERFULLSVFG())
        svfg =  memSSA.buildFullSVFG(ander);
    else
        svfg =  memSSA.buildPTROnlySVFG(ander);
    setGraph(memSSA.getSVFG());
    callgraph = ander->getCallGraph();
    //AndersenWaveDiff::releaseAndersenWaveDiff();
    /// allocate control-flow graph branch conditions
    getSaberCondAllocator()->allocate(getPAG()->getModule());

    initSrcs();
    initSnks();
}

void SrcSnkDDA::analyze(SVFModule* module)
{
    double analyzeStart = SVFStat::myClk();

    initialize(module);

    ContextCond::setMaxCxtLen(Options::CxtLimit());

    for (SVFGNodeSetIter iter = sourcesBegin(), eiter = sourcesEnd();
            iter != eiter; ++iter)
    {
        setCurSlice(*iter);

        DBOUT(DGENERAL, outs() << "Analysing slice:" << (*iter)->getId() << ")\n");
        ContextCond cxt;
        DPIm item((*iter)->getId(),cxt);
        forwardTraverse(item);

        /// do not consider there is bug when reaching a global SVFGNode
        /// if we touch a global, then we assume the client uses this memory until the program exits.
        if (getCurSlice()->isReachGlobal())
        {
            DBOUT(DSaber, outs() << "Forward analysis reaches globals for slice:" << (*iter)->getId() << ")\n");
        }
        else
        {
            DBOUT(DSaber, outs() << "Forward process for slice:" << (*iter)->getId() << " (size = " << getCurSlice()->getForwardSliceSize() << ")\n");

            for (SVFGNodeSetIter sit = getCurSlice()->sinksBegin(), esit =
                        getCurSlice()->sinksEnd(); sit != esit; ++sit)
            {
                ContextCond cxt;
                DPIm item((*sit)->getId(),cxt);
                backwardTraverse(item);
            }

            DBOUT(DSaber, outs() << "Backward process for slice:" << (*iter)->getId() << " (size = " << getCurSlice()->getBackwardSliceSize() << ")\n");

            if(Options::DumpSlice())
                annotateSlice(_curSlice);

            if(_curSlice->AllPathReachableSolve())
                _curSlice->setAllReachable();

            DBOUT(DSaber, outs() << "Guard computation for slice:" << (*iter)->getId() << ")\n");
        }

        reportBug(getCurSlice());
    }

    double analyzeEnd = SVFStat::myClk();
    double analyzeTime = (analyzeEnd - analyzeStart) / TIMEINTERVAL;
    std::cout << "Total SrcSnkDDA Analysis Time: " << analyzeTime << "\n";

    double postProcessStart = SVFStat::myClk();
    if (Options::ComputeInputReachable() && (Options::DFreeCheck() || Options::UAFCheck() || Options::NPDCheck()) && _curSlice != nullptr)
    {
        std::cout << "Total Bugs:" << _curSlice->bugnum << "\n";
        std::cout << "Input Unreachable Bugs:" << _curSlice->inputsUnreachableBugs << "\n";
        double computeInputReachableStart = SVFStat::myClk();
        unsigned unreachableSinkNum = 0;
        for (auto it = getSinks().begin(), eit = getSinks().end(); it != eit; ++it)
        {
            const SVFGNode* sink = *it;
            if (!(svfg->inputReachableSet.test(sink->getId())))
            {
                unreachableSinkNum++; 
            }
        }
        double computeInputReachableEnd = SVFStat::myClk();
        std::cout << "Total Sinks:" << getSinks().size() << "\n";
        std::cout << "Input Unreachable Sinks:" << unreachableSinkNum << "\n";
        double computeInputReachableTime = (computeInputReachableEnd - computeInputReachableStart) / TIMEINTERVAL;
        std::cout << "Compute Input Reachable Time: " << computeInputReachableTime << "\n";
    }
    if (Options::BranchBBInfo())
    {
        Map<NodeID, Set<const SVFBasicBlock*>> svfgNodeToBBs;
        Map<NodeID, Set<const SVFBasicBlock*>> svfgNodeToBBs_PTIA; // with points-to influence analysis
        Map<NodeID, Set<const BranchStmt*>> svfgNodeToBranches;
        Map<NodeID, Set<const BranchStmt*>> svfgNodeToBranches_PTIA;
        Map<NodeID, Set<const BranchStmt*>> svfgNodeToLoopBranches;
        Map<NodeID, Set<const BranchStmt*>> svfgNodeToNonLoopBranches;
        Map<NodeID, Set<const BranchStmt*>> svfgNodeToLoopBranches_PTIA;
        Map<NodeID, Set<const BranchStmt*>> svfgNodeToNonLoopBranches_PTIA;
        
        // for (auto it = getSinks().begin(), eit = getSinks().end(); it != eit; ++it)
        // Collect the bbs that are backward reachable from the input-unreachable-sinks.

        std::cout << "Build PTIA begin ...\n";
        double ptiaStart = SVFStat::myClk();
        AndersenWaveDiff* ander = AndersenWaveDiff::createAndersenWaveDiff(PAG::getPAG());
        PTIG* ptig = new PTIG(ander->getConstraintGraph());
        double ptiaEnd = SVFStat::myClk();
        double ptiaTime = (ptiaEnd - ptiaStart) / TIMEINTERVAL;
        std::cout << "Build PTIA end\n";
        std::cout << "PTIA Time: " << ptiaTime << "\n";

        float totalBranchNum = 0.0;
        int maxBranchNum = 0;
        int minBranchNum = INT32_MAX;
        int unreachableSinkNum = 0;
        for (NodeID sinkid: unreachableSinks)
        {
            unreachableSinkNum++;
            SVFGNode* sink = svfg->getSVFGNode(sinkid);
            const ICFGNode* icfgNode = sink->getICFGNode();
            // NodeID icfgNodeID = icfgNode->getId();
            int branchnum = icfg->getBackwardSliceBranchNum(icfgNode);
            totalBranchNum += branchnum;
            if (branchnum > maxBranchNum) {
                maxBranchNum = branchnum;
            }
            if (branchnum < minBranchNum) {
                minBranchNum = branchnum;
            }
        }
        std::cout << "Average Branch Num: " << (totalBranchNum / unreachableSinkNum) << "\n";
        std::cout << "Max Branch Num: " << maxBranchNum << "\n";
        std::cout << "Min Branch Num: " << minBranchNum << "\n";
        std::cout << "Total Unreachable Sinks: " << unreachableSinkNum << "\n";
        std::cout << "Total Branch Num: " << getPAG()->getSVFStmtSet(SVFStmt::Branch).size() << "\n";
        std::cout << "Collect Sink BWBB begin ...\n";
        double collectSinkBWBBStart = SVFStat::myClk();
        NodeBS gepInLoopSinks;
        Map<NodeID, NodeBS> sinkToBWReachableSet;
        for (NodeID sinkid : unreachableSinks)
        {
            // const SVFGNode* sink = *it;
            svfg->backwardReachableSet.clear();
            svfg->computeBackwardReachableNodesByID(sinkid);
            // SVFGNode* sinkNode = svfg->getSVFGNode(sinkid);
            PAGNode* sinkPAGNode = getPAG()->getGNode(sinkToPAGNodeMap[sinkid]);
            NodeBS ptigReachSet = ptig->computeReachableRepNodes(sinkPAGNode->getId());
            sinkToBWReachableSet[sinkid] = svfg->backwardReachableSet;
            for (auto it : svfg->backwardReachableSet)
            {
                const SVFGNode* node = svfg->getSVFGNode(it);
                const SVFBasicBlock* bb = node->getICFGNode()->getBB();
                // std::cout << "Sink: " << sink->getId() << " BB: " << bb->getName() << "\n";
                svfgNodeToBBs[sinkid].insert(bb);
                NodeID sinkPagNodeID = sinkPAGNode->getId();
                if (SVFUtil::isa<AddrVFGNode>(node)) {
                    const AddrVFGNode* addrNode = SVFUtil::cast<AddrVFGNode>(node);
                    const AddrStmt* addrStmt = SVFUtil::cast<AddrStmt>(addrNode->getPAGEdge());
                    NodeID dstID = addrStmt->getLHSVarID();
                    if (ptig->isReachable(sinkPagNodeID, dstID))
                    {
                        svfgNodeToBBs_PTIA[sinkid].insert(bb);
                    }
                }
                else if (SVFUtil::isa<CopyVFGNode>(node)) {
                    const CopyVFGNode* copyNode = SVFUtil::cast<CopyVFGNode>(node);
                    const CopyStmt* copyStmt = SVFUtil::cast<CopyStmt>(copyNode->getPAGEdge());
                    NodeID dstID = copyStmt->getLHSVarID();
                    if (ptig->isReachable(sinkPagNodeID, dstID))
                    {
                        svfgNodeToBBs_PTIA[sinkid].insert(bb);
                    }
                }
                else if (SVFUtil::isa<GepVFGNode>(node)) {
                    const GepVFGNode* gepNode = SVFUtil::cast<GepVFGNode>(node);
                    const GepStmt* gepStmt = SVFUtil::cast<GepStmt>(gepNode->getPAGEdge());
                    NodeID dstID = gepStmt->getLHSVarID();
                    if (ptig->isReachable(sinkPagNodeID, dstID))
                    {
                        svfgNodeToBBs_PTIA[sinkid].insert(bb);
                        // compute gep in loop
                        if (bb->getParent()->hasLoopInfo(bb)) {
                            gepInLoopSinks.set(sinkid);
                        }
                    }
                }
                else if (SVFUtil::isa<LoadVFGNode>(node)) {
                    const LoadVFGNode* loadNode = SVFUtil::cast<LoadVFGNode>(node);
                    const LoadStmt* loadStmt = SVFUtil::cast<LoadStmt>(loadNode->getPAGEdge());
                    NodeID dstID = loadStmt->getLHSVarID();
                    if (ptig->isReachable(sinkPagNodeID, dstID))
                    {
                        svfgNodeToBBs_PTIA[sinkid].insert(bb);
                    }
                }
                else if (SVFUtil::isa<StoreVFGNode>(node)) {
                    const StoreVFGNode* storeNode = SVFUtil::cast<StoreVFGNode>(node);
                    const StoreStmt* storeStmt = SVFUtil::cast<StoreStmt>(storeNode->getPAGEdge());
                    NodeID srcID = storeStmt->getRHSVarID();
                    if (ptig->isReachable(sinkPagNodeID, srcID))
                    {
                        svfgNodeToBBs_PTIA[sinkid].insert(bb);
                    }
                }
                else if (SVFUtil::isa<PHIVFGNode>(node)) {
                    const PHIVFGNode* phiNode = SVFUtil::cast<PHIVFGNode>(node);
                    const PAGNode* res = phiNode->getRes();
                    NodeID resID = res->getId();
                    if (ptig->isReachable(sinkPagNodeID, resID))
                    {
                        svfgNodeToBBs_PTIA[sinkid].insert(bb);
                    }
                }
                // else {
                //     svfgNodeToBBs_PTIA[sinkid].insert(bb);
                // }
            }
        }
        double collectSinkBWBBEnd = SVFStat::myClk();
        double collectSinkBWBBTime = (collectSinkBWBBEnd - collectSinkBWBBStart) / TIMEINTERVAL;
        std::cout << "Collect Sink BWBB end\n";
        std::cout << "Collect Sink BWBB Time: " << collectSinkBWBBTime << "\n";


        

        // Collect the branches that are backward reachable from the input-unreachable-sinks.
        std::cout << "Collect Branch begin ...\n";
        double collectBranchStart = SVFStat::myClk();
        for (auto branchStmt : svfg->getPAG()->getSVFStmtSet(SVFStmt::Branch))
        {
            const BranchStmt* branch = SVFUtil::cast<BranchStmt>(branchStmt);
            if (branch->isUnconditional())
            {
                continue;
            }
            auto succAndCondPairVec = branch->getSuccessors();
            for (auto succAndCondPair: succAndCondPairVec)
            {
                const ICFGNode* succ = succAndCondPair.first;
                const SVFBasicBlock* bb = succ->getBB();
                for (auto it = svfgNodeToBBs.begin(), eit = svfgNodeToBBs.end(); it != eit; ++it)
                {
                    if (it->second.find(bb) != it->second.end())
                    {
                        svfgNodeToBranches[it->first].insert(branch);
                    }
                }

                for (auto it = svfgNodeToBBs_PTIA.begin(), eit = svfgNodeToBBs_PTIA.end(); it != eit; ++it)
                {
                    if (it->second.find(bb) != it->second.end())
                    {
                        svfgNodeToBranches_PTIA[it->first].insert(branch);
                    }
                }
            }
        }
        double collectBranchEnd = SVFStat::myClk();
        double collectBranchTime = (collectBranchEnd - collectBranchStart) / TIMEINTERVAL;
        std::cout << "Collect Branch end\n";
        std::cout << "Collect Branch Time: " << collectBranchTime << "\n";
        
        if (!Options::EnablePTIG()) {
            if (svfgNodeToBranches.size() != 0)
            {
                
                double max = svfgNodeToBranches.begin()->second.size();
                double min = svfgNodeToBranches.begin()->second.size(); 
                double total = 0;
                
                for (auto it : unreachableSinks) {
                    // for each unreachable sink, find the key branches
                    auto branches = svfgNodeToBranches.find(it);
                    if (branches == svfgNodeToBranches.end())
                    {
                        continue;
                    }
                    int branchesNum = branches->second.size();
                    if (max < branchesNum)
                    {
                        max = branchesNum;
                    }
                    if (min > branchesNum)
                    {
                        min = branchesNum;
                    }
                    total += branchesNum;
                }
                double avg = total / unreachableSinks.count();
                std::cout << "Max Branches: " << max << "\n";
                std::cout << "Min Branches: " << min << "\n";
                std::cout << "Total Branches: " << total << "\n";
                std::cout << "Avg Branches: " << avg << "\n";
                std::cout << "*********************\n";
            } else {
                std::cout << "svfgNodeToBranches.size() == 0!\n";
            }
        }
        
        if (svfgNodeToBranches_PTIA.size() != 0) {
            double max_ptig = svfgNodeToBranches_PTIA.begin()->second.size();
            double min_ptig = svfgNodeToBranches_PTIA.begin()->second.size();
            double total_ptig = 0;

            for (auto it : unreachableSinks) {
                auto branches = svfgNodeToBranches_PTIA.find(it);
                if (branches == svfgNodeToBranches_PTIA.end())
                {
                    continue;
                }
                int branchesNum = branches->second.size();
                if (max_ptig < branchesNum)
                {
                    max_ptig = branchesNum;
                }
                if (min_ptig > branchesNum)
                {
                    min_ptig = branchesNum;
                }
                total_ptig += branchesNum;
            }
            double avg_ptig = total_ptig / unreachableSinks.count();
            std::cout << "Max PTIG Branches: " << max_ptig << "\n";
            std::cout << "Min PTIG Branches: " << min_ptig << "\n";
            std::cout << "Total PTIG Branches: " << total_ptig << "\n";
            std::cout << "Avg PTIG Branches: " << avg_ptig << "\n";

            std::cout << "Compute Branch BB Info end ...\n";
        } else {
            std::cout << "svfgNodeToBranches_PTIA.size() == 0!\n";
        }

        if (!Options::EnablePTIG()) {
            float noLoopSVFGNode = 0;
            float noGepInLoopSVFGNode = 0;
            for (auto it : unreachableSinks) {
                bool hasLoop = false;
                bool gepInLoop = false;
                unsigned totalbranches = 0;
                unsigned loopbranches = 0;
                if (gepInLoopSinks.test(it)) {
                    gepInLoop = true;
                }
                auto branches = svfgNodeToBranches.find(it);
                if (branches != svfgNodeToBranches.end())
                {
                    for (auto branchit = branches->second.begin(), ebranchit = branches->second.end(); branchit != ebranchit; ++branchit)
                    {
                        const BranchStmt* branch = *branchit;
                        const SVFBasicBlock* bb = branch->getBB();
                        
                        if (bb->getParent()->isLoopHeader(bb))
                        {
                            svfgNodeToLoopBranches[it].insert(branch);
                            hasLoop = true;
                        }
                        else {
                            svfgNodeToNonLoopBranches[it].insert(branch);
                        }
                    }
                    totalbranches = svfgNodeToBranches[it].size();
                    loopbranches = svfgNodeToLoopBranches[it].size();
                }

                if (!hasLoop)
                {
                    noLoopSVFGNode++;
                }
                if (!gepInLoop)
                {
                    noGepInLoopSVFGNode++;
                }
                std::cout << "GepInLoop: " << (gepInLoop? "[Y]":"[N]") << " Loopbranch:" << (hasLoop ? "[Y]":"[N]") << " SVFGNode: " << it << "Total Branches: " << totalbranches << " LoopBranches: " << loopbranches << "\n";
                if (!gepInLoop) {
                    std::cout << "LoopBranches:\n";
                    for (const BranchStmt* loopBranch: svfgNodeToLoopBranches[it])
                    {
                        std::cout << loopBranch->getValue()->getSourceFile() << ":" << loopBranch->getValue()->getSourceLine() << "\n";
                        // std::cout << loopBranch->getValue()->getSourceLoc() << "\n";
                    }
                    std::cout << "NonLoopBranches:\n";
                    for (const BranchStmt* nonLoopBranch: svfgNodeToNonLoopBranches[it])
                    {
                        std::cout << nonLoopBranch->getValue()->getSourceFile() << ":" << nonLoopBranch->getValue()->getSourceLine() << "\n";
                        // std::cout << nonLoopBranch->getValue()->getSourceLoc() << "\n";
                    }
                }
            }


            std::cout << "No Loop Branch SVFGNode Num:" << noLoopSVFGNode << "\n";
            std::cout << "No GepInLoop Branch SVFGNode Num:" << noGepInLoopSVFGNode << "\n";
            std::cout << "*********************\n";
        }

        double loopBranchComputeStart = SVFStat::myClk();
        float noLoopSVFGNode_PTIG = 0;
        float noGepInLoopSVFGNode_PTIG = 0;
        for (auto it : unreachableSinks) {
            bool hasLoop = false;
            bool gepInLoop = false;
            unsigned totalbranches = 0;
            unsigned loopbranches = 0;
            if (gepInLoopSinks.test(it)) {
                gepInLoop = true;
            }
            auto branches = svfgNodeToBranches_PTIA.find(it);
            if (branches != svfgNodeToBranches_PTIA.end())
            {
                for (auto branchit = branches->second.begin(), ebranchit = branches->second.end(); branchit != ebranchit; ++branchit)
                {
                    const BranchStmt* branch = *branchit;
                    const SVFBasicBlock* bb = branch->getBB();
                    if (bb->getParent()->isLoopHeader(bb))
                    {
                        svfgNodeToLoopBranches_PTIA[it].insert(branch);
                        hasLoop = true;
                    }
                    else {
                        svfgNodeToNonLoopBranches_PTIA[it].insert(branch);
                    }
                }
                totalbranches = svfgNodeToBranches_PTIA[it].size();
                loopbranches = svfgNodeToLoopBranches_PTIA[it].size();
            }
            if (!hasLoop)
            {
                noLoopSVFGNode_PTIG++;
            }
            if (!gepInLoop)
            {
                noGepInLoopSVFGNode_PTIG++;
            }
            std::cout << "GepInLoop: " << (gepInLoop? "[Y]":"[N]") << " Loopbranch:" << (hasLoop ? "[Y]":"[N]") << " SVFGNode: " << it << "Total Branches: " << totalbranches << " LoopBranches: " << loopbranches << "\n";
            if (!gepInLoop) {
                std::cout << "LoopBranches:\n";
                for (const BranchStmt* loopBranch: svfgNodeToLoopBranches_PTIA[it])
                {
                    std::cout << loopBranch->getValue()->getSourceFile() << ":" << loopBranch->getValue()->getSourceLine() << "\n";
                }
                std::cout << "NonLoopBranches:\n";
                for (const BranchStmt* nonLoopBranch: svfgNodeToNonLoopBranches_PTIA[it])
                {
                    std::cout << nonLoopBranch->getValue()->getSourceFile() << ":" << nonLoopBranch->getValue()->getSourceLine() << "\n";
                }
            }
        }
        double loopBranchComputeEnd = SVFStat::myClk();
        double loopBranchComputeTime = (loopBranchComputeEnd - loopBranchComputeStart) / TIMEINTERVAL;
        std::cout << "No Loop Branch SVFGNode Num:" << noLoopSVFGNode_PTIG << "\n";
        std::cout << "No GepInLoop Branch SVFGNode Num:" << noGepInLoopSVFGNode_PTIG << "\n";
        std::cout << "Loop Branch Compute Time: " << loopBranchComputeTime << "\n";
        std::cout << "*********************\n";
                    
        // Compute branch conflict
        
        double branchConflictComputeStart = SVFStat::myClk();
        for (auto it = svfgNodeToBranches_PTIA.begin(), eit = svfgNodeToBranches_PTIA.end(); it != eit; ++it)
        {
            keyBranches.insert(it->second.begin(), it->second.end());
        }
        
        buildBVConflictMap();
        double branchConflictComputeEnd = SVFStat::myClk();
        double branchConflictComputeTime = (branchConflictComputeEnd - branchConflictComputeStart) / TIMEINTERVAL;
        printBVConflictMap();
        std::cout << "Branch Conflict Compute Time: " << branchConflictComputeTime << "\n";
    }
    double postProcessEnd = SVFStat::myClk();
    double postProcessTime = (postProcessEnd - postProcessStart) / TIMEINTERVAL;
    std::cout << "Post Process Time: " << postProcessTime << "\n";

    finalize();

}


/*!
 * determine whether a SVFGNode n is in a allocation wrapper function,
 * if so, return all SVFGNodes which receive the value of node n
 */
bool SrcSnkDDA::isInAWrapper(const SVFGNode* src, CallSiteSet& csIdSet)
{

    bool reachFunExit = false;

    WorkList worklist;
    worklist.push(src);
    SVFGNodeBS visited;
    u32_t step = 0;
    while (!worklist.empty())
    {
        const SVFGNode* node  = worklist.pop();

        if(visited.test(node->getId())==0)
            visited.set(node->getId());
        else
            continue;
        // reaching maximum steps when traversing on SVFG to identify a memory allocation wrapper
        if (step++ > Options::MaxStepInWrapper())
            return false;

        for (SVFGNode::const_iterator it = node->OutEdgeBegin(), eit =
                    node->OutEdgeEnd(); it != eit; ++it)
        {
            const SVFGEdge* edge = (*it);
            //assert(edge->isDirectVFGEdge() && "the edge should always be direct VF");
            // if this is a call edge
            if(edge->isCallDirectVFGEdge())
            {
                return false;
            }
            // if this is a return edge
            else if(edge->isRetDirectVFGEdge())
            {
                reachFunExit = true;
                csIdSet.insert(getSVFG()->getCallSite(SVFUtil::cast<RetDirSVFGEdge>(edge)->getCallSiteId()));
            }
            // (1) an intra direct edge, we will keep tracking
            // (2) an intra indirect edge, we only track if the succ SVFGNode is a load, which means we only track one level store-load pair .
            // (3) do not track for all other interprocedural edges.
            else
            {
                const SVFGNode* succ = edge->getDstNode();
                if(SVFUtil::isa<IntraDirSVFGEdge>(edge))
                {
                    if (SVFUtil::isa<CopySVFGNode, GepSVFGNode, PHISVFGNode,
                            FormalRetSVFGNode, ActualRetSVFGNode,
                            StoreSVFGNode>(succ))
                    {
                        worklist.push(succ);
                    }
                }
                else if(SVFUtil::isa<IntraIndSVFGEdge>(edge))
                {
                    if(SVFUtil::isa<LoadSVFGNode, IntraMSSAPHISVFGNode>(succ))
                    {
                        worklist.push(succ);
                    }
                }
                else
                    return false;
            }
        }
    }
    if(reachFunExit)
        return true;
    else
        return false;
}


/*!
 * Propagate information forward by matching context
 */
void SrcSnkDDA::FWProcessOutgoingEdge(const DPIm& item, SVFGEdge* edge)
{
    DBOUT(DSaber,outs() << "\n##processing source: " << getCurSlice()->getSource()->getId() <<" forward propagate from (" << edge->getSrcID());

    // for indirect SVFGEdge, the propagation should follow the def-use chains
    // points-to on the edge indicate whether the object of source node can be propagated

    const SVFGNode* dstNode = edge->getDstNode();
    DPIm newItem(dstNode->getId(),item.getContexts());

    /// handle globals here
    if(isGlobalSVFGNode(dstNode) || getCurSlice()->isReachGlobal())
    {
        getCurSlice()->setReachGlobal();
        return;
    }


    /// perform context sensitive reachability
    // push context for calling
    if (edge->isCallVFGEdge())
    {
        CallSiteID csId = 0;
        if(const CallDirSVFGEdge* callEdge = SVFUtil::dyn_cast<CallDirSVFGEdge>(edge))
            csId = callEdge->getCallSiteId();
        else
            csId = SVFUtil::cast<CallIndSVFGEdge>(edge)->getCallSiteId();

        newItem.pushContext(csId);
        DBOUT(DSaber, outs() << " push cxt [" << csId << "] ");
    }
    // match context for return
    else if (edge->isRetVFGEdge())
    {
        CallSiteID csId = 0;
        if(const RetDirSVFGEdge* callEdge = SVFUtil::dyn_cast<RetDirSVFGEdge>(edge))
            csId = callEdge->getCallSiteId();
        else
            csId = SVFUtil::cast<RetIndSVFGEdge>(edge)->getCallSiteId();

        if (newItem.matchContext(csId) == false)
        {
            DBOUT(DSaber, outs() << "-|-\n");
            return;
        }
        DBOUT(DSaber, outs() << " pop cxt [" << csId << "] ");
    }

    /// whether this dstNode has been visited or not
    if(forwardVisited(dstNode,newItem))
    {
        DBOUT(DSaber,outs() << " node "<< dstNode->getId() <<" has been visited\n");
        return;
    }
    else
        addForwardVisited(dstNode, newItem);

    if(pushIntoWorklist(newItem))
        DBOUT(DSaber,outs() << " --> " << edge->getDstID() << ", cxt size: " << newItem.getContexts().cxtSize() <<")\n");

}

/*!
 * Propagate information backward without matching context, as forward analysis already did it
 */
void SrcSnkDDA::BWProcessIncomingEdge(const DPIm&, SVFGEdge* edge)
{
    DBOUT(DSaber,outs() << "backward propagate from (" << edge->getDstID() << " --> " << edge->getSrcID() << ")\n");
    const SVFGNode* srcNode = edge->getSrcNode();
    if(backwardVisited(srcNode))
        return;
    else
        addBackwardVisited(srcNode);

    ContextCond cxt;
    DPIm newItem(srcNode->getId(), cxt);
    pushIntoWorklist(newItem);
}

/// Set current slice
void SrcSnkDDA::setCurSlice(const SVFGNode* src)
{
    int totalbugs = 0;
    int halfreach = 0;
    int unreach = 0;
    if(_curSlice!=nullptr)
    {
        totalbugs = _curSlice->bugnum;
        halfreach = _curSlice->inputsHalfReachableBugs;
        unreach = _curSlice->inputsUnreachableBugs;
        delete _curSlice;
        _curSlice = nullptr;
        clearVisitedMap();
    }

    _curSlice = new ProgSlice(src,getSaberCondAllocator(), getSVFG(), this);
    _curSlice->bugnum = totalbugs;
    _curSlice->inputsHalfReachableBugs = halfreach;
    _curSlice->inputsUnreachableBugs = unreach;
}

void SrcSnkDDA::annotateSlice(ProgSlice* slice)
{
    getSVFG()->getStat()->addToSources(slice->getSource());
    for(SVFGNodeSetIter it = slice->sinksBegin(), eit = slice->sinksEnd(); it!=eit; ++it )
        getSVFG()->getStat()->addToSinks(*it);
    for(SVFGNodeSetIter it = slice->forwardSliceBegin(), eit = slice->forwardSliceEnd(); it!=eit; ++it )
        getSVFG()->getStat()->addToForwardSlice(*it);
    for(SVFGNodeSetIter it = slice->backwardSliceBegin(), eit = slice->backwardSliceEnd(); it!=eit; ++it )
        getSVFG()->getStat()->addToBackwardSlice(*it);
}

void SrcSnkDDA::dumpSlices()
{

    if(Options::DumpSlice())
        const_cast<SVFG*>(getSVFG())->dump("Slice",true);
}

void SrcSnkDDA::printZ3Stat()
{

    outs() << "Z3 Mem usage: " << getSaberCondAllocator()->getMemUsage() << "\n";
    outs() << "Z3 Number: " << getSaberCondAllocator()->getCondNum() << "\n";
}

// Reachable set computation with cycle-safe memoization
SrcSnkDDA::BBSet SrcSnkDDA::computeReachableBBs(const SVFBasicBlock* bb)
{
    if (reachCache.count(bb))
    {
        return reachCache[bb];
    }

    reachCache[bb] = {bb};
    for (const SVFBasicBlock* succ: bb->getSuccessors())
    {
        SrcSnkDDA::BBSet succReachable = computeReachableBBs(succ);
        reachCache[bb].insert(succReachable.begin(), succReachable.end());
    }

    return reachCache[bb];
}

bool SrcSnkDDA::containsBranch(BBSet& reachableBBs, const BranchStmt* branch)
{
    if (keyBranches.find(branch) == keyBranches.end())
    {
        return false;
    }
    for (const SVFBasicBlock* bb : reachableBBs)
    {
        if (branch->getBB() == bb)
        {
            return true;
        }
    }
    return false;
}

void SrcSnkDDA::buildBVConflictMap()
{
    std::vector<BranchValue> keyBVs;
    for (const BranchStmt* branch : keyBranches)
    {
        // branch->getEdgeID()
        for (u32_t i = 0; i < branch->getSuccessors().size(); ++i)
        {
            BranchValue bv = {branch, i == 0}; // true for first successor, false for second // TODO: switch stmt
            const SVFBasicBlock* bb = branch->getSuccessor(i)->getBB();
            bv2ReachableBBsMap[bv] = computeReachableBBs(bb);
            keyBVs.push_back(bv);
            bvConflictMap[bv] = {}; // Initialize the conflict set for this branch value
        }
    }
    
    for (size_t i = 0; i < keyBVs.size(); ++i)
    {
        const BranchValue& bv1 = keyBVs[i];
        BBSet& bv1ReachableBBs = bv2ReachableBBsMap[bv1];
        for (size_t j = i + 1; j < keyBVs.size(); ++j)
        {
            const BranchValue& bv2 = keyBVs[j];
            BBSet& bv2ReachableBBs = bv2ReachableBBsMap[bv2];
            // if (bv1.first == bv2.first && bv1.second != bv2.second) // Same branch, different successors
            // {
                // Check if they conflict
            if (bv1.first == bv2.first) continue; // Skip if they are the same branch
            if (!containsBranch(bv1ReachableBBs, bv2.first) &&  !containsBranch(bv2ReachableBBs, bv1.first))
            {
                bvConflictMap[bv1].insert(bv2);
                bvConflictMap[bv2].insert(bv1);
            }
            // }
        }
    }
}

void SrcSnkDDA::printBVConflictMap() const
{
    outs() << "========== Branch Value Conflict Map ==========\n";
    for (const auto& pair : bvConflictMap)
    {
        const BranchValue& bv = pair.first;
        const BVSet& conflicts = pair.second;
        if (conflicts.empty())
            continue; // Skip if there are no conflicts
        outs() << "Branch: " << bv.first->getValue()->getSourceFile() << ":" << bv.first->getValue()->getSourceLine()
               << " (" << (bv.second ? "T" : "F") << ") has conflicts with:\n";
        for (const BranchValue& conflict : conflicts)
        {
            outs() << "  - " << conflict.first->getValue()->getSourceFile() << ":" << conflict.first->getValue()->getSourceLine()
                   << " (" << (conflict.second ? "T" : "F") << ")\n";
        }
    }
}