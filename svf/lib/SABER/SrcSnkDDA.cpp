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


#include "Util/Options.h"
#include "Graphs/SVFG.h"
#include "SABER/SrcSnkDDA.h"
#include "Graphs/SVFGStat.h"
#include "SVFIR/SVFIR.h"
#include "SVFIR/SVFStatements.h"
#include "SVFIR/SVFValue.h"
#include "Util/Options.h"
#include "WPA/Andersen.h"

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
    if (Options::ComputeInputReachable() && Options::DFreeCheck())
    {
        std::cout << "Total DF Bugs:" << _curSlice->bugnum << "\n";
        std::cout << "Input Unreachable DF Bugs:" << _curSlice->inputsUnreachableBugs << "\n";
        unsigned unreachableSinks = 0;
        for (auto it = getSinks().begin(), eit = getSinks().end(); it != eit; ++it)
        {
            const SVFGNode* sink = *it;
            if (svfg->reachableSet.test(sink->getId()))
            {
                unreachableSinks++;
            }
        }
        std::cout << "Total Sinks:" << getSinks().size() << "\n";
        std::cout << "Input Unreachable Sinks:" << unreachableSinks << "\n";
    }
    if (Options::BranchBBInfo())
    {
        std::cout << "Compute Branch BB Info begin ...\n";
        
        Map<NodeID, Set<const SVFBasicBlock*>> svfgNodeToBBs;
        Map<NodeID, Set<const BranchStmt*>> svfgNodeToBranches;

        std::cout << "Collect Sink BWBB begin ...\n";
        // for (auto it = getSinks().begin(), eit = getSinks().end(); it != eit; ++it)
        for (NodeID sinkid : unreachableSinks)
        {
            // const SVFGNode* sink = *it;
            svfg->backwardReachableSet.clear();
            svfg->computeBackwardReachableNodesByID(sinkid);
            for (auto it : svfg->backwardReachableSet)
            {
                const SVFGNode* node = svfg->getSVFGNode(it);
                const SVFBasicBlock* bb = node->getICFGNode()->getBB();
                // std::cout << "Sink: " << sink->getId() << " BB: " << bb->getName() << "\n";
                svfgNodeToBBs[sinkid].insert(bb);
            }
        }
        std::cout << "Collect Sink BWBB end\n";
        std::cout << "Collect Branch begin ...\n";
        for (auto branchStmt : svfg->getPAG()->getSVFStmtSet(SVFStmt::Branch))
        {
            const BranchStmt* branch = SVFUtil::cast<BranchStmt>(branchStmt);
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
            }
        }
        std::cout << "Collect Branch end\n";
        
        int max = svfgNodeToBranches.begin()->second.size();
        int min = svfgNodeToBranches.begin()->second.size(); 
        float total = 0;
        for (auto it = svfgNodeToBranches.begin(), eit = svfgNodeToBranches.end(); it != eit; ++it)
        {
            if (max < it->second.size())
            {
                max = it->second.size();
            }
            if (min > it->second.size())
            {
                min = it->second.size();
            }
            total += it->second.size();
        }
        double avg = total / svfgNodeToBranches.size();
        std::cout << "Max Branches: " << max << "\n";
        std::cout << "Min Branches: " << min << "\n";
        std::cout << "Total Branches: " << total << "\n";
        std::cout << "Avg Branches: " << avg << "\n";
        std::cout << "Compute Branch BB Info end ...\n";
    }
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
