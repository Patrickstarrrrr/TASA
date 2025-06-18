//===- ProgSlice.cpp -- Program slicing--------------------------------------//
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
 * ProgSlice.cpp
 *
 *  Created on: Apr 5, 2014
 *      Author: Yulei Sui
 */

#include "SABER/ProgSlice.h"
#include "Graphs/IRGraph.h"
#include "Graphs/SVFG.h"
#include "Graphs/VFGNode.h"
#include "SABER/LeakChecker.h"
#include "SVFIR/SVFValue.h"
#include "Util/Casting.h"
#include "Util/Options.h"
#include "Util/ThreadAPI.h"
#include <utility>

using namespace SVF;
using namespace SVFUtil;

/*!
 * Compute path conditions for nodes on the backward slice
 * path condition of each node is calculated starting from root node (source)
 * Given a SVFGNode n, its path condition C is allocated (path_i stands for one of m program paths reaches n)
 *
 * C = \bigvee Guard(path_i),  0 < i < m
 * Guard(path_i) = \bigwedge VFGGuard(x,y),  suppose (x,y) are two SVFGNode nodes on path_i
 */
bool ProgSlice::AllPathReachableSolve()
{
    const SVFGNode* source = getSource();
    VFWorkList worklist;
    worklist.push(source);
    /// mark source node conditions to be true
    setVFCond(source,getTrueCond());

    while(!worklist.empty())
    {
        const SVFGNode* node = worklist.pop();
        setCurSVFGNode(node);

        Condition invalidCond = computeInvalidCondFromRemovedSUVFEdge(node);
        Condition cond = getVFCond(node);
        for(SVFGNode::const_iterator it = node->OutEdgeBegin(), eit = node->OutEdgeEnd(); it!=eit; ++it)
        {
            const SVFGEdge* edge = (*it);
            const SVFGNode* succ = edge->getDstNode();
            if(inBackwardSlice(succ))
            {
                Condition vfCond;
                const SVFBasicBlock* nodeBB = getSVFGNodeBB(node);
                const SVFBasicBlock* succBB = getSVFGNodeBB(succ);
                if (nodeBB == nullptr || succBB == nullptr)
                {
                    continue;
                }
                /// clean up the control flow conditions for next round guard computation
                clearCFCond();

                if(edge->isCallVFGEdge())
                {
                    vfCond = ComputeInterCallVFGGuard(nodeBB,succBB, getCallSite(edge)->getParent());
                }
                else if(edge->isRetVFGEdge())
                {
                    vfCond = ComputeInterRetVFGGuard(nodeBB,succBB, getRetSite(edge)->getParent());
                }
                else
                    vfCond = ComputeIntraVFGGuard(nodeBB,succBB);
                vfCond = condAnd(vfCond, condNeg(invalidCond));
                Condition succPathCond = condAnd(cond, vfCond);
                if(setVFCond(succ,  condOr(getVFCond(succ), succPathCond) ))
                    worklist.push(succ);
            }

            DBOUT(DSaber, outs() << " node (" << node->getId()  <<
                  ") --> " << "succ (" << succ->getId() << ") condition: " << getVFCond(succ) << "\n");
        }
    }

    return isSatisfiableForAll();
}

/*!
 * Compute invalid branch condition stemming from removed strong update value-flow edges
 *
 * Fix issue: https://github.com/SVF-tools/SVF/issues/1306
 * Line 11->13 is removed due to a strong update at Line 13, which means Line 11 is unreachable to Line 13 on the value flow graph.
 * However on the control flow graph they are still considered as reachable,
 * making the vf guard on Line 11 -> Line 15 a true condition (should consider the infeasible branch Line 11 -> Line 13)
 * Therefore, we collect this infeasible branch condition (condition on Line 11 -> Line 13, `a == b`) as an invalid condition (invalidCond),
 * and add the negation of invalidCond when computing value flow guard starting from the source of the SU.
 * In this example, we add `a != b` on Line 11 -> Line 15.
 *
 * @param cur current SVFG node
 * @return invalid branch condition
 */
ProgSlice::Condition ProgSlice::computeInvalidCondFromRemovedSUVFEdge(const SVFGNode * cur)
{
    Set<const SVFBasicBlock*> validOutBBs; // the BBs of valid successors
    for(SVFGNode::const_iterator it = cur->OutEdgeBegin(), eit = cur->OutEdgeEnd(); it!=eit; ++it)
    {
        const SVFGEdge* edge = (*it);
        const SVFGNode* succ = edge->getDstNode();
        if(inBackwardSlice(succ))
        {
            validOutBBs.insert(getSVFGNodeBB(succ));
        }
    }
    Condition invalidCond = getFalseCond();
    auto suVFEdgesIt = getRemovedSUVFEdges().find(cur);
    if (suVFEdgesIt != getRemovedSUVFEdges().end())
    {
        for (const auto &succ: suVFEdgesIt->second)
        {
            if (!validOutBBs.count(getSVFGNodeBB(succ)))
            {
                // removed vfg node does not reside in the BBs of valid successors
                const SVFBasicBlock *nodeBB = getSVFGNodeBB(cur);
                const SVFBasicBlock *succBB = getSVFGNodeBB(succ);
                clearCFCond();
                invalidCond = condOr(invalidCond, ComputeIntraVFGGuard(nodeBB, succBB));
            }
        }
    }
    return invalidCond;
}

/*!
 * Solve by computing disjunction of conditions from all sinks (e.g., memory leak)
 */
bool ProgSlice::isSatisfiableForAll()
{

    Condition guard = getFalseCond();
    for(SVFGNodeSetIter it = sinksBegin(), eit = sinksEnd(); it!=eit; ++it)
    {
        guard = condOr(guard,getVFCond(*it));
    }
    setFinalCond(guard);

    return pathAllocator->isAllPathReachable(guard);
}

/*!
 * Solve by analysing each pair of sinks (e.g., double free)
 */
bool ProgSlice::isSatisfiableForPairs()
{
    bool ret = true;
    for(SVFGNodeSetIter it = sinksBegin(), eit = sinksEnd(); it!=eit; ++it)
    {
        for(SVFGNodeSetIter sit = it, esit = sinksEnd(); sit!=esit; ++sit)
        {
            if(*it == *sit)
                continue;
            Condition guard = condAnd(getVFCond(*sit),getVFCond(*it));
            if(!isEquivalentBranchCond(guard, getFalseCond()))
            {
                setFinalCond(guard);
                const SVFGNode* src = *it;
                const SVFGNode* dst = *sit;
                auto dda = (LeakChecker*)(ssDDA);
                if (Options::PrintDFBugSinkInfo())
                {
                    std::cout << "sink 1 at : (" 
                        << dda->getSnkCSID(src)->getSourceLoc()
                        << ")\n";
                    std::cout << "sink 2 at : (" 
                        << dda->getSnkCSID(dst)->getSourceLoc()
                        << ")\n";
                }
                if (Options::ComputeInputReachable())
                {
                    const SVFValue* srcvalue = src->getValue();
                    const SVFValue* dstvalue = dst->getValue();
                    const std::string srcloc = srcvalue->getSourceLoc();
                    const std::string dstloc = dstvalue->getSourceLoc();
                    NodeID srcid = (*it)->getId();
                    NodeID dstid = (*sit)->getId();
                    bool srcReach = svfg->reachableSet.test(srcid);
                    bool dstReach = svfg->reachableSet.test(dstid);
                    if (srcReach && dstReach) {
                        inputsReachableBugs++;
                        if (Options::PrintDFBugSinkInfo())
                        {
                            std::cout << "Both Reachable : (" 
                            << srcid << " at : [" << srcloc  << "]" 
                            << ", " 
                            << dstid << " at : [" << dstloc << "])\n";
                        }
                    }
                    else if (srcReach) {
                        inputsHalfReachableBugs++;
                        if (Options::PrintDFBugSinkInfo())
                        {
                            std::cout << "First Reachable : (" 
                            << srcid << " at : [" << srcloc  << "]" 
                            << ", " 
                            << dstid << " at : [" << dstloc << "])\n";
                        }
                    }
                    else if (dstReach) {
                        inputsHalfReachableBugs++;
                        if (Options::PrintDFBugSinkInfo())
                        {
                            std::cout << "Second Reachable : (" 
                            << srcid << " at : [" << srcloc  << "]" 
                            << ", " 
                            << dstid << " at : [" << dstloc << "])\n";
                        }
                    }
                    else {
                        inputsUnreachableBugs++;
                        if (Options::BranchBBInfo()) {
                            dda->unreachableSinks.set(srcid);
                            dda->unreachableSinks.set(dstid);
                        }
                        if (Options::PrintDFBugSinkInfo())
                        {
                            std::cout << "Both Unreachable : (" 
                            << srcid << " at : [" << srcloc  << "]" 
                            << ", " 
                            << dstid << " at : [" << dstloc << "])\n";
                        }
                    }
                }
                bugnum++;
                // return false;
                ret = false;
            }
        }
    }

    return ret;
}

/*!
 * Solve by analysing each sink to user (e.g., UAF)
 */
 bool ProgSlice::isSatisfiableForSinkToUser()
 {
    bool ret = true;
    for(SVFGNodeSetIter sinkit = sinksBegin(), sinkeit = sinksEnd(); sinkit!= sinkeit; ++sinkit)
    {
        const SVFGNode* sinknode = *sinkit;
        const PAGNode* sinkpagnode = ssDDA->getPAGNodeBySink(sinknode);
        if (sinkpagnode == nullptr)
            continue;
        ssDDA->getSVFG()->backwardReachableSet.clear();
        ssDDA->getSVFG()->computeBackwardReachableNodesByID(sinknode->getId());
        for (auto useit = this->forwardSliceBegin(), useeit = this->forwardSliceEnd(); useit != useeit; ++useit)
        {
            // svfg->reachableSet.clear();
            // svfg->computeReachableNodesByID(sinknode->getId());
            const SVFGNode* node = *useit;
            if ((ssDDA->getSVFG()->backwardReachableSet.test(node->getId())))
                continue; // backreachable from sink
            if (*useit == *sinkit)
                continue;
            const PAGNode* usepointer = nullptr;
            if (auto loaduse = SVFUtil::dyn_cast<LoadSVFGNode>(node))
            {
                usepointer = loaduse->getPAGSrcNode();
            }
            else if (auto storeuse = SVFUtil::dyn_cast<StoreSVFGNode>(node))
            {
                usepointer = storeuse->getPAGDstNode();
            }
            else if (auto gepuse = SVFUtil::dyn_cast<GepSVFGNode>(node))
            {
                usepointer = gepuse->getPAGSrcNode();
            }
            else if (auto copyuse = SVFUtil::dyn_cast<CopySVFGNode>(node))
            {
                usepointer = copyuse->getPAGSrcNode();
            }
            else if (auto phiuse = SVFUtil::dyn_cast<PHISVFGNode>(node))
            {
                usepointer = phiuse->getRes();
            }
            else if (auto addruse = SVFUtil::dyn_cast<AddrVFGNode>(node))
            {
                usepointer = addruse->getPAGDstNode();
            }
            else if (auto paramuse = SVFUtil::dyn_cast<ArgumentVFGNode>(node))
            {
                usepointer = paramuse->getParm();
            }
            if (usepointer == nullptr)
                continue;
            if(!(ssDDA->getSVFG()->getPTA()->alias(usepointer->getId(), sinkpagnode->getId())))
                continue;
            Condition guard = condAnd(getVFCond(sinknode),getVFCond(*useit));
            if(!isEquivalentBranchCond(guard, getFalseCond()))
            {
                setFinalCond(guard);
                const SVFGNode* src = *sinkit;
                const SVFGNode* dst = *useit;
                auto dda = (LeakChecker*)(ssDDA);
                // if (Options::PrintDFBugSinkInfo())
                // {
                //     std::cout << "sink at : (" 
                //         << dda->getSnkCSID(src)->getSourceLoc()
                //         << ")\n";
                //     std::cout << "use at : (" 
                //         // << dda->getSnkCSID(dst)->getSourceLoc()
                //         << usepointer->getSourceLoc()
                //         << ")\n";
                // }
                if (Options::ComputeInputReachable())
                {
                    const SVFValue* srcvalue = src->getValue();
                    const SVFValue* dstvalue = dst->getValue();
                    const std::string srcloc = srcvalue->getSourceLoc();
                    const std::string dstloc = dstvalue->getSourceLoc();
                    NodeID srcid = (*sinkit)->getId();
                    NodeID dstid = (*useit)->getId();
                    bool srcReach = ssDDA->getSVFG()->reachableSet.test(srcid);
                    bool dstReach = ssDDA->getSVFG()->reachableSet.test(dstid);
                    if (srcReach && dstReach) {
                        inputsReachableBugs++;
                        if (Options::PrintDFBugSinkInfo())
                        {
                            std::cout << "Both Reachable : (" 
                            << srcid << " at : [" << srcloc  << "]" 
                            << ", " 
                            << dstid << " at : [" << dstloc << "])\n";
                        }
                    }
                    else if (srcReach) {
                        inputsHalfReachableBugs++;
                        if (Options::PrintDFBugSinkInfo())
                        {
                            std::cout << "First Reachable : (" 
                            << srcid << " at : [" << srcloc  << "]" 
                            << ", " 
                            << dstid << " at : [" << dstloc << "])\n";
                        }
                    }
                    else if (dstReach) {
                        inputsHalfReachableBugs++;
                        if (Options::PrintDFBugSinkInfo())
                        {
                            std::cout << "Second Reachable : (" 
                            << srcid << " at : [" << srcloc  << "]" 
                            << ", " 
                            << dstid << " at : [" << dstloc << "])\n";
                        }
                    }
                    else {
                        inputsUnreachableBugs++;
                        if (Options::BranchBBInfo()) {
                            dda->unreachableSinks.set(srcid);
                            dda->unreachableSinks.set(dstid);
                        }
                        if (Options::PrintDFBugSinkInfo())
                        {
                            std::cout << "Both Unreachable : (" 
                            << srcid << " at : [" << srcloc  << "]" 
                            << ", " 
                            << dstid << " at : [" << dstloc << "])\n";
                        }
                    }
                }
                bugnum++;
                // return false;
                ret = false;
            }
        }
    }
 
    return ret;
}
/*!
 * Solve by analysing each sink to user (e.g., UAF)
 */
 bool ProgSlice::isSatisfiableForSomeSinks()
 {
    bool ret = true;
    for(SVFGNodeSetIter sinkit = sinksBegin(), sinkeit = sinksEnd(); sinkit!= sinkeit; ++sinkit)
    {
        const SVFGNode* sinknode = *sinkit;
        // const PAGNode* sinkpagnode = ssDDA->getPAGNodeBySink(sinknode);
        // if (sinkpagnode == nullptr)
        //     continue;
        Condition guard = getVFCond(sinknode);
        if (!isEquivalentBranchCond(guard, getFalseCond()))
        {
            setFinalCond(guard);
            // const SVFGNode* dst = *useit;
            auto dda = (LeakChecker*)(ssDDA);
            if (Options::ComputeInputReachable())
            {
                const SVFValue* srcvalue = sinknode->getValue();
                const std::string srcloc = srcvalue->getSourceLoc();
                NodeID srcid = (*sinkit)->getId();
                bool srcReach = ssDDA->getSVFG()->reachableSet.test(srcid);
                if (srcReach) {
                    inputsReachableBugs++;
                    if (Options::PrintDFBugSinkInfo())
                    {
                        std::cout << "Input Reachable : (" 
                        << srcid << " at : [" << srcloc  << "]\n";
                    }
                }
                else {
                    inputsUnreachableBugs++;
                    if (Options::BranchBBInfo()) {
                        dda->unreachableSinks.set(srcid);
                    }
                    if (Options::PrintDFBugSinkInfo())
                    {
                        std::cout << "Input Unreachable : (" 
                        << srcid << " at : [" << srcloc  << "]\n";
                    }
                }
            }
            bugnum++;
            ret = false;
        }
    }
    return ret;
}

const CallICFGNode* ProgSlice::getCallSite(const SVFGEdge* edge) const
{
    assert(edge->isCallVFGEdge() && "not a call svfg edge?");
    if(const CallDirSVFGEdge* callEdge = SVFUtil::dyn_cast<CallDirSVFGEdge>(edge))
        return getSVFG()->getCallSite(callEdge->getCallSiteId());
    else
        return getSVFG()->getCallSite(SVFUtil::cast<CallIndSVFGEdge>(edge)->getCallSiteId());
}
const CallICFGNode* ProgSlice::getRetSite(const SVFGEdge* edge) const
{
    assert(edge->isRetVFGEdge() && "not a return svfg edge?");
    if(const RetDirSVFGEdge* callEdge = SVFUtil::dyn_cast<RetDirSVFGEdge>(edge))
        return getSVFG()->getCallSite(callEdge->getCallSiteId());
    else
        return getSVFG()->getCallSite(SVFUtil::cast<RetIndSVFGEdge>(edge)->getCallSiteId());
}

void ProgSlice::evalFinalCond2Event(GenericBug::EventStack &eventStack) const
{
    NodeBS elems = pathAllocator->exactCondElem(finalCond);
    for(NodeBS::iterator it = elems.begin(), eit = elems.end(); it!=eit; ++it)
    {
        const ICFGNode* tinst = pathAllocator->getCondInst(*it);
        if(pathAllocator->isNegCond(*it))
            eventStack.push_back(SVFBugEvent(
                                     SVFBugEvent::Branch|((((u32_t)false) << 4) & BRANCHFLAGMASK), tinst));
        else
            eventStack.push_back(SVFBugEvent(
                                     SVFBugEvent::Branch|((((u32_t)true) << 4) & BRANCHFLAGMASK), tinst));
    }
}

/*!
 * Evaluate Atoms of a condition
 * TODO: for now we only evaluate one path, evaluate every single path
 *
 * Atom -- a propositional variable: a, b, c
 * Literal -- an atom or its negation: a, ~a
 * Clause  -- A disjunction of some literals: a \vee b
 * CNF formula -- a conjunction of some clauses:  (a \vee b ) \wedge (c \vee d)
 */
std::string ProgSlice::evalFinalCond() const
{
    std::string str;
    std::stringstream rawstr(str);
    Set<std::string> locations;
    NodeBS elems = pathAllocator->exactCondElem(finalCond);

    for(NodeBS::iterator it = elems.begin(), eit = elems.end(); it!=eit; ++it)
    {
        const ICFGNode* tinst = pathAllocator->getCondInst(*it);
        if(pathAllocator->isNegCond(*it))
            locations.insert(tinst->getSourceLoc()+"|False");
        else
            locations.insert(tinst->getSourceLoc()+"|True");
    }

    /// print leak path after eliminating duplicated element
    for(Set<std::string>::iterator iter = locations.begin(), eiter = locations.end();
            iter!=eiter; ++iter)
    {
        rawstr << "\t\t  --> (" << *iter << ") \n";
    }

    return rawstr.str();
}

void ProgSlice::destroy()
{
}
