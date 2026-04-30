#include "SABER/MyUAFChecker.h"
#include "Util/SVFUtil.h"
#include "Util/Options.h"

using namespace SVF;
using namespace SVFUtil;



void  MyUAFChecker::initSnks()
{
    SVFIR* pag = getPAG();

    for(SVFIR::CSToArgsListMap::iterator it = pag->getCallSiteArgsMap().begin(),
            eit = pag->getCallSiteArgsMap().end(); it!=eit; ++it)
    {

        PTACallGraph::FunctionSet callees;
        getCallgraph()->getCallees(it->first,callees);
        for(PTACallGraph::FunctionSet::const_iterator cit = callees.begin(), ecit = callees.end(); cit!=ecit; cit++)
        {
            const SVFFunction* fun = *cit;
            if (isSinkLikeFun(fun))
            {
                SVFIR::SVFVarList &arglist = it->second;
                assert(!arglist.empty()	&& "no actual parameter at deallocation site?");
                /// we only choose pointer parameters among all the actual parameters
                for (SVFIR::SVFVarList::const_iterator ait = arglist.begin(),
                        aeit = arglist.end(); ait != aeit; ++ait)
                {
                    const PAGNode *pagNode = *ait;
                    if (pagNode->isPointer())
                    {
                        const SVFGNode *snk = getSVFG()->getActualParmVFGNode(pagNode, it->first);
                        addToSinks(snk);
                        freeSinkSVFGNodes.set(snk->getId());
                        addSinkToPAGNodeMap(snk, pagNode);
                        addSnkToCSID(snk, it->first); // snk info
                        // For any multi-level pointer e.g., XFree(void** pagNode) that passed into a ExtAPI::EFT_FREE_MULTILEVEL function (e.g., XFree),
                        // we will add the DstNode of a load edge, i.e., dummy = *pagNode
                        SVFStmt::SVFStmtSetTy& loads = const_cast<PAGNode*>(pagNode)->getOutgoingEdges(SVFStmt::Load);
                        for(const SVFStmt* ld : loads)
                        {
                            if(SVFUtil::isa<DummyValVar>(ld->getDstNode())) {
                                addToSinks(getSVFG()->getStmtVFGNode(ld));
                                freeSinkSVFGNodes.set(getSVFG()->getStmtVFGNode(ld)->getId());
                                addSinkToPAGNodeMap(snk, pagNode);
                                addSnkToCSID(getSVFG()->getStmtVFGNode(ld), it->first); // snk info
                            }
                        }
                    }
                }
            }
        }
    }

    for (auto derefnode: svfg->dereferenceSVFNodes)
    {
        addToSinks(derefnode);
        addSnkToCSID(derefnode, nullptr); // snk info
        useSinkSVFGNodes.set(derefnode->getId());
    }
    // for (auto it = svfg->begin(), eit = svfg->end(); it != eit; ++it)
    // {
    //     const SVFGNode* node = it->second;
    //     if (const LoadSVFGNode* loadnode = SVFUtil::dyn_cast<LoadSVFGNode>(node))
    //     {
    //         const PAGNode* loaddst = loadnode->getPAGDstNode();
    //         for (auto loadoutit = loadnode->OutEdgeBegin(), loadouteit = loadnode->OutEdgeEnd(); loadoutit != loadouteit; ++loadoutit)
    //         {
    //             const SVFGNode* loadoutnode = (*loadoutit)->getDstNode();
    //             if (const LoadSVFGNode* loadload = SVFUtil::dyn_cast<LoadSVFGNode>(loadoutnode)) 
    //             {
    //                 const PAGNode* loadloadsrc = loadload->getPAGSrcNode();
    //                 if (loadloadsrc == loaddst)
    //                 {
    //                     addToSinks(loadnode);
    //                     useSinkSVFGNodes.set(loadnode->getId());
    //                     addSinkToPAGNodeMap(loadnode, loaddst);
    //                     addSnkToCSID(loadnode, nullptr); // snk info
    //                 }
    //             }
    //             else if (const StoreSVFGNode* loadstore = SVFUtil::dyn_cast<StoreSVFGNode>(loadoutnode)) 
    //             {
    //                 const PAGNode* loadstoredst = loadstore->getPAGDstNode();
    //                 if (loadstoredst == loaddst)
    //                 {
    //                     addToSinks(loadnode);
    //                     useSinkSVFGNodes.set(loadnode->getId());
    //                     addSinkToPAGNodeMap(loadnode, loaddst);
    //                     addSnkToCSID(loadnode, nullptr); // snk info
    //                 }
    //             }
    //         }
    //     }
    // }
}

void MyUAFChecker::reportBug(ProgSlice* slice)
{
    if(slice->isSatisfiableForUAFSinks() == false)
    {
        GenericBug::EventStack eventStack;
        slice->evalFinalCond2Event(eventStack);
        eventStack.push_back(
            SVFBugEvent(SVFBugEvent::SourceInst, getSrcCSID(slice->getSource())));
        report.addSaberBug(GenericBug::USEAFTERFREE, eventStack);
    }
    // if(Options::ValidateTests())
    //     testsValidation(slice);
}

// void MyUAFChecker::reportBug(ProgSlice* slice)
// {
//     if(slice->isSatisfiableForSomeSinks() == false)
//     {
//         GenericBug::EventStack eventStack;
//         slice->evalFinalCond2Event(eventStack);
//         eventStack.push_back(
//             SVFBugEvent(SVFBugEvent::SourceInst, getSrcCSID(slice->getSource())));
//         report.addSaberBug(GenericBug::USEAFTERFREE, eventStack);
//     }
//     // if(Options::ValidateTests())
//     //     testsValidation(slice);
// }

// void MyUAFChecker::initSrcs()
// {
//     SVFIR* pag = getPAG();

//     for(SVFIR::CSToArgsListMap::iterator it = pag->getCallSiteArgsMap().begin(),
//             eit = pag->getCallSiteArgsMap().end(); it!=eit; ++it)
//     {

//         PTACallGraph::FunctionSet callees;
//         getCallgraph()->getCallees(it->first,callees);
//         for(PTACallGraph::FunctionSet::const_iterator cit = callees.begin(), ecit = callees.end(); cit!=ecit; cit++)
//         {
//             const SVFFunction* fun = *cit;
//             if (isSinkLikeFun(fun))
//             {
//                 SVFIR::SVFVarList &arglist = it->second;
//                 assert(!arglist.empty()	&& "no actual parameter at deallocation site?");
//                 /// we only choose pointer parameters among all the actual parameters
//                 for (SVFIR::SVFVarList::const_iterator ait = arglist.begin(),
//                         aeit = arglist.end(); ait != aeit; ++ait)
//                 {
//                     const PAGNode *pagNode = *ait;
//                     if (pagNode->isPointer())
//                     {
//                         const SVFGNode *snk = getSVFG()->getActualParmVFGNode(pagNode, it->first);
//                         addToSources(snk);
//                         addSourceToPAGNodeMap(snk, pagNode);
//                         addSrcToCSID(snk, it->first); // snk info
//                         // For any multi-level pointer e.g., XFree(void** pagNode) that passed into a ExtAPI::EFT_FREE_MULTILEVEL function (e.g., XFree),
//                         // we will add the DstNode of a load edge, i.e., dummy = *pagNode
//                         SVFStmt::SVFStmtSetTy& loads = const_cast<PAGNode*>(pagNode)->getOutgoingEdges(SVFStmt::Load);
//                         for(const SVFStmt* ld : loads)
//                         {
//                             if(SVFUtil::isa<DummyValVar>(ld->getDstNode())) {
//                                 addToSources(getSVFG()->getStmtVFGNode(ld));
//                                 addSourceToPAGNodeMap(snk, pagNode);
//                                 addSrcToCSID(getSVFG()->getStmtVFGNode(ld), it->first); // snk info
//                             }
//                         }
//                     }
//                 }
//             }
//         }
//     }
// }