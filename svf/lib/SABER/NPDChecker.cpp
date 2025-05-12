#include "Graphs/IRGraph.h"
#include "Graphs/SVFG.h"
#include "Util/Casting.h"
#include "Util/Options.h"
#include "SABER/NPDChecker.h"
#include "Util/SVFBugReport.h"
#include "Util/ThreadAPI.h"

using namespace SVF;
using namespace SVFUtil;

void NPDChecker::initSrcs()
{
    const SVFGNode* nullptrNode = getSVFG()->getSVFGNode(0);
    if (auto n = SVFUtil::dyn_cast<NullPtrSVFGNode>(nullptrNode))
    {
        for (auto it = n->OutEdgeBegin(), eit = n->OutEdgeEnd(); it != eit; ++it)
        {
            const SVFGNode* node = (*it)->getDstNode();
            if (auto store = SVFUtil::dyn_cast<StoreSVFGNode>(node))
            {
                addToSources(node);
                addSrcToCSID(node, nullptr);
            }   
        }
        
    }
}

void  NPDChecker::initSnks()
{
    for (auto it = svfg->begin(), eit = svfg->end(); it != eit; ++it)
    {
        const SVFGNode* node = it->second;
        if (const LoadSVFGNode* loadnode = SVFUtil::dyn_cast<LoadSVFGNode>(node))
        {
            const PAGNode* loaddst = loadnode->getPAGDstNode();
            for (auto loadoutit = loadnode->OutEdgeBegin(), loadouteit = loadnode->OutEdgeEnd(); loadoutit != loadouteit; ++loadoutit)
            {
                const SVFGNode* loadoutnode = (*loadoutit)->getDstNode();
                if (const LoadSVFGNode* loadload = SVFUtil::dyn_cast<LoadSVFGNode>(loadoutnode)) 
                {
                    const PAGNode* loadloadsrc = loadload->getPAGSrcNode();
                    if (loadloadsrc == loaddst)
                    {
                        addToSinks(loadload);
                        addSinkToPAGNodeMap(loadnode, loaddst);
                        addSnkToCSID(loadnode, nullptr); // snk info
                    }
                }
                else if (const StoreSVFGNode* loadstore = SVFUtil::dyn_cast<StoreSVFGNode>(loadoutnode)) 
                {
                    const PAGNode* loadstoredst = loadstore->getPAGDstNode();
                    if (loadstoredst == loaddst)
                    {
                        addToSinks(loadstore);
                        addSinkToPAGNodeMap(loadnode, loaddst);
                        addSnkToCSID(loadnode, nullptr); // snk info
                    }
                }
            }
        }
    }
}

void NPDChecker::reportBug(ProgSlice* slice)
{
    if (slice->isSatisfiableForSomeSinks() == false) 
    {
        // some path reachable from nullptr node to sink (pointer dereference)
        GenericBug::EventStack eventStack;
        // eventStack.push_back(SVFBugEvent::SourceInst, slice->gets)
        slice->evalFinalCond2Event(eventStack);
        eventStack.push_back(
            SVFBugEvent(SVFBugEvent::SourceInst, slice->getSource()->getICFGNode()));
        report.addSaberBug(GenericBug::NULLPOINTERDEREFERENCE, eventStack);// TODO
    }
}