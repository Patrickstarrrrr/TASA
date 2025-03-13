#include "Graphs/PTIG.h"

using namespace SVF;
using namespace SVFUtil;
using namespace std;

PTIGEdge* PTIG::addPTIGEdge(NodeID src, NodeID dst)
{
    PTIGNode *srcNode = getPTIGNode(src);
    PTIGNode *dstNode = getPTIGNode(dst);
    if (hasEdge(srcNode, dstNode))
        return nullptr;
    PTIGEdge* edge = new PTIGEdge(srcNode, dstNode);

    bool inserted = edgeSet.insert(edge).second;
    (void)inserted; // Suppress warning of unused variable under release build
    assert(inserted && "new PTIGEdge not added??");

    srcNode->addOutgoingEdge(edge);
    dstNode->addIncomingEdge(edge);
    return edge;
}

void PTIG::buildPTIG(ConstraintGraph *g)
{
    nodeToRepMap = g->getNodeToRepMap();
    nodeToSubsMap = g->getNodeToSubsMap();
    for (auto it = g->begin(), eit = g->end(); it != eit; ++it)
    {
        addPTIGNode(new PTIGNode(it->first), it->first);
        nodeToReachableMap[it->first].set(it->first);
    }
    for (auto it = g->getDirectCGEdges().begin(), eit = g->getDirectCGEdges().end(); it != eit; ++it)
    {
        // PTIGEdge *edge = new PTIGEdge(getGNode((*it)->getSrcID()), getGNode((*it)->getDstID()));
        addPTIGEdge((*it)->getSrcID(), (*it)->getDstID());
    }
    for (auto it = g->getLoadCGEdges().begin(), eit = g->getLoadCGEdges().end(); it != eit; ++it)
    {
        addPTIGEdge((*it)->getSrcID(), (*it)->getDstID());
    }
}

NodeBS& PTIG::computeReachableRepNodes(NodeID id)
{
    NodeID rep = sccRepNode(id);
    if (computedNodes.test(rep))
        return nodeToReachableMap[rep];

    NodeBS res;
    res.set(rep);
    computedNodes.set(rep);

    PTIGNode* node = getPTIGNode(rep);
    for (auto it = node->InEdgeBegin(), eit = node->InEdgeEnd(); it != eit; ++it)
    {
        PTIGEdge *inEdge = *it;
        NodeID src = inEdge->getSrcID();
        NodeID srcRep = sccRepNode(src);

        if (computedNodes.test(srcRep))
            res |= nodeToReachableMap[srcRep];
        else
            res |= computeReachableRepNodes(srcRep);
    }

    nodeToReachableMap[rep] = res;
    return nodeToReachableMap[rep];
}

bool PTIG::isReachable(NodeID interested, NodeID from)
{
    NodeID repFrom = sccRepNode(from);
    NodeID repInterested = sccRepNode(interested);
    if (repFrom == repInterested) return true;

    if (!computedNodes.test(repInterested)) {
        computeReachableRepNodes(repInterested);
    }
    return nodeToReachableMap[repInterested].test(repFrom);
}