#ifndef PIG_H_
#define PIG_H_

#include "Graphs/ConsG.h"
#include "Graphs/GraphTraits.h"
#include "Util/WorkList.h"

namespace SVF
{

class PTIGNode;
class PTIGEdge;
typedef GenericNode<PTIGNode,PTIGEdge> GenericPTIGNodeTy;

class PTIGEdge : public GenericEdge<PTIGNode>
{
public:
    typedef GenericNode<PTIGNode,PTIGEdge>::GEdgeSetTy PTIGEdgeSetTy;
    PTIGEdge(PTIGNode* s, PTIGNode* d) : GenericEdge<PTIGNode>(s,d,0)
    {
    }
};

class PTIGNode : public GenericPTIGNodeTy
{
public:
    PTIGNode(NodeID i) : GenericPTIGNodeTy(i, OtherKd)
    {
    }
};

class PTIG: public GenericGraph<PTIGNode,PTIGEdge>
{
public:
    typedef OrderedMap<NodeID, ConstraintNode *> NodeIDToNodeMapTy;
    typedef PTIGEdge::PTIGEdgeSetTy::iterator PTIGNodeIter;
    typedef Map<NodeID, NodeID> NodeToRepMap;
    typedef Map<NodeID, NodeBS> NodeToSubsMap;
    typedef Map<NodeID, NodeBS> NodeToReachableMap;
    typedef FIFOWorkList<NodeID> WorkList;
    EdgeID edgeIndex;

    PTIGEdge::PTIGEdgeSetTy edgeSet;

    PTIG(ConstraintGraph* g)
    {
        buildPTIG(g);
    }

    void buildPTIG(ConstraintGraph* g);
    NodeBS& computeReachableRepNodes(NodeID id);
    bool isReachable(NodeID interested, NodeID from);

private:
    NodeToRepMap nodeToRepMap;
    NodeToSubsMap nodeToSubsMap;
    NodeToReachableMap nodeToReachableMap;
    NodeBS computedNodes;

    PTIGEdge* addPTIGEdge(NodeID src, NodeID dst);
    
    /// SCC rep/sub nodes methods
    //@{
    inline NodeID sccRepNode(NodeID id) const
    {
        NodeToRepMap::const_iterator it = nodeToRepMap.find(id);
        if(it==nodeToRepMap.end())
            return id;
        else
            return it->second;
    }
    inline NodeBS& sccSubNodes(NodeID id)
    {
        nodeToSubsMap[id].set(id);
        return nodeToSubsMap[id];
    }
    inline void setRep(NodeID node, NodeID rep)
    {
        nodeToRepMap[node] = rep;
    }
    inline void setSubs(NodeID node, NodeBS& subs)
    {
        nodeToSubsMap[node] |= subs;
    }
    inline void resetSubs(NodeID node)
    {
        nodeToSubsMap.erase(node);
    }
    inline NodeBS& getSubs(NodeID node)
    {
        return nodeToSubsMap[node];
    }
    inline NodeID getRep(NodeID node)
    {
        return nodeToRepMap[node];
    }
    inline void resetRep(NodeID node)
    {
        nodeToRepMap.erase(node);
    }
    //@}

    /// Get/add/remove constraint node
    //@{
    inline PTIGNode* getPTIGNode(NodeID id) const
    {
        id = sccRepNode(id);
        return getGNode(id);
    }
    inline void addPTIGNode(PTIGNode* node, NodeID id)
    {
        addGNode(id, node);
    }
    inline bool hasPTIGNode(NodeID id) const
    {
        id = sccRepNode(id);
        return hasGNode(id);
    }
    inline void removePTIGNode(PTIGNode* node)
    {
        removeGNode(node);
    }
    //@}

    inline bool hasEdge(PTIGNode* src, PTIGNode* dst)
    {
        PTIGEdge edge(src,dst);
        return edgeSet.find(&edge) != edgeSet.end();
        // return false;
    }

    inline PTIGEdge* getEdge(PTIGNode* src, PTIGNode* dst)
    {
        PTIGEdge edge(src,dst);
        auto eit = edgeSet.find(&edge);
        return *eit;
    }
};

}// End namespace SVF


#endif