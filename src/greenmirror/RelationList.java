package greenmirror;

import java.util.LinkedList;
import java.util.function.Predicate;
import java.util.stream.Collectors;

/**
 * A custom <code>LinkedList&gt;Relation&lt;</code> class which includes some filters.
 * 
 * @author Karim El Assal
 */
public class RelationList extends LinkedList<Relation> {
    
    
    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @return All A Nodes of all relations of this RelationList.
     */
    //@ ensures \result != null;
    /*@ pure */ public NodeList getNodesA() {
        NodeList nodes = new NodeList();
        this.forEach(relation -> nodes.add(relation.getNodeA()));
        return nodes;
    }
    
    /**
     * @param id
     * @return <code>Relation</code>s with the given <code>id</code>.
     */
    //@ requires id != null;
    //@ ensures \result != null;
    //@ ensures \result.size() <= this.size();
    /*@ pure */ public RelationList withId(String id) {
        return withFilter(relation -> id.equals(relation.getId()));
    }
    
    /**
     * @param name
     * @return <code>Relation</code>s with the given <code>name</code>.
     */
    //@ requires name != null;
    //@ ensures \result != null;
    //@ ensures \result.size() <= this.size();
    /*@ pure */ public RelationList withName(String name) {
        return withFilter(relation -> name.equals(relation.getName()));
    }

    /**
     * @param rigid
     * @return <code>Relation</code>s with the given <code>rigid</code>ity.
     */
    //@ requires rigid != null;
    //@ ensures \result != null;
    //@ ensures \result.size() <= this.size();
    /*@ pure */ public RelationList withIsRigid(boolean rigid) {
        return withFilter(relation -> relation.isRigid() == rigid);
    }

    /**
     * @param placement
     * @return <code>Relation</code>s with the given <code>placement</code>.
     */
    //@ requires placement != null;
    //@ ensures \result != null;
    //@ ensures \result.size() <= this.size();
    /*@ pure */ public RelationList withPlacement(Placement placement) {
        return withFilter(relation -> relation.getPlacement().equals(placement));
    }

    /**
     * @param placement
     * @return <code>Relation</code>s with any <code>placement</code> other than <code>NONE</code>.
     */
    //@ ensures \result != null;
    //@ ensures \result.size() <= this.size();
    /*@ pure */ public RelationList withPlacement() {
        return withFilter(relation -> !relation.getPlacement().equals(Placement.NONE));
    }

    /**
     * @return <code>Relation</code>s with no placement.
     */
    //@ ensures \result != null;
    //@ ensures \result.size() <= this.size();
    /*@ pure */ public RelationList withNoPlacement() {
        return withFilter(relation -> relation.getPlacement().equals(Placement.NONE));
    }

    /**
     * @param nodes
     * @return <code>Relation</code>s that are connected to one of the nodes of <code>nodes</code>.
     */
    //@ requires nodes != null;
    //@ ensures \result != null;
    //@ ensures \result.size() <= this.size();
    /*@ pure */ public RelationList withNodes(NodeList nodes) {
        return withFilter(relation -> 
                    nodes.contains(relation.getNodeA()) 
                 || nodes.contains(relation.getNodeB()));
    }

    /**
     * @param node
     * @return <code>Relation</code>s that are connected to <code>node</code>.
     */
    //@ requires node != null;
    //@ ensures \result != null;
    //@ ensures \result.size() <= this.size();
    /*@ pure */ public RelationList withNode(Node node) {
        return withFilter(relation -> 
                    node.equals(relation.getNodeA()) 
                 || node.equals(relation.getNodeB()));
    }

    /**
     * @param nodes
     * @return <code>Relation</code>s in which node A is one of the nodes of <code>nodes</code>.
     */
    //@ requires nodes != null;
    //@ ensures \result != null;
    //@ ensures \result.size() <= this.size();
    /*@ pure */ public RelationList withNodeA(NodeList nodes) {
        return withFilter(relation -> 
                    nodes.contains(relation.getNodeA()));
    }

    /**
     * @param node
     * @return <code>Relation</code>s in which node A equals <code>node</code>.
     */
    //@ requires node != null;
    //@ ensures \result != null;
    //@ ensures \result.size() <= this.size();
    /*@ pure */ public RelationList withNodeA(Node node) {
        return withFilter(relation -> 
                    node.equals(relation.getNodeA()));
    }

    /**
     * @param nodes
     * @return <code>Relation</code>s in which node B is one of the nodes of <code>nodes</code>.
     */
    //@ requires nodes != null;
    //@ ensures \result != null;
    //@ ensures \result.size() <= this.size();
    /*@ pure */ public RelationList withNodeB(NodeList nodes) {
        return withFilter(relation -> 
                    nodes.contains(relation.getNodeB()));
    }

    /**
     * @param node
     * @return <code>Relation</code>s in which node B equals <code>node</code>.
     */
    //@ requires node != null;
    //@ ensures \result != null;
    //@ ensures \result.size() <= this.size();
    /*@ pure */ public RelationList withNodeB(Node node) {
        return withFilter(relation -> 
                    node.equals(relation.getNodeB()));
    }
    
    /**
     * @param predicate The filter.
     * @return          A new <code>RelationList</code> with a filter applied.
     */
    //@ requires predicate != null;
    //@ ensures \result != null;
    //@ ensures \result.size() <= this.size();
    /*@ pure */ private RelationList withFilter(Predicate<Relation> predicate) {
        return this.stream().filter(predicate)
                .collect(Collectors.toCollection(RelationList::new));
    }
    

    // -- Commands ---------------------------------------------------------------------------

    /**
     * Remove all <code>Relation</code>s in this <code>RelationList</code>. Also removes this 
     * <code>Relation</code> from the connected <code>Node</code>s.
     */
    //@ ensures this.size() == 0;
    public void removeAll() {
        // We iterate of a copy of this <code>RelationList</code>, so we don't get concurrency errors.
        this.withFilter(relation -> true).forEach(relation -> {
            relation.removeFromNodes();
            this.remove(relation);
        });
    }

}