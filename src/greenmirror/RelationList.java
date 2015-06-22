package greenmirror;

import greenmirror.placements.NoPlacement;

import org.eclipse.jdt.annotation.NonNull;

import java.util.LinkedList;
import java.util.function.Predicate;
import java.util.stream.Collectors;

/**
 * A custom <code>LinkedList&gt;Relation&lt;</code> class providing specific filters.
 * 
 * @author Karim El Assal
 */
public class RelationList extends LinkedList<Relation> {
    
    
    // -- Constructors -----------------------------------------------------------------------
    
    /** Creates a new, empty list. */
    public RelationList() {
        
    }
    
    /** 
     * Creates a list from an array of <code>Relation</code>s. 
     * 
     * @param relations the relations to add to this <code>RelationList</code>
     **/
    public RelationList(@NonNull Relation... relations) {
        for (Relation relation : relations) {
            add(relation);
        }
    }
    
    /**
     * Creates a list from an existing list.
     * 
     * @param relations the relations to add to this <code>RelationList</code>
     */
    public RelationList(@NonNull RelationList relations) {
        super(relations);
    }
    
    
    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @return all nodes A of all relations on this <code>RelationList</code>
     */
    /*@ pure */ @NonNull public NodeList getNodesA() {
        final NodeList nodes = new NodeList();
        this.forEach(relation -> { 
            if (!nodes.contains(relation.getNodeA())) {
                nodes.add(relation.getNodeA());
            }
        });
        return nodes;
    }
    
    /**
     * @param id the relation id
     * @return   <code>Relation</code>s with the given <code>id</code>.
     */
    //@ ensures \result.size() <= this.size();
    /*@ pure */ @NonNull public RelationList withId(@NonNull String id) {
        return withFilter(relation -> id.equals(relation.getId()));
    }
    
    /**
     * @param name the relation name
     * @return     <code>Relation</code>s with the given <code>name</code>
     */
    //@ ensures \result.size() <= this.size();
    /*@ pure */ @NonNull public RelationList withName(@NonNull String name) {
        return withFilter(relation -> name.equals(relation.getName()));
    }

    /**
     * @param rigid the relation rigidity
     * @return      <code>Relation</code>s with the given <code>rigid</code>ity
     */
    //@ ensures \result.size() <= this.size();
    /*@ pure */ @NonNull public RelationList withIsRigid(boolean rigid) {
        return withFilter(relation -> relation.isRigid() == rigid);
    }

    /**
     * @param placement the relation placement
     * @return          <code>Relation</code>s with the given {@link Placement}
     */
    //@ ensures \result.size() <= this.size();
    /*@ pure */ @NonNull public RelationList withPlacement(@NonNull Placement placement) {
        return withFilter(relation -> relation.getPlacement().equals(placement));
    }

    /**
     * @return <code>Relation</code>s with any {@link Placement} other than {@link NoPlacement}
     */
    //@ ensures \result != null;
    //@ ensures \result.size() <= this.size();
    /*@ pure */ public RelationList withPlacement() {
        return withFilter(relation -> !relation.getPlacement().equals(Placement.NONE));
    }

    /**
     * @return <code>Relation</code>s with {@link NoPlacement}
     */
    //@ ensures \result.size() <= this.size();
    /*@ pure */ @NonNull public RelationList withNoPlacement() {
        return withFilter(relation -> relation.getPlacement().equals(Placement.NONE));
    }

    /**
     * @param nodes these nodes are relevant to the returned relations
     * @return      <code>Relation</code>s that are connected to one of the passed nodes
     */
    //@ ensures \result.size() <= this.size();
    /*@ pure */ @NonNull public RelationList withNodes(@NonNull NodeList nodes) {
        return withFilter(relation -> 
                    nodes.contains(relation.getNodeA()) 
                 || nodes.contains(relation.getNodeB()));
    }

    /**
     * @param node this node is relevant to the returned relations
     * @return <code>Relation</code>s that are connected to <code>node</code>.
     */
    //@ ensures \result.size() <= this.size();
    /*@ pure */ @NonNull public RelationList withNode(@NonNull Node node) {
        return withFilter(relation -> 
                    node.equals(relation.getNodeA()) 
                 || node.equals(relation.getNodeB()));
    }

    /**
     * @param nodes one of these nodes is node A of the returned relations
     * @return <code>Relation</code>s in which node A is one of the passed nodes
     */
    //@ ensures \result.size() <= this.size();
    /*@ pure */ @NonNull public RelationList withNodeA(@NonNull NodeList nodes) {
        return withFilter(relation -> 
                    nodes.contains(relation.getNodeA()));
    }

    /**
     * @param node this node is node A of the returned relations
     * @return <code>Relation</code>s in which node A equals <code>node</code>.
     */
    //@ ensures \result.size() <= this.size();
    /*@ pure */ @NonNull public RelationList withNodeA(@NonNull Node node) {
        return withFilter(relation -> 
                    node.equals(relation.getNodeA()));
    }

    /**
     * @param nodes one of these nodes is node B of the returned relations
     * @return <code>Relation</code>s in which node B is one of the passed nodes
     */
    //@ ensures \result.size() <= this.size();
    /*@ pure */ @NonNull public RelationList withNodeB(@NonNull NodeList nodes) {
        return withFilter(relation -> 
                    nodes.contains(relation.getNodeB()));
    }

    /**
     * @param node this node is node A of the returned relations
     * @return <code>Relation</code>s in which node B equals <code>node</code>.
     */
    //@ ensures \result.size() <= this.size();
    /*@ pure */ @NonNull public RelationList withNodeB(@NonNull Node node) {
        return withFilter(relation -> 
                    node.equals(relation.getNodeB()));
    }
    
    /**
     * @param predicate the filter
     * @return          a new <code>RelationList</code> with the filter applied
     */
    //@ ensures \result.size() <= this.size();
    /*@ pure */ @NonNull private RelationList withFilter(@NonNull Predicate<Relation> predicate) {
        final RelationList list = this.stream().filter(predicate)
                                      .collect(Collectors.toCollection(RelationList::new));
        return list == null ? new RelationList() : list; // just a formality for @NonNull
    }
    

    // -- Commands ---------------------------------------------------------------------------

    /**
     * Removes all <code>Relation</code>s in this <code>RelationList</code>. Also removes this 
     * <code>Relation</code> from the connected <code>Node</code>s.
     */
    //@ ensures this.size() == 0;
    public void removeAll() {
        // We iterate over a copy of this <code>RelationList</code>, so we don't get concurrency 
        //  errors.
        this.withFilter(relation -> true).forEach(relation -> {
            relation.removeFromNodes();
            this.remove(relation);
        });
    }

}