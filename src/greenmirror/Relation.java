package greenmirror;

import org.eclipse.jdt.annotation.NonNull;

import java.util.Arrays;
import java.util.List;

/**
 * A class to model relations between <code>Node</code>s.
 * <p>
 * Relations are always directional: going from node A to node B. Although a name is not
 * required, it is recommended to always specify one.
 * 
 * @author Karim El Assal
 */
public class Relation implements Cloneable {


    // -- Instance variables -----------------------------------------------------------------
    
    /**
     * the <code>Node</code>s between this <code>Relation</code> exists. This 
     * <code>Relation</code> is directed from <code>Node</code> A to <code>Node</code> B
     */
    private Node nodeA = null;
    private Node nodeB = null;
    
    /** the optional name of this <code>Relation</code> */
    private String name = null;
    
    /** whether <code>Node</code> A moves when <code>Node</code> B moves */
    private boolean rigid = false;

    /** the <code>Placement</code> of <code>Node</code> A relative to <code>Node</code> B */
    @NonNull private Placement placement = Placement.NONE;
    
    /** the FX of <code>Node</code> A for the duration of this <code>Relation</code>. Optional */
    private FxWrapper temporaryFxOfNodeA = null;

    
    // -- Constructors -----------------------------------------------------------------------

    /**
     * Creates a <code>Relation</code> with a specific <code>name</code>.
     * 
     * @param name the name of this relation
     */
    //@ ensures name.equals(getName());
    public Relation(String name) {
        setName(name);
    }

    /** Creates a <code>Relation</code> without specifying anything. */
    public Relation() {}
    
    
    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * Returns an id that is as unique as it can get on the basis of the current properties.
     * It is of the format "nodeAid|relationName|nodeBid|placementString|isRigid" where "nodeAid"
     * and "nodeBid" are empty string when they are <code>null</code>. "isRigid" will be replaced
     * by "true" or "false" accordingly.
     * 
     * @return a (sort of) unique id
     */
    /*@ pure */ @NonNull public String getId() {
        return (getNodeA() == null ? "" : getNodeA().getId()) + "|"
              + getName() + "|"
             + (getNodeB() == null ? "" : getNodeB().getId()) + "|"
             + getPlacement().toString() + "|"
             + String.valueOf(isRigid());
    }
    
    /** @return node A */
    /*@ pure */ public Node getNodeA() {
        return nodeA;
    }
    
    /** @return node B */
    /*@ pure */ public Node getNodeB() {
        return nodeB;
    }
    
    /**
     * Returns the node on the other side of this relation than <code>firstNode</code> is.
     * 
     * @param firstNode the node you DON'T want
     * @return          the node connected to <code>firstNode</code> due to this 
     *                  <code>Relation</code>; <code>null</code> if <code>firstNode</code> 
     *                  is not part of this <code>Relation</code> or if the other node is
     *                  <code>null</code>
     */
    /*@ pure */ public Node getOtherNode(@NonNull Node firstNode) {
        if (firstNode.equals(getNodeA())) {
            return getNodeB();
        } else if (firstNode.equals(getNodeB())) {
            return getNodeA();
        } else {
            return null;
        }
    }

    /**
     * @return the name of this relation: <code>null</code> if it is not set
     */
    /*@ pure */ public String getName() {
        return name;
    }

    /** @return <code>true</code> if this is a rigid relation: if node A moves when node B moves */
    /*@ pure */ public boolean isRigid() {
        return rigid;
    }
    
    /** @return the <code>Placement</code> of node A relative to node b */
    /*@ pure */ @NonNull public Placement getPlacement() {
        return placement;
    }
    
    /** @return the FX of node A for the duration of this <code>Relation</code> */
    /*@ pure */ public FxWrapper getTemporaryFxOfNodeA() {
        return temporaryFxOfNodeA;
    }
    
    /** @return a textual description of this <code>Relation</code> containing all properties */
    @Override @NonNull 
    /*@ pure */ public String toString() {
        return
              "Relation name=" + (getName() == null ? "" : getName())
            + "|fromNode=" + (getNodeA() == null ? "" : 
                        (getNodeA().getId() == null ? "" : Log.n(getNodeA())))
            + "|toNode=" + (getNodeB() == null ? "" : 
                        (getNodeB().getId() == null ? "" : Log.n(getNodeB())))
            + "|placement=" + getPlacement().toString()
            + "|rigid=" + (isRigid() ? "true" : "false")
            + "|temporaryFxOfNodeA="
            + (getTemporaryFxOfNodeA() == null ? "not_set" : "set");
    }
    

    // -- Setters ----------------------------------------------------------------------------

    /**
     * Sets the starting node of this directional relation.
     * 
     * @param node the node that will be set as node A
     * @return     <code>this</code>
     * @throws IllegalStateException if node A is being set while a temporary FX is set, but 
     *                               node A doesn't have its own FX (and <code>node</code> is
     *                               not <code>null</code>)
     */
    //@ ensures getNodeA() == node;
    //@ ensures \result == this;
    @NonNull public Relation setNodeA(Node node) {
        if (getTemporaryFxOfNodeA() != null && node != null && node.getFxWrapper() == null) {
            throw new IllegalStateException("node A should have its own FX if it's going "
                    + "to receive a temporary FX");
        }
        nodeA = node;
        return this;
    }
    
    /**
     * Sets node A to the next node in the list of <code>nodes</code>. If the end of the list 
     * is reached, the first is selected.
     * 
     * @param nodes the nodes to choose from
     * @return      <code>this</code>
     * @throws IllegalArgumentException if no node could be chosen from the list
     */
    //@ requires !nodes.isEmpty();
    //@ ensures getNodeA() == nodes.getCircularNext(getNodeA());
    //@ ensures \result == this;
    @NonNull public Relation setNextNodeA(@NonNull NodeList nodes) {
        Node node = null;
        try {
            node = nodes.getCircularNext(getNodeA());
        } catch (NullPointerException e) {
            ; // don't do anything, node stays null so we know something went wrong.
        }
        if (node == null) {
            throw new IllegalArgumentException("no node could be chosen from the list");
        }
        setNodeA(node);
        return this;
    }
    
    /** removes the reference to node A */
    //@ ensures getNodeA() == null;
    private void removeNodeA() {
        nodeA = null;
    }

    /**
     * @param node the node that will be set as node B
     * @return     <code>this</code>
     */
    //@ ensures getNodeB() == node;
    //@ ensures \result == this;
    @NonNull public Relation setNodeB(Node node) {
        nodeB = node;
        return this;
    }
    
    /**
     * Sets node B to the next node in the <code>nodes</code> list. If the end of the list 
     * is reached, the first is selected.
     * 
     * @param nodes the nodes to choose from
     * @return      <code>this</code>
     */
    //@ requires !nodes.isEmpty();
    //@ ensures getNodeB() == nodes.getCircularNext(getNodeB());
    //@ ensures \result == this;
    @NonNull public Relation setNextNodeB(@NonNull NodeList nodes) {
        Node node = null;
        try {
            node = nodes.getCircularNext(getNodeB());
        } catch (NullPointerException e) {
            ; // don't do anything, node stays null so we know something went wrong.
        }
        if (node == null) {
            throw new IllegalArgumentException("no node could be chosen from the list");
        }
        setNodeB(node);
        return this;
    }
    
    /** removes the reference to node B */
    //@ ensures getNodeB() == null;
    private void removeNodeB() {
        nodeA = null;
    }

    /**
     * @param name the name to set
     * @return     <code>this</code>
     */
    //@ ensures getName() == name;
    //@ ensures \result == this;
    @NonNull public Relation setName(String name) {
        this.name = name;
        return this;
    }

    /**
     * @param rigid whether node A moves when node B moves
     * @return      <code>this</code>
     * @throws IllegalStateException if this relation is set to be rigid before a placement is set
     */
    //@ requires !getPlacement().equals(Placement.NONE);
    //@ ensures isRigid() == rigid;
    //@ ensures \result == this;
    @NonNull public Relation setRigid(boolean rigid) {
        if (rigid && getPlacement().equals(Placement.NONE)) {
            throw new IllegalStateException("the following relation needs a placement before "
                    + "it can be set to be rigid: " + this.toString());
        }
        this.rigid = rigid;
        return this;
    }

    /**
     * sets the placement of node A on node B. It assumes node B has a placement.
     * 
     * @param placement the <code>Placement</code> of node A relative to node B
     * @return          <code>this</code>
     */
    //@ ensures getPlacement() == placement;
    //@ ensures \result == this;
    @NonNull public Relation setPlacement(@NonNull Placement placement) {
        this.placement = placement;
        return this;
    }
    
    /**
     * Sets the placement to the next in the list of <code>placements</code>. If the end of 
     * the list is reached, the first one is chosen. If the current placement doesn't appear in 
     * <code>placements</code>, nothing happens.
     * 
     * @param placements the list of available placements
     * @return           <code>this</code>
     */
    //@ requires placements.length > 0;
    //@ ensures \result == this;
    @NonNull public Relation setNextPlacement(@NonNull Placement... placements) {
        final List<Placement> list = Arrays.asList(placements);
        if (list.contains(getPlacement())) {
            final int curI = list.indexOf(getPlacement()); 
            final Placement nextPlacement;
            if (curI == list.size() - 1) {
                nextPlacement = list.get(0); 
            } else {
                nextPlacement = list.get(curI + 1);
            }
            // Due to the @NonNull annotations we do this with the Placement.NONE. It won't 
            // ever be selected. Because <code>list</code> contains the current placement, 
            // <code>curI</code> will always be a value between 0 and list.size() - 1, meaning
            // <code>nextPlacement</code> won't be <code>null</code>.
            setPlacement(nextPlacement == null ? Placement.NONE : nextPlacement);
        }
        return this;
    }
    
    /**
     * Sets the temporary FX of node A. Node A should already have an FX set.
     * 
     * @param fx the FX of node A for the duration of this <code>Relation</code>
     * @throws  IllegalStateException if node A doesn't have an FX set
     */
    //@ ensures getTemporaryFxOfNodeA() == fx;
    //@ ensures \result == this;    
    @NonNull public Relation setTemporaryFxOfNodeA(@NonNull FxWrapper fx) {
        if (getNodeA() != null && getNodeA().getFxWrapper() == null) {
            throw new IllegalStateException("Node A has no FX set. Set this first.");
        }
        temporaryFxOfNodeA = fx;
        return this;
    }
    
    /**
     * Applies all properties of <code>originalRelation</code>. This works as a reverse clone().
     * 
     * @param originalRelation the original relation
     * @return                 <code>this</code>
     */
    //@ ensures \result == this;
    @NonNull public Relation fromRelation(@NonNull Relation originalRelation) {
        this.setName(originalRelation.getName());
        this.setNodeA(originalRelation.getNodeA());
        this.setNodeB(originalRelation.getNodeB());
        this.setPlacement(originalRelation.getPlacement());
        this.setRigid(originalRelation.isRigid());
        if (originalRelation.getTemporaryFxOfNodeA() != null) {
            this.setTemporaryFxOfNodeA(originalRelation.getTemporaryFxOfNodeA().clone());
        }
        return this;
    }

    @Override @NonNull 
    public Relation clone() {
        Relation relation = new Relation();
        relation.setName(this.getName());
        relation.setNodeA(this.getNodeA());
        relation.setNodeB(this.getNodeB());
        relation.setPlacement(this.getPlacement());
        relation.setRigid(this.isRigid());
        if (this.getTemporaryFxOfNodeA() != null) {
            relation.setTemporaryFxOfNodeA(this.getTemporaryFxOfNodeA().clone());
        }
        return relation;
    }
    


    // -- Commands ---------------------------------------------------------------------------

    /**
     * Adds this relation to node A and B's list of <code>Relation</code>s. Nodes A and B
     * have to be set.
     */
    //@ requires getNodeA() != null && getNodeB() != null;
    //@ ensures getNodeA().getRelations().contains(this);
    //@ ensures getNodeB().getRelations().contains(this);
    public void addToNodes() {
        getNodeA().getRelations().add(this);
        getNodeB().getRelations().add(this);
    }


    /** Removes this <code>Relation</code> from the connected nodes' <code>RelationList</code>s. */
    //@ ensures !getNodeA().getRelations().contains(this);
    //@ ensures !getNodeB().getRelations().contains(this);
    public void removeFromNodes() {
        if (getNodeA() != null) {
            getNodeA().getRelations().remove(this);
        }
        if (getNodeB() != null) {
            getNodeB().getRelations().remove(this);
        }
    }
    
    /**
     * Removes this relation from the current node A and passes it on to the next one in the
     * list. If <code>nodes</code> doesn't contain the current node A and/or has a size 
     * smaller than two, nothing happens.
     * 
     * @param nodes the list containing the current node A and the next
     * @return      <code>this</code>
     */
    //@ requires nodes.size() > 1 && nodes.contains(getNodeA());
    //@ ensures \result == this;
    @NonNull public Relation passToNextNodeA(@NonNull NodeList nodes) {
        if (nodes.size() > 1 && nodes.contains(getNodeA())) {
            final Node nextNode = nodes.getCircularNext(getNodeA());
            removeFromNodes();
            removeNodeA();
            // Node B is still set and node A isn't, so we add this relation to one of the two.
            nextNode.addRelation(this);
        }
        return this;
    }

    /**
     * Does exactly the same as {@link #passToNextNodeA(NodeList)}, but with node B.
     * 
     * @see #passToNextNodeA(NodeList)
     */
    //@ requires nodes.size() > 1 && nodes.contains(getNodeB());
    //@ ensures \result == this;
    @NonNull public Relation passToNextNodeB(@NonNull NodeList nodes) {
        if (nodes.size() > 1 && nodes.contains(getNodeB())) {
            Node nextNode = nodes.getCircularNext(getNodeB());
            removeFromNodes();
            removeNodeB();
            // Node A is still set and node B isn't, so we add this Relation to one of the two.
            nextNode.addRelation(this);
        }
        return this;
    }

}