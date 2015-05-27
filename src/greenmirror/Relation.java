package greenmirror;

import java.util.Arrays;
import java.util.List;


/**
 * A class to model relations between <tt>Node</tt>s.
 * 
 * @author Karim El Assal
 */
public class Relation {


    // -- Instance variables -----------------------------------------------------------------
    
    /**
     * The <tt>Node</tt>s between this <tt>Relation</tt> exists. This <tt>Relation</tt> is
     * directed from <tt>Node</tt> A to <tt>Node</tt> B.
     */
    private Node nodeA = null;
    private Node nodeB = null;
    
    /**
     * The optional name of this <tt>Relation</tt>.
     */
    private String name = null;
    
    /**
     * Whether <tt>Node</tt> A moves when <tt>Node</tt> B moves.
     */
    private boolean rigid = false;

    /**
     * The <tt>Placement</tt> of <tt>Node</tt> A relative to <tt>Node</tt> B.
     */
    //@ private invariant placement != null;
    private Placement placement = Placement.NONE;
    
    /**
     * The FX of <tt>Node</tt> A for the duration of this <tt>Relation</tt>. Optional.
     */
    private FxWrapper temporaryFxOfNodeA = null;

    
    // -- Constructors -----------------------------------------------------------------------

    /**
     * Create a <tt>Relation</tt> with a specific <tt>name</tt>.
     * @param name
     */
    //@ ensures name.equals(getName());
    public Relation(String name) {
        setName(name);
    }

    /**
     * Create a <tt>Relation</tt> without specifying anything.
     */
    public Relation() {}
    
    
    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @return A unique id.
     */
    /*@ pure */ public String getId() {
        return (getNodeA() == null ? "" : getNodeA().getId()) + "|"
              + getName() + "|"
             + (getNodeB() == null ? "" : getNodeB().getId()) + "|"
             + getPlacement().toString() + "|"
             + String.valueOf(isRigid());
    }
    
    /**
     * @return <tt>Node</tt> A.
     */
    /*@ pure */ public Node getNodeA() {
        return nodeA;
    }
    
    /**
     * @return <tt>Node</tt> B.
     */
    /*@ pure */ public Node getNodeB() {
        return nodeB;
    }
    
    /**
     * @param firstNode
     * @return The node connected to <tt>firstNode</tt> due to this <tt>Relation</tt>; 
     *         <tt>null</tt> if <tt>firstNode</tt> is not part of this <tt>Relation</tt>.
     */
    //@ requires firstNode != null;
    /*@ pure */ public Node getOtherNode(Node firstNode) {
        if (firstNode.equals(getNodeA())) {
            return getNodeB();
        } else if (firstNode.equals(getNodeB())) {
            return getNodeA();
        } else {
            return null;
        }
    }

    /**
     * @return The name.
     */
    /*@ pure */ public String getName() {
        return name;
    }

    /**
     * @return <tt>true</tt> if <tt>Node</tt> A moves when <tt>Node</tt> B moves.
     */
    /*@ pure */ public boolean isRigid() {
        return rigid;
    }
    
    /**
     * @return The <tt>Placement</tt> of <tt>Node</tt> A relative to <tt>Node</tt> B.
     */
    //@ ensures \result != null;
    /*@ pure */ public Placement getPlacement() {
        return placement;
    }
    
    /**
     * @return The FX of Node A for the duration of this <tt>Relation</tt>.
     */
    /*@ pure */ public FxWrapper getTemporaryFxOfNodeA() {
        return temporaryFxOfNodeA;
    }
    
    /**
     * @return A textual description of this <tt>Relation</tt>.
     */
    @Override
    /*@ pure */ public String toString() {
        return
              "Relation name=" + (getName() == null ? "" : getName())
            + "|fromNodeId=" + (getNodeA() == null ? "" : 
                        (getNodeA().getId() == null ? "" : getNodeA().getId()))
            + "|toNodeId=" + (getNodeB() == null ? "" : 
                        (getNodeB().getId() == null ? "" : getNodeB().getId()))
            + "|placement=" + getPlacement().toString()
            + "|rigid=" + (isRigid() ? "true" : "false")
            + "|temporaryFxOfNodeA="
            + (getTemporaryFxOfNodeA() == null ? "not_set" : "set");
    }
    

    // -- Setters ----------------------------------------------------------------------------

    /**
     * @param node The first <tt>Node</tt> will be set as <tt>Node</tt> A.
     * @return <tt>this</tt>
     */
    //@ requires node != null && node.size() > 0;
    //@ ensures getNodeA() == node.getFirst();
    //@ ensures \result == this;
    public Relation setNodeA(NodeList node) {
        setNodeA(node.getFirst());
        return this;
    }

    /**
     * Set the starting node of this directional relation.
     * @param node The <tt>Node</tt> that will be set as <tt>Node</tt> A.
     * @return <tt>this</tt>
     * @throws IllegalStateException If node A is being set while a temporary FX is set, but 
     *                               Node A doesn't have its own FX.
     */
    //@ requires node != null;
    //@ ensures getNodeA() == node;
    //@ ensures \result == this;
    public Relation setNodeA(Node node) {
        if (getTemporaryFxOfNodeA() != null && node.getFxWrapper() == null) {
            throw new IllegalStateException("Node A should have its own FX if it's going "
                    + "to receive a temporary FX.");
        }
        nodeA = node;
        return this;
    }
    
    /**
     * Set Node A to the next node in <tt>nodes</tt>. If the end of the list is reached, the 
     * first is selected.
     * @param nodes The nodes to choose from.
     * @return      <tt>this</tt>
     */
    //@ requires nodes != null;
    //@ ensures getNodeA() == nodes.getCircularNext(getNodeA());
    //@ ensures \result == this;
    public Relation setNextNodeA(NodeList nodes) {
        setNodeA(nodes.getCircularNext(getNodeA()));
        return this;
    }
    
    /**
     * Remove the reference to <tt>Node</tt> A.
     */
    //@ ensures getNodeA() == null;
    private void removeNodeA() {
        nodeA = null;
    }

    /**
     * @param node The first <tt>Node</tt> will be set as <tt>Node</tt> B.
     * @return <tt>this</tt>
     */
    //@ requires node != null && node.size() > 0;
    //@ ensures getNodeB() == node.getFirst();
    //@ ensures \result == this;
    public Relation setNodeB(NodeList node) {
        setNodeB(node.getFirst());
        return this;
    }

    /**
     * @param node The <tt>Node</tt> that will be set as <tt>Node</tt> B.
     * @return <tt>this</tt>
     */
    //@ requires node != null;
    //@ ensures getNodeB() == node;
    //@ ensures \result == this;
    public Relation setNodeB(Node node) {
        nodeB = node;
        return this;
    }
    
    /**
     * Set Node B to the next node in <tt>nodes</tt>. If the end of the list is reached, the 
     * first is selected.
     * @param nodes The nodes to choose from.
     * @return      <tt>this</tt>
     */
    //@ requires nodes != null;
    //@ ensures getNodeB() == nodes.getCircularNext(getNodeB());
    //@ ensures \result == this;
    public Relation setNextNodeB(NodeList nodes) {
        setNodeB(nodes.getCircularNext(getNodeB()));
        return this;
    }
    
    /**
     * Remove the reference to <tt>Node</tt> B.
     */
    //@ ensures getNodeB() == null;
    private void removeNodeB() {
        nodeA = null;
    }

    /**
     * @param name The name to set.
     * @return <tt>this</tt>
     */
    //@ ensures getName() == name;
    //@ ensures \result == this;
    public Relation setName(String name) {
        this.name = name;
        return this;
    }

    /**
     * @param rigid Whether <tt>Node</tt> A moves when <tt>Node</tt> B moves.
     * @throws IllegalStateException If this Relation is set to be rigid before a placement is set.
     */
    //@ requires !getPlacement().equals(Placement.NONE);
    //@ ensures isRigid() == rigid;
    //@ ensures \result == this;
    public Relation setRigid(boolean rigid) {
        if (rigid && getPlacement().equals(Placement.NONE)) {
            throw new IllegalStateException("The following relation needs a placement before "
                    + "it can be set to be rigid: " + this.toString());
        }
        this.rigid = rigid;
        return this;
    }

    /**
     * @param placement The <tt>Placement</tt> of <tt>Node</tt> A relative to <tt>Node</tt> B.
     * @throws IllegalStateException If the placement is set before node B has a location on the 
     *                               screen.
     */
    //@ requires placement != null;
    //@ ensures getPlacement() == placement;
    //@ ensures \result == this;
    public Relation setPlacement(Placement placement) {
        if (getNodeB() == null || getNodeB().getFxWrapper() == null
            || (!getNodeB().getFxWrapper().isPositionSet() 
                    && !getNodeB().hasPlacementRelation())) {
            throw new IllegalStateException("The following relation needs an ending node with a "
                    + "location before it can place the starting node:" + this.toString());
        }
        this.placement = placement;
        return this;
    }
    
    /**
     * Set the placement to the next in the list of <tt>placements</tt>. If the end of the list 
     * is reached, the next one is chosen. If the current placement doesn't appear in 
     * <tt>placements</tt>, nothing happens.
     * @param placements The list of available placements.
     * @return           <tt>this</tt>
     */
    //@ requires placements.length > 0;
    //@ ensures \result == this;
    public Relation setNextPlacement(Placement... placements) {
        List<Placement> list = Arrays.asList(placements);
        if (list.contains(getPlacement())) {
            int curI = list.indexOf(getPlacement());
            if (curI == list.size() - 1) {
                setPlacement(list.get(0));
            } else {
                setPlacement(list.get(curI + 1));
            }
        }
        return this;
    }
    
    /**
     * Set the temporary FX of Node A. Node A should already have an FX set.
     * @param fx The FX of <tt>Node</tt> A for the duration of this <tt>Relation</tt>.
     * @throws IllegalStateException If Node A doesn't have an FX set.
     */
    //@ requires fx != null;
    //@ ensures getTemporaryFxOfNodeA() == fx;
    //@ ensures \result == this;    
    public Relation setTemporaryFxOfNodeA(FxWrapper fx) {
        if (getNodeA() != null && getNodeA().getFxWrapper() == null) {
            throw new IllegalStateException("Node A has no FX set. Set this first.");
        }
        temporaryFxOfNodeA = fx;
        return this;
    }
    
    /**
     * Apply all properties of <tt>originalRelation</tt>. This works as a reverse clone().
     * @param originalRelation The original <tt>Relation</tt>.
     * @return                  <tt>this</tt>
     */
    //@ requires originalRelation != null;
    //@ ensures \result == this;
    public Relation fromRelation(Relation originalRelation) {
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
     * Add this <tt>Relation</tt> to Node A and B's list of <tt>Relation</tt>s. Nodes A and B
     * have to be set.
     */
    //@ requires getNodeA() != null && getNodeB() != null;
    //@ ensures getNodeA().getRelations().contains(this);
    //@ ensures getNodeB().getRelations().contains(this);
    public void addToNodes() {
        getNodeA().getRelations().add(this);
        getNodeB().getRelations().add(this);
    }


    /**
     * Remove this <tt>Relation</tt>. It removes itself from the connected <tt>Node</tt>'s
     * <tt>RelationList</tt>s.
     */
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
     * Pass the <tt>Node</tt> A connection of this <tt>Relation</tt> to the next <tt>Node</tt> 
     * given in <tt>nodes</tt>. If <tt>nodes</tt> doesn't contain the current <tt>Node</tt> A
     * and/or has a size smaller than two, nothing happens.
     * @param nodes The list containing the current <tt>Node</tt> A and the next.
     * @return <tt>this</tt>
     */
    //@ requires nodes != null && nodes.size() > 1 && nodes.contains(getNodeA());
    //@ ensures \result == this;
    public Relation passToNextNodeA(NodeList nodes) {
        throw new UnsupportedOperationException();
        //TODO: make a command in the groovy base script for this.
        /*
        if (nodes != null && nodes.size() > 1 && nodes.contains(getNodeA())) {
            Node nextNode = nodes.getCircularNext(getNodeA());
            remove();
            removeNodeA();
            // Node B is still set and node A isn't, so we add this Relation to one of the two.
            nextNode.addRelation(this);
        }
        return this;*/
    }

    /**
     * Pass the <tt>Node</tt> B connection of this <tt>Relation</tt> to the next <tt>Node</tt> 
     * given in <tt>nodes</tt>. If <tt>nodes</tt> doesn't contain the current <tt>Node</tt> B
     * and/or has a size smaller than two, nothing happens.
     * @param nodes The list containing the current <tt>Node</tt> B and the next.
     * @return <tt>this</tt>
     */
    //@ requires nodes != null && nodes.size() > 1 && nodes.contains(getNodeB());
    //@ ensures \result == this;
    public Relation passToNextNodeB(NodeList nodes) {
        if (nodes != null && nodes.size() > 1 && nodes.contains(getNodeB())) {
            Node nextNode = nodes.getCircularNext(getNodeB());
            removeFromNodes();
            removeNodeB();
            // Node A is still set and node B isn't, so we add this Relation to one of the two.
            nextNode.addRelation(this);
        }
        return this;
    }

}