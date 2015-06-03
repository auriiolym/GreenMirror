package greenmirror;

import java.util.Arrays;
import java.util.List;


/**
 * A class to model relations between <code>Node</code>s.
 * 
 * @author Karim El Assal
 */
public class Relation {


    // -- Instance variables -----------------------------------------------------------------
    
    /**
     * The <code>Node</code>s between this <code>Relation</code> exists. This <code>Relation</code> is
     * directed from <code>Node</code> A to <code>Node</code> B.
     */
    private Node nodeA = null;
    private Node nodeB = null;
    
    /**
     * The optional name of this <code>Relation</code>.
     */
    private String name = null;
    
    /**
     * Whether <code>Node</code> A moves when <code>Node</code> B moves.
     */
    private boolean rigid = false;

    /**
     * The <code>Placement</code> of <code>Node</code> A relative to <code>Node</code> B.
     */
    //@ private invariant placement != null;
    private Placement placement = Placement.NONE;
    
    /**
     * The FX of <code>Node</code> A for the duration of this <code>Relation</code>. Optional.
     */
    private FxWrapper temporaryFxOfNodeA = null;

    
    // -- Constructors -----------------------------------------------------------------------

    /**
     * Create a <code>Relation</code> with a specific <code>name</code>.
     * @param name
     */
    //@ ensures name.equals(getName());
    public Relation(String name) {
        setName(name);
    }

    /**
     * Create a <code>Relation</code> without specifying anything.
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
     * @return <code>Node</code> A.
     */
    /*@ pure */ public Node getNodeA() {
        return nodeA;
    }
    
    /**
     * @return <code>Node</code> B.
     */
    /*@ pure */ public Node getNodeB() {
        return nodeB;
    }
    
    /**
     * @param firstNode
     * @return The node connected to <code>firstNode</code> due to this <code>Relation</code>; 
     *         <code>null</code> if <code>firstNode</code> is not part of this <code>Relation</code>.
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
     * @return <code>true</code> if <code>Node</code> A moves when <code>Node</code> B moves.
     */
    /*@ pure */ public boolean isRigid() {
        return rigid;
    }
    
    /**
     * @return The <code>Placement</code> of <code>Node</code> A relative to <code>Node</code> B.
     */
    //@ ensures \result != null;
    /*@ pure */ public Placement getPlacement() {
        return placement;
    }
    
    /**
     * @return The FX of Node A for the duration of this <code>Relation</code>.
     */
    /*@ pure */ public FxWrapper getTemporaryFxOfNodeA() {
        return temporaryFxOfNodeA;
    }
    
    /**
     * @return A textual description of this <code>Relation</code>.
     */
    @Override
    /*@ pure */ public String toString() {
        return
              "Relation name=" + (getName() == null ? "" : getName())
            + "|fromNodeId=" + (getNodeA() == null ? "" : 
                        (getNodeA().getId() == null ? "" : Log.n(getNodeA())))
            + "|toNodeId=" + (getNodeB() == null ? "" : 
                        (getNodeB().getId() == null ? "" : Log.n(getNodeB())))
            + "|placement=" + getPlacement().toString()
            + "|rigid=" + (isRigid() ? "true" : "false")
            + "|temporaryFxOfNodeA="
            + (getTemporaryFxOfNodeA() == null ? "not_set" : "set");
    }
    

    // -- Setters ----------------------------------------------------------------------------

    /**
     * @param node The first <code>Node</code> will be set as <code>Node</code> A.
     * @return <code>this</code>
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
     * @param node The <code>Node</code> that will be set as <code>Node</code> A.
     * @return <code>this</code>
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
     * Set Node A to the next node in <code>nodes</code>. If the end of the list is reached, the 
     * first is selected.
     * @param nodes The nodes to choose from.
     * @return      <code>this</code>
     */
    //@ requires nodes != null;
    //@ ensures getNodeA() == nodes.getCircularNext(getNodeA());
    //@ ensures \result == this;
    public Relation setNextNodeA(NodeList nodes) {
        setNodeA(nodes.getCircularNext(getNodeA()));
        return this;
    }
    
    /**
     * Remove the reference to <code>Node</code> A.
     */
    //@ ensures getNodeA() == null;
    private void removeNodeA() {
        nodeA = null;
    }

    /**
     * @param node The first <code>Node</code> will be set as <code>Node</code> B.
     * @return <code>this</code>
     */
    //@ requires node != null && node.size() > 0;
    //@ ensures getNodeB() == node.getFirst();
    //@ ensures \result == this;
    public Relation setNodeB(NodeList node) {
        setNodeB(node.getFirst());
        return this;
    }

    /**
     * @param node The <code>Node</code> that will be set as <code>Node</code> B.
     * @return <code>this</code>
     */
    //@ requires node != null;
    //@ ensures getNodeB() == node;
    //@ ensures \result == this;
    public Relation setNodeB(Node node) {
        nodeB = node;
        return this;
    }
    
    /**
     * Set Node B to the next node in <code>nodes</code>. If the end of the list is reached, the 
     * first is selected.
     * @param nodes The nodes to choose from.
     * @return      <code>this</code>
     */
    //@ requires nodes != null;
    //@ ensures getNodeB() == nodes.getCircularNext(getNodeB());
    //@ ensures \result == this;
    public Relation setNextNodeB(NodeList nodes) {
        setNodeB(nodes.getCircularNext(getNodeB()));
        return this;
    }
    
    /**
     * Remove the reference to <code>Node</code> B.
     */
    //@ ensures getNodeB() == null;
    private void removeNodeB() {
        nodeA = null;
    }

    /**
     * @param name The name to set.
     * @return <code>this</code>
     */
    //@ ensures getName() == name;
    //@ ensures \result == this;
    public Relation setName(String name) {
        this.name = name;
        return this;
    }

    /**
     * @param rigid Whether <code>Node</code> A moves when <code>Node</code> B moves.
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
     * Set the placement of node A on node B. It assumes node A has a placement.
     * @param placement The <code>Placement</code> of <code>Node</code> A relative to <code>Node</code> B.
     */
    //@ requires placement != null;
    //@ ensures getPlacement() == placement;
    //@ ensures \result == this;
    public Relation setPlacement(Placement placement) {
        this.placement = placement;
        return this;
    }
    
    /**
     * Set the placement to the next in the list of <code>placements</code>. If the end of the list 
     * is reached, the next one is chosen. If the current placement doesn't appear in 
     * <code>placements</code>, nothing happens.
     * @param placements The list of available placements.
     * @return           <code>this</code>
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
     * @param fx The FX of <code>Node</code> A for the duration of this <code>Relation</code>.
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
     * Apply all properties of <code>originalRelation</code>. This works as a reverse clone().
     * @param originalRelation The original <code>Relation</code>.
     * @return                  <code>this</code>
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
     * Add this <code>Relation</code> to Node A and B's list of <code>Relation</code>s. Nodes A and B
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
     * Remove this <code>Relation</code>. It removes itself from the connected <code>Node</code>'s
     * <code>RelationList</code>s.
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
     * Pass the <code>Node</code> A connection of this <code>Relation</code> to the next <code>Node</code> 
     * given in <code>nodes</code>. If <code>nodes</code> doesn't contain the current <code>Node</code> A
     * and/or has a size smaller than two, nothing happens.
     * @param nodes The list containing the current <code>Node</code> A and the next.
     * @return <code>this</code>
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
     * Pass the <code>Node</code> B connection of this <code>Relation</code> to the next <code>Node</code> 
     * given in <code>nodes</code>. If <code>nodes</code> doesn't contain the current <code>Node</code> B
     * and/or has a size smaller than two, nothing happens.
     * @param nodes The list containing the current <code>Node</code> B and the next.
     * @return <code>this</code>
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