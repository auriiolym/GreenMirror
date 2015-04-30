package greenmirror;

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
     * The appearance of <tt>Node</tt> A for the duration of this <tt>Relation</tt>. Optional.
     */
    private VisualComponent temporaryAppearanceOfNodeA = null;

    
    // -- Constructors -----------------------------------------------------------------------

    /**
     * Create a <tt>Relation</tt> with a specific <tt>name</tt>.
     * @param name
     */
    //@ requires name != null;
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
     * @return The appearance of <tt>Node</tt> A for the duration of this <tt>Relation</tt>.
     */
    /*@ pure */ public VisualComponent getTemporaryAppearanceOfNodeA() {
        return temporaryAppearanceOfNodeA;
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
            + "|placement=" + getPlacement()
            + "|rigid=" + (isRigid() ? "true" : "false")
            + "|temporaryAppearanceofNodeA="
            + (getTemporaryAppearanceOfNodeA() == null ? "not_set" : "set");
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
     * @param node The <tt>Node</tt> that will be set as <tt>Node</tt> A.
     * @return <tt>this</tt>
     */
    //@ requires node != null;
    //@ ensures getNodeA() == node;
    //@ ensures \result == this;
    public Relation setNodeA(Node node) {
        nodeA = node;
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
     */
    //@ ensures isRigid() == rigid;
    //@ ensures \result == this;
    public Relation setRigid(boolean rigid) {
        this.rigid = rigid;
        return this;
    }

    /**
     * @param placement The <tt>Placement</tt> of <tt>Node</tt> A relative to <tt>Node</tt> B.
     */
    //@ requires placement != null;
    //@ ensures getPlacement() == placement;
    //@ ensures \result == this;
    public Relation setPlacement(Placement placement) {
        this.placement = placement;
        return this;
    }
    
    /**
     * @param vc The appearance of <tt>Node</tt> A for the duration of this <tt>Relation</tt>.
     */
    //@ requires placement != null;
    //@ ensures getPlacement() == placement;
    //@ ensures \result == this;    
    public Relation setTemporaryAppearanceOfNodeA(VisualComponent vc) {
        temporaryAppearanceOfNodeA = vc;
        return this;
    }

    public Relation clone() {
        // TODO - implement Relation.clone
        throw new UnsupportedOperationException();
    }
    


    // -- Commands ---------------------------------------------------------------------------



    /**
     * Remove this <tt>Relation</tt>. It removes itself from the connected <tt>Node</tt>'s
     * <tt>RelationList</tt>s and lets <tt>Node</tt> A know it is removed.
     */
    //@ ensures !getNodeA().getRelations().contains(this);
    //@ ensures !getNodeB().getRelations().contains(this);
    public void remove() {
        if (getNodeA() != null) {
            getNodeA().getRelations().remove(this);
        }
        if (getNodeB() != null) {
            getNodeB().getRelations().remove(this);
        }
        getNodeA().relationRemoved(this);
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
        if (nodes != null && nodes.size() > 1 && nodes.contains(getNodeA())) {
            Node nextNode = nodes.getCircularNext(getNodeA());
            remove();
            removeNodeA();
            // Node B is still set and node A isn't, so we add this Relation to one of the two.
            nextNode.addRelation(this);
        }
        return this;
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
            remove();
            removeNodeB();
            // Node A is still set and node B isn't, so we add this Relation to one of the two.
            nextNode.addRelation(this);
        }
        return this;
    }

}