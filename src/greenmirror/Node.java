package greenmirror;

import greenmirror.commands.AddRelationCommand;
import greenmirror.commands.ChangeNodeFxCommand;
import greenmirror.commands.SetNodeFxCommand;

import java.util.HashSet;
import java.util.Observable;
import java.util.Observer;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * The <code>Node</code> class. This models any visual node on the visualizer.
 * 
 * Extends java.util.Observable.
 * 
 * @author Karim El Assal
 */
public class Node extends Observable implements Observer {
    
    /**
     * A class to generalize the use of the <code>Node</code> identifiers. Possible values
     * are (without quotes): "type:name", "type:", "name", "".
     * 
     * @author Karim El Assal
     */
    public static class Identifier {
        
        /**
         * The name and type.
         */
        private String name = null;
        private String type = null;
        
        /**
         * Create a new <code>Node.Identifier</code> instance without directly setting the name 
         * and/or type.
         */
        public Identifier() {}
        
        /**
         * Create a new <code>Node.Identifier</code> instance.
         * @param identifier The identifying <code>String</code>.
         */
        public Identifier(String identifier) {
            if (identifier == null || identifier.length() == 0) {
                type = null;
                name = null;
                
            } else if (!identifier.contains(":")) {
                type = null;
                name = identifier;
            
            } else {
                String[] idParts = identifier.split(":", 2);
                type = idParts[0].length() == 0 ? null : idParts[0];
                name = idParts[1].length() == 0 ? null : idParts[1]; 
            }
        }
        
        /**
         * @return The name component of this <code>Node.Identifier</code>.
         */
        /*@ pure */ public String getName() {
            return name;
        }
        
        /**
         * @return Whether this <code>Node.Identifier</code> has a name component.
         */
        //@ ensures \result == (getName() != null);
        /*@ pure */ public boolean hasName() {
            return getName() != null;
        }
        
        /**
         * @return The type component of this <code>Node.Identifier</code>.
         */
        /*@ pure */ public String getType() {
            return type;
        }
        
        /**
         * @return Whether this <code>Node.Identifier</code> has a type component.
         */
        //@ ensures \result == (getType() != null);
        /*@ pure */ public boolean hasType() {
            return getType() != null;
        }
        
        /**
         * @return The string representation in the format "type:name", "type:" (no name 
         * set), "name" (no type set) or "" (no type and no name set).
         */
        @Override
        /*@ pure non_null */ public String toString() {
            return (hasType() ? getType() + ":" : "")
                 + (hasName() ? getName() : "");
        }
        
        /**
         * @param name The name to set.
         */
        //@ ensures getName() == name || getName().equals(name);
        public void setName(String name) {
            this.name = name;
        }
        
        /**
         * @param type The type to set.
         */
        //@ ensures getType() == type || getType().equals(type);
        public void setType(String type) {
            this.type = type;
        }
    }
    
    /**
     * The id, type and name. These are allowed to be <code>null</code>.
     */
    private Integer id = null;
    private String type = null;
    private String name = null;
    
    /**
     * Labels the <code>Node</code> has.
     */
    //@ private invariant labels != null;
    private Set<String> labels = new HashSet<String>();

    /**
     * The wrapper that handles the appearance.
     */
    private FxWrapper fxWrapper;
    
    /**
     * All <code>Relation</code>s.
     */
    //@ private invariant relations != null;
    private RelationList relations = new RelationList();

    
    // -- Constructors -----------------------------------------------------------------------
    
    /**
     * Create a new <code>Node</code> instance with the given <code>identifier</code>.
     * @param identifier The name and/or type of this <code>Node</code>.
     */
    public Node(String identifier) {
        Identifier ir = new Identifier(identifier);
        setType(ir.getType());
        setName(ir.getName());
    }

    /**
     * Create a new <code>Node</code> instance without any identifier (yet).
     */
    public Node() {
        
    }
    

    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @return This <code>Node</code>'s id; <code>null</code> if it isn't set (yet).
     */
    /*@ pure */ public Integer getId() {
        return id;
    }
    
    /**
     * @return The identifier string.
     */
    /*@ pure */ public String getIdentifier() {
        Identifier identifier = new Identifier();
        identifier.setType(getType());
        identifier.setName(getName());
        return identifier.toString();
    }
    
    /**
     * @return This <code>Node</code>'s type; <code>null</code> if it isn't set (yet).
     */
    /*@ pure */ public String getType() {
        return type;
    }

    /**
     * @return This <code>Node</code>'s name; <code>null</code> if it isn't set (yet).
     */
    /*@ pure */ public String getName() {
        return name;
    }

    /**
     * @param label The label to check for.
     * @return <code>true</code> if this <code>Node</code> has <code>label</code>.
     */
    /*@ pure */ public boolean hasLabel(String label) {
        return getLabels().contains(label);
    }
    
    /**
     * @return The labels.
     */
    //@ ensures \result != null;
    /*@ pure */ private Set<String> getLabels() {
        return labels;
    }
    
    /**
     * @return All current <code>Relation</code>s.
     */
    //@ ensures \result != null;
    /*@ pure */ public RelationList getRelations() {
        return relations;
    }

    /**
     * @param direction The direction of the requested <code>Relation</code>s: 
     *       1 for <code>Relation</code>s from <code>this</code> to any other <code>Node</code>; 
     *      -1 for <code>Relation</code>s from any other <code>Node</code> to <code>this</code>; 
     *       0 if the direction doesn't matter (just give all <code>Relation</code>s).
     * @return The <code>Relation</code>s with the given <code>direction</code>.
     */
    //@ requires direction == -1 || direction == 0 || direction == 1;
    //@ ensures \result.size() <= getRelations().size();
    /*@ pure */ public RelationList getRelations(int direction) {
        Stream<Relation> res;
        switch (direction) {
        case -1:
            res = getRelations().stream()
                        .filter(relation -> relation.getNodeB() == this);
            break;
        case 0:
            res = getRelations().stream();
            break;
        case 1:
            res = getRelations().stream()
                        .filter(relation -> relation.getNodeA() == this);
            break;
        default:
            throw new IllegalArgumentException();
        }
        return res.collect(Collectors.toCollection(RelationList::new));
    }

    /**
     * Returns a specific <code>Relation</code>.
     * @param direction    The direction of the <code>Relation</code>. 
     *                     {@link greenmirror.Node#getRelations(int)}
     * @param relationName The name of the <code>Relation</code>.
     * @return             The <code>Relation</code>; <code>null</code> if the specified 
     *                     <code>Relation</code> does not exist.
     */
    //@ requires direction == -1 || direction == 0 || direction == 1;
    //@ requires relationName != null;
    /*@ pure */ public Relation getRelation(int direction, String relationName) {
        RelationList list = getRelations(direction).withName(relationName);
        return list.size() > 0 ? list.get(0) : null;
    }
    
    /**
     * Check if this node has a specific <code>Relation</code>.
     * @param relation The <code>Relation</code> to check for.
     * @return         <code>true</code> if this node has <code>relation</code>.
     */
    //@ ensures \result == getRelations().contains(relation);
    /*@ pure */ public boolean hasRelation(Relation relation) {
        return getRelations().contains(relation);
    }
    
    /**
     * @return Whether this <code>Node</code> has a <code>Relation</code> that determines its 
     *         <code>Placement</code>.
     */
    /*@ pure */ public boolean hasPlacementRelation() {
        return getRelations().size() == 0 ? false : (getPlacementRelation() != null);
    }
    
    /**
     * @return The <code>Relation</code> which specifies the <code>Placement</code> of this <code>Node</code>;
     *         <code>null</code> if no placement <code>Relation</code> exists.
     */
    /*@ pure */ public Relation getPlacementRelation() {
        RelationList placementRelations = getRelations(1).withPlacement();
        return placementRelations.size() > 0 ? placementRelations.get(0) : null;
    }

    /**
     * Returns all <code>Node</code>s that have a <code>Relation</code> with <code>this</code> with a 
     * specific name.
     * @param direction    The direction of the <code>Relation</code>. 
     *                     {@link greenmirror.Node.getRelations(int)}
     * @param relationName The name of the relation. 
     * @return All related <code>Node</code>s.
     */
    //@ requires direction == -1 || direction == 0 || direction == 1;
    //@ requires relationName != null;
    //@ ensures \result != null;
    /*@ pure */ public NodeList getRelatedNodes(int direction, String relationName) {
        NodeList list = new NodeList();
        for (Relation relation : getRelations(direction).withName(relationName)) {
            list.add(relation.getOtherNode(this));
        }
        return list;
    }

    /**
     * Returns all <code>Node</code>s that have a <code>Relation</code> with <code>this</code>.
     * @param direction The direction of the <code>Relation</code>. 
     *                  {@link greenmirror.Node.getRelations(int)}
     * @return All related <code>Node</code>s.
     */
    //@ requires direction == -1 || direction == 0 || direction == 1;
    //@ ensures \result != null;
    /*@ pure */ public NodeList getRelatedNodes(int direction) {
        NodeList list = new NodeList();
        for (Relation relation : getRelations(direction)) {
            list.add(relation.getOtherNode(this));
        }
        return list;
    }

    /**
     * Returns all <code>Node</code>s that have a <code>Relation</code> with <code>this</code>.
     * @return All related <code>Node</code>s.
     */
    //@ ensures \result != null;
    /*@ pure */ public NodeList getRelatedNodes() {
        return getRelatedNodes(0);
    }

    /**
     * Returns the <code>Node</code> that has a specific <code>Relation</code> with <code>this</code>.
     * @param direction    The direction of the <code>Relation</code>. 
     *                     {@link greenmirror.Node.getRelations(int)}
     * @param relationName The name of the <code>Relation</code>.
     * @return             The related <code>Node</code>; <code>null</code> if the specified 
     *                     <code>Relation</code> does not exist.
     */
    //@ requires direction == -1 || direction == 0 || direction == 1;
    //@ requires relationName != null;
    /*@ pure */ public Node getRelatedNode(int direction, String relationName) {
        Relation rel = getRelation(direction, relationName);
        return rel == null ? null : rel.getOtherNode(this);
    }
    
    /**
     * This method should be used in the application. {@see #fx()}
     * @return The <code>FxWrapper</code>.
     */
    /*@ pure */ public FxWrapper getFxWrapper() {
        return fxWrapper;
    }

    /**
     * Checks if there exists a <code>Relation</code> with <code>node</code>.
     * @param node The other <code>Node</code>.
     * @return <code>true</code> if a <code>Relation</code> exists.
     */
    /*@ pure */ public boolean hasRelationWith(Node node) {
        return getRelations().stream()
                    .filter(relation -> relation.getOtherNode(this) == node)
                    .findFirst().isPresent();
                    //.collect(Collectors.toCollection(RelationList::new))
                    //.size() > 0;
    }

    /**
     * Checks if there exists a <code>Relation</code> with one of the <code>Node</code>s given in
     * <code>nodes</code>.
     * @param nodes The list to check for.
     * @return <code>true</code> if a <code>Relation</code> exists with one of the <code>Node</code>s.
     */
    //@ requires nodes != null;
    /*@ pure */ public boolean hasRelationWith(NodeList nodes) {
        return getRelatedNodes().stream()
                    .filter(relatedNode -> nodes.contains(relatedNode))
                    .findFirst().isPresent();
    }
    
    /**
     * @return A clear description of the <code>Node</code>.
     */
    @Override
    /*@ pure */ public String toString() {
        return 
              "node id=" + (getId() == null ? "" : getId().toString())
            + " | type=" + (getType() == null ? "" : getType().toString())
            + " | name=" + (getName() == null ? "" : getName().toString())
            + " | labels=" + getLabels().toString()
            + " | relations=" + getRelations().toString()
            + " | FX=" + String.valueOf(getFxWrapper());
    }

    

    // -- Setters ----------------------------------------------------------------------------
    
    /**
     * @param id This <code>Node</code>'s id to set.
     */
    //@ ensures getId() == id;
    public void setId(Integer id) {
        this.id = id;
    }

    /**
     * @param type This <code>Node</code>'s type to set.
     * @return <code>this</code>.
     */
    //@ ensures getType() == type;
    //@ ensures \result == this;
    public Node setType(String type) {
        this.type = type;
        return this;
    }

    /**
     * @param name This <code>Node</code>'s name to set.
     * @return <code>this</code>
     */
    //@ ensures getName() == name;
    //@ ensures \result == this;
    public Node setName(String name) {
        this.name = name;
        return this;
    }

    /**
     * @param label Label to add to this <code>Node</code>'s labels.
     * @return <code>this</code>
     */
    //@ ensures hasLabel(label);
    //@ ensures \result == this;
    public Node addLabel(String label) {
        if (label != null) {
            getLabels().add(label);
        }
        return this;
    }
    
    /**
     * Remove a label. Optional operation.
     * @param label Label to remove from this <code>Node</code>'s labels.
     * @return <code>this</code>
     */
    //@ ensures !hasLabel(label);
    //@ ensures \result == this;
    public Node removeLabel(String label) {
        getLabels().remove(label);
        return this;
    }

    /**
     * Add a <code>Relation</code> to this <code>Node</code> and the <code>Node</code> on the other end.
     * The <code>Relation</code> should already have either node A or node B set to the other 
     * <code>Node</code>, so the current <code>Node</code> will be set to respectively node B or node A.
     * If this <code>Node</code> already has <code>relation</code>, nothing happens.
     * @param relation The <code>Relation</code> to add.
     * @return         <code>this</code>
     */
    /*@ requires relation != null;
      @ requires (relation.getNodeA() == null && relation.getNodeB() != null) ||
      @          (relation.getNodeB() == null && relation.getNodeA() != null); 
      @ ensures \result == this; */
    public Node addRelation(Relation relation) {
        if (!getRelations().contains(relation)) {
            if ((relation.getNodeA() == null && relation.getNodeB() == null)
             || (relation.getNodeA() != null && relation.getNodeB() != null)) {
                throw new IllegalArgumentException("Only and exactly one of the two ends of "
                        + "the relation should be null.");
            }
            if (relation.getNodeA() == null) {
                relation.setNodeA(this);
            } else if (relation.getNodeB() == null) {
                relation.setNodeB(this);
            }
            getRelations().add(relation);
            relation.getOtherNode(this).getRelations().add(relation);
            
            //TODO: check if it's a Placement Relation. If so, remove the previous relation.
            setChanged();
            notifyObservers(new AddRelationCommand(relation));
        }
        return this;
    }

    /**
     * Remove <code>relation</code> from this <code>Node</code>. Optional operation.
     * @param relation The <code>Relation</code> to remove.
     */
    //@ ensures !getRelations().contains(relation);
    public void removeRelation(Relation relation) {
        if (!getRelations().contains(relation)) {
            return;
        }
        relation.removeFromNodes();
    }
    
    /**
     * Set the new <code>FxWrapper</code>. This can only be done once. Observers get notified 
     * of the new <code>FxWrapper</code> and this <code>Node</code> starts observing the 
     * <code>FxWrapper</code>.
     * @param fxWrapper
     * @return                          <code>this</code>
     * @throws IllegalArgumentException If the <code>FxWrapper</code> was already set.
     */
    //@ requires fxWrapper != null;
    public Node set(FxWrapper fxWrapper) {
        
        if (getFxWrapper() != null
                && !getFxWrapper().getType().equals(
                        GreenMirrorUtils.capitalizeFirstChar(fxWrapper.getType()))) {
            throw new IllegalArgumentException("You have already set the FX type");
        }
        setFxWrapper(fxWrapper);
        getFxWrapper().addObserver(this);
        setChanged();
        notifyObservers(new SetNodeFxCommand(this));
        
        return this;
    }
    
    /**
     * @param fxWrapper The <code>FxWrapper</code> to set.
     */
    //@ ensures getFxWrapper() == fxWrapper;
    private void setFxWrapper(FxWrapper fxWrapper) {
        this.fxWrapper = fxWrapper;
    }

    
    // -- Commands ---------------------------------------------------------------------------
    
    
    public FxWrapper fx(String type) {
        if (getFxWrapper() != null) {
            // If the FxWrapper was already set.
            if (!getFxWrapper().getType().equals(GreenMirrorUtils.capitalizeFirstChar(type))) {
                // Throw exception if it's a different type.
                throw new IllegalArgumentException("You have already set the FX type.");
            } else {
                // Return if it's the same as the requested type.
                return fx();
            }
        }
        // If it wasn't created yet, try to create it, add observers and notify our own observers.
        setFxWrapper(FxWrapper.getNewInstance(type));
        getFxWrapper().addObserver(this);
        
        setChanged();
        notifyObservers(new SetNodeFxCommand(this));
           
        return fx();
    }
    
    /**
     * This method should be used in a Groovy user script. {@see #getFxWrapper()}
     * @return The <code>FxWrapper</code>.
     */
    /*@ pure */ public FxWrapper fx() {
        if (getFxWrapper() == null) {
            throw new IllegalStateException("No FX element has been set.");
        }
        return getFxWrapper();
    }

    /* (non-Javadoc)
     * @see java.util.Observer#update(java.util.Observable, java.lang.Object)
     */
    @Override
    public void update(Observable observable, Object arg1) {
        // The appearance was changed. Notify the controller that the server should know
        // that the (original) FX has changed.
        if (observable instanceof FxWrapper) {
            setChanged();
            notifyObservers(new ChangeNodeFxCommand(this));
            return;
        }        
    }
    
    /**
     * Clone this <code>Node</code>, except for the relations.
     */
    @Override
    public Node clone() {
        Node node = new Node();
        node.setType(this.getType());
        node.setName(this.getName());
        for (String label : this.getLabels()) {
            node.addLabel(label);
        }
        if (this.getFxWrapper() != null) {
            node.set(this.getFxWrapper().clone());
        }
        return node;
    }
}