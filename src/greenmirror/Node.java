package greenmirror;

import greenmirror.commands.AddRelationCommand;
import greenmirror.commands.ChangeNodeFxCommand;
import greenmirror.commands.RemoveRelationCommand;
import greenmirror.commands.SetNodeFxCommand;

import java.util.HashSet;
import java.util.Observable;
import java.util.Observer;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * The <tt>Node</tt> class. This models any visual node on the visualizer.
 * 
 * Extends java.util.Observable.
 * 
 * @author Karim El Assal
 */
public class Node extends Observable implements Observer {
    
    /**
     * A class to generalize the use of the <tt>Node</tt> identifiers. Possible values
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
         * Create a new <tt>Node.Identifier</tt> instance without directly setting the name 
         * and/or type.
         */
        public Identifier() {}
        
        /**
         * Create a new <tt>Node.Identifier</tt> instance.
         * @param identifier The identifying <tt>String</tt>.
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
         * @return The name component of this <tt>Node.Identifier</tt>.
         */
        /*@ pure */ public String getName() {
            return name;
        }
        
        /**
         * @return Whether this <tt>Node.Identifier</tt> has a name component.
         */
        //@ ensures \result == (getName() != null);
        /*@ pure */ public boolean hasName() {
            return getName() != null;
        }
        
        /**
         * @return The type component of this <tt>Node.Identifier</tt>.
         */
        /*@ pure */ public String getType() {
            return type;
        }
        
        /**
         * @return Whether this <tt>Node.Identifier</tt> has a type component.
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
        //@ ensures \result != null;
        /*@ pure */ public String toString() {
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
     * The id, type and name. These are allowed to be <tt>null</tt>.
     */
    private Integer id = null;
    private String type = null;
    private String name = null;
    
    /**
     * Labels the <tt>Node</tt> has.
     */
    //@ private invariant labels != null;
    private Set<String> labels = new HashSet<String>();

    /**
     * The wrapper that handles the appearance.
     */
    private FxWrapper fxWrapper;
    
    /**
     * All <tt>Relation</tt>s.
     */
    //@ private invariant relations != null;
    private RelationList relations = new RelationList();

    
    // -- Constructors -----------------------------------------------------------------------
    
    /**
     * Create a new <tt>Node</tt> instance with the given <tt>identifier</tt>.
     * @param identifier The name and/or type of this <tt>Node</tt>.
     */
    public Node(String identifier) {
        Identifier ir = new Identifier(identifier);
        setType(ir.getType());
        setName(ir.getName());
    }

    /**
     * Create a new <tt>Node</tt> instance without any identifier (yet).
     */
    public Node() {
        
    }
    

    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @return This <tt>Node</tt>'s id; <tt>null</tt> if it isn't set (yet).
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
     * @return This <tt>Node</tt>'s type; <tt>null</tt> if it isn't set (yet).
     */
    /*@ pure */ public String getType() {
        return type;
    }

    /**
     * @return This <tt>Node</tt>'s name; <tt>null</tt> if it isn't set (yet).
     */
    /*@ pure */ public String getName() {
        return name;
    }

    /**
     * @param label The label to check for.
     * @return <tt>true</tt> if this <tt>Node</tt> has <tt>label</tt>.
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
     * @return All current <tt>Relation</tt>s.
     */
    //@ ensures \result != null;
    /*@ pure */ public RelationList getRelations() {
        return relations;
    }

    /**
     * @param direction The direction of the requested <tt>Relation</tt>s: 
     *       1 for <tt>Relation</tt>s from <tt>this</tt> to any other <tt>Node</tt>; 
     *      -1 for <tt>Relation</tt>s from any other <tt>Node</tt> to <tt>this</tt>; 
     *       0 if the direction doesn't matter (just give all <tt>Relation</tt>s).
     * @return The <tt>Relation</tt>s with the given <tt>direction</tt>.
     */
    //@ requires direction == -1 || direction == 0 || direction == 1;
    //@ ensures \result.size() <= getRelations();
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
     * Returns a specific <tt>Relation</tt>.
     * @param direction    The direction of the <tt>Relation</tt>. 
     *                     {@link greenmirror.Node#getRelations(int)}
     * @param relationName The name of the <tt>Relation</tt>.
     * @return             The <tt>Relation</tt>; <tt>null</tt> if the specified 
     *                     <tt>Relation</tt> does not exist.
     */
    //@ requires direction == -1 || direction == 0 || direction == 1;
    //@ requires relationName != null;
    /*@ pure */ public Relation getRelation(int direction, String relationName) {
        RelationList list = getRelations(direction).withName(relationName);
        return list.size() > 0 ? list.get(0) : null;
    }
    
    /**
     * Check if this node has a specific <tt>Relation</tt>.
     * @param relation The <tt>Relation</tt> to check for.
     * @return         <tt>true</tt> if this node has <tt>relation</tt>.
     */
    //@ ensures \result == getRelations().contains(relation);
    /*@ pure */ public boolean hasRelation(Relation relation) {
        return getRelations().contains(relation);
    }
    
    /**
     * @return Whether this <tt>Node</tt> has a <tt>Relation</tt> that determines its 
     *         <tt>Placement</tt>.
     */
    /*@ pure */ public boolean hasPlacementRelation() {
        return getRelations().size() == 0 ? false : (getPlacementRelation() != null);
    }
    
    /**
     * @return The <tt>Relation</tt> which specifies the <tt>Placement</tt> of this <tt>Node</tt>;
     *         <tt>null</tt> if no placement <tt>Relation</tt> exists.
     */
    /*@ pure */ public Relation getPlacementRelation() {
        RelationList placementRelations = getRelations(1).withPlacement();
        return placementRelations.size() > 0 ? placementRelations.get(0) : null;
    }

    /**
     * Returns all <tt>Node</tt>s that have a <tt>Relation</tt> with <tt>this</tt> with a 
     * specific name.
     * @param direction    The direction of the <tt>Relation</tt>. 
     *                     {@link greenmirror.Node.getRelations(int)}
     * @param relationName The name of the relation. 
     * @return All related <tt>Node</tt>s.
     */
    //@ requires direction == -1 || direction == 0 || direction == 1;
    //@ requires relationName != null;
    //@ ensures \result != null;
    /*@ pure */ public NodeList getRelatedNodes(int direction, String relationName) {
        NodeList list = new NodeList();
        getRelations(direction).withName(relationName)
                               .forEach(relation -> list.add(relation.getOtherNode(this)));
        return list;
    }

    /**
     * Returns all <tt>Node</tt>s that have a <tt>Relation</tt> with <tt>this</tt>.
     * @param direction The direction of the <tt>Relation</tt>. 
     *                  {@link greenmirror.Node.getRelations(int)}
     * @return All related <tt>Node</tt>s.
     */
    //@ requires direction == -1 || direction == 0 || direction == 1;
    //@ ensures \result != null;
    /*@ pure */ public NodeList getRelatedNodes(int direction) {
        NodeList list = new NodeList();
        getRelations(direction).forEach(relation -> list.add(relation.getOtherNode(this)));
        return list;
    }

    /**
     * Returns all <tt>Node</tt>s that have a <tt>Relation</tt> with <tt>this</tt>.
     * @return All related <tt>Node</tt>s.
     */
    //@ ensures \result != null;
    /*@ pure */ public NodeList getRelatedNodes() {
        return getRelatedNodes(0);
    }

    /**
     * Returns the <tt>Node</tt> that has a specific <tt>Relation</tt> with <tt>this</tt>.
     * @param direction    The direction of the <tt>Relation</tt>. 
     *                     {@link greenmirror.Node.getRelations(int)}
     * @param relationName The name of the <tt>Relation</tt>.
     * @return             The related <tt>Node</tt>; <tt>null</tt> if the specified 
     *                     <tt>Relation</tt> does not exist.
     */
    //@ requires direction == -1 || direction == 0 || direction == 1;
    //@ requires relationName != null;
    /*@ pure */ public Node getRelatedNode(int direction, String relationName) {
        Relation rel = getRelation(direction, relationName);
        return rel == null ? null : rel.getOtherNode(this);
    }
    
    /**
     * This method should be used in the application. {@see #fx()}
     * @return The <tt>FxWrapper</tt>.
     */
    /*@ pure */ public FxWrapper getFxWrapper() {
        return fxWrapper;
    }

    /**
     * Checks if there exists a <tt>Relation</tt> with <tt>node</tt>.
     * @param node The other <tt>Node</tt>.
     * @return <tt>true</tt> if a <tt>Relation</tt> exists.
     */
    /*@ pure */ public boolean hasRelationWith(Node node) {
        return getRelations().stream()
                    .filter(relation -> relation.getOtherNode(this) == node)
                    .findFirst().isPresent();
                    //.collect(Collectors.toCollection(RelationList::new))
                    //.size() > 0;
    }

    /**
     * Checks if there exists a <tt>Relation</tt> with one of the <tt>Node</tt>s given in
     * <tt>nodes</tt>.
     * @param nodes The list to check for.
     * @return <tt>true</tt> if a <tt>Relation</tt> exists with one of the <tt>Node</tt>s.
     */
    //@ requires nodes != null;
    /*@ pure */ public boolean hasRelationWith(NodeList nodes) {
        return getRelatedNodes().stream()
                    .filter(relatedNode -> nodes.contains(relatedNode))
                    .findFirst().isPresent();
    }
    
    /**
     * @return A clear description of the <tt>Node</tt>.
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
     * @param id This <tt>Node</tt>'s id to set.
     */
    //@ ensures getId() == id;
    public void setId(Integer id) {
        this.id = id;
    }

    /**
     * @param type This <tt>Node</tt>'s type to set.
     * @return <tt>this</tt>.
     */
    //@ ensures getType() == type;
    //@ ensures \result == this;
    public Node setType(String type) {
        this.type = type;
        return this;
    }

    /**
     * @param name This <tt>Node</tt>'s name to set.
     * @return <tt>this</tt>
     */
    //@ ensures getName() == name;
    //@ ensures \result == this;
    public Node setName(String name) {
        this.name = name;
        return this;
    }

    /**
     * @param label Label to add to this <tt>Node</tt>'s labels.
     * @return <tt>this</tt>
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
     * @param label Label to remove from this <tt>Node</tt>'s labels.
     * @return <tt>this</tt>
     */
    //@ ensures !hasLabel(label);
    //@ ensures \result == this;
    public Node removeLabel(String label) {
        getLabels().remove(label);
        return this;
    }

    /**
     * Add a <tt>Relation</tt> to this <tt>Node</tt> and the <tt>Node</tt> on the other end.
     * The <tt>Relation</tt> should already have either node A or node B set to the other 
     * <tt>Node</tt>, so the current <tt>Node</tt> will be set to respectively node B or node A.
     * If this <tt>Node</tt> already has <tt>relation</tt>, nothing happens.
     * @param relation The <tt>Relation</tt> to add.
     * @return         <tt>this</tt>
     */
    //@ requires relation != null;
    /*@ requires (relation.getNodeA() == null && relation.getNodeB() != null) ||
     *@          (relation.getNodeB() == null && relation.getNodeA() != null); */
    //@ ensures \result == this;
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
     * Remove <tt>relation</tt> from this <tt>Node</tt>. Optional operation.
     * @param relation The <tt>Relation</tt> to remove.
     */
    //@ ensures !getRelations().contains(relation);
    public void removeRelation(Relation relation) {
        if (!getRelations().contains(relation)) {
            return;
        }
        relation.removeFromNodes();
    }
    
    /**
     * Set the new <tt>FxWrapper</tt>. This can only be done once. Observers get notified 
     * of the new <tt>FxWrapper</tt> and this <tt>Node</tt> starts observing the 
     * <tt>FxWrapper</tt>.
     * @param fxWrapper
     * @return                          <tt>this</tt>
     * @throws IllegalArgumentException If the <tt>FxWrapper</tt> was already set.
     */
    //@ requires fxWrapper != null;
    public Node set(FxWrapper fxWrapper) {
        if (getFxWrapper() != null) {
            throw new IllegalArgumentException("You have already set the FX type");
        }
        setFxWrapper(fxWrapper);
        getFxWrapper().addObserver(this);
        setChanged();
        notifyObservers(new SetNodeFxCommand(this));
        
        return this;
    }
    
    /**
     * @param fxWrapper The <tt>FxWrapper</tt> to set.
     */
    //@ ensures getFxWrapper() == fxWrapper;
    private void setFxWrapper(FxWrapper fxWrapper) {
        this.fxWrapper = fxWrapper;
    }

    
    // -- Commands ---------------------------------------------------------------------------
    
    
    public FxWrapper fx(String type) {
        if (getFxWrapper() != null) {
            // If the FxWrapper was already set.
            if (!getFxWrapper().getType().equals(
                Character.toUpperCase(type.charAt(0)) + type.substring(1))) {
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
     * @return The <tt>FxWrapper</tt>.
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
     * Clone this <tt>Node</tt>, except for the relations.
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