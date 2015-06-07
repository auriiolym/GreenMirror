package greenmirror;

import greenmirror.commands.AddRelationCommand;
import greenmirror.commands.ChangeNodeFxCommand;
import greenmirror.commands.SetNodeFxCommand;
import greenmirror.commands.SwitchPlacementRelationCommand;
import greenmirror.placements.CustomPlacement;
import greenmirror.placements.RandomPlacement;
import org.eclipse.jdt.annotation.NonNull;

import java.util.Observable;
import java.util.Observer;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * The class that models any node. 
 * 
 * When it is added to GreenMirror, it will be watched using the observer pattern. In addition,
 * it observes its {@link FxWrapper} (when it's got one) for changes in its properties.
 * 
 * @author Karim El Assal
 */
public class Node extends Observable implements Observer, Cloneable {
    
    // -- Inner classes ----------------------------------------------------------------------
    
    /**
     * A class to generalize the use of the <code>Node</code> identifiers. Possible values
     * are: "type:name", "type:", "name", "", null.
     * 
     * @author Karim El Assal
     */
    public static class Identifier {
        
        /** the name and type */
        private String name = null;
        private String type = null;
        
        /**
         * Create a new <code>Node.Identifier</code> instance without directly setting the name 
         * and/or type.
         */
        public Identifier() {}
        
        /**
         * Create a new <code>Node.Identifier</code> instance.
         * 
         * @param identifier the identifying string
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
        
        /** @return the name component of this <code>Node.Identifier</code> */
        /*@ pure */ public String getName() {
            return name;
        }
        
        /** @return whether this <code>Node.Identifier</code> has a name component */
        //@ ensures \result == (getName() != null);
        /*@ pure */ public boolean hasName() {
            return getName() != null;
        }
        
        /** @return the type component of this <code>Node.Identifier</code> */
        /*@ pure */ public String getType() {
            return type;
        }
        
        /** @return whether this <code>Node.Identifier</code> has a type component */
        //@ ensures \result == (getType() != null);
        /*@ pure */ public boolean hasType() {
            return getType() != null;
        }
        
        /** 
         * @return the string representation in the format "type:name", "type:" (no name 
         *         set), "name" (no type set) or "" (no type and no name set).
         */
        @Override @NonNull
        /*@ pure */ public String toString() {
            return (hasType() ? getType() + ":" : "")
                 + (hasName() ? getName() : "");
        }
        
        /** @param name the name to set */
        //@ ensures (getName() == name) || (getName().equals(name));
        public void setName(String name) {
            this.name = name;
        }
        
        /** @param type the type to set */
        //@ ensures (getType() == type) || (getType().equals(type));
        public void setType(String type) {
            this.type = type;
        }
    }
    
    /** the id, type and name */
    private Integer id = null;
    private String type = null;
    private String name = null;
    
    /** labels this <code>Node</code> has */
    @NonNull private Set<String> labels = new TreeSet<String>();

    /** the wrapper that handles the appearance */
    private FxWrapper fxWrapper;
    
    /** all <code>Relation</code>s */
    @NonNull private RelationList relations = new RelationList();

    
    // -- Constructors -----------------------------------------------------------------------
    
    /**
     * Create a new <code>Node</code> instance with the given <code>identifier</code>.
     * 
     * @param identifier the name and/or type of this <code>Node</code>
     */
    public Node(String identifier) {
        final Identifier ir = new Identifier(identifier);
        setType(ir.getType());
        setName(ir.getName());
    }

    /**
     * Create a new <code>Node</code> instance without any type and name information (yet).
     */
    public Node() {}
    

    // -- Queries ----------------------------------------------------------------------------
    
    /** @return this <code>Node</code>'s id; <code>null</code> if it isn't set (yet) */
    /*@ pure */ public Integer getId() {
        return id;
    }
    
    /** @return the identifier string */
    /*@ pure */ @NonNull public String getIdentifier() {
        final Identifier identifier = new Identifier();
        identifier.setType(getType());
        identifier.setName(getName());
        return identifier.toString();
    }
    
    /** @return this <code>Node</code>'s type; <code>null</code> if it isn't set (yet) */
    /*@ pure */ public String getType() {
        return type;
    }

    /** @return this <code>Node</code>'s name; <code>null</code> if it isn't set (yet) */
    /*@ pure */ public String getName() {
        return name;
    }

    /**
     * @param label the label to check for
     * @return <code>true</code> if this <code>Node</code> has <code>label</code>
     */
    /*@ pure */ public boolean hasLabel(String label) {
        return getLabels().contains(label);
    }
    
    /**
     * @return the labels
     */
    /*@ pure */ @NonNull private Set<String> getLabels() {
        return labels;
    }
    
    /**
     * Returns the set {@link FxWrapper}. This method should be used in the application.
     * 
     * @return the <code>FxWrapper</code>; <code>null</code> if it isn't set (yet)
     * @see    FxWrapper
     * @see    #fx()
     */
    /*@ pure */ public FxWrapper getFxWrapper() {
        return fxWrapper;
    }
    
    /**
     * @return all current {@link Relation}s
     */
    /*@ pure */ @NonNull public RelationList getRelations() {
        return relations;
    }

    /**
     * @param direction the direction of the requested {@link Relation}s: 
     *       1 for <code>Relation</code>s from <code>this</code> to any other <code>Node</code>; 
     *      -1 for <code>Relation</code>s from any other <code>Node</code> to <code>this</code>; 
     *       0 if the direction doesn't matter (just give all <code>Relation</code>s).
     * @return the <code>Relation</code>s with the given <code>direction</code>
     * @throws IllegalArgumentException if <code>direction</code> is invalid
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
            throw new IllegalArgumentException("invalid direction");
        }
        return res.collect(Collectors.toCollection(RelationList::new));
    }

    /**
     * Returns a specific {@link Relation}.
     * 
     * @param direction    see {@link #getRelations(int)}
     * @param relationName the name of the <code>Relation</code>
     * @return             the <code>Relation</code>; <code>null</code> if the specified 
     *                     <code>Relation</code> does not exist
     * @throws IllegalArgumentException if <code>direction</code> is invalid
     */
    //@ requires direction == -1 || direction == 0 || direction == 1;
    /*@ pure */ public Relation getRelation(int direction, @NonNull String relationName) {
        final RelationList list = getRelations(direction).withName(relationName);
        return list.size() > 0 ? list.get(0) : null;
    }
    
    /**
     * Check if this node has a specific {@link Relation}.
     * 
     * @param relation the <code>Relation</code> to check for
     * @return         <code>true</code> if this node has <code>relation</code>
     */
    //@ ensures \result == getRelations().contains(relation);
    /*@ pure */ public boolean hasRelation(Relation relation) {
        return getRelations().contains(relation);
    }
    
    /**
     * @return whether this <code>Node</code> has a {@link Relation} that determines its 
     *         {@link Placement}.
     */
    /*@ pure */ public boolean hasPlacementRelation() {
        // Minor optimalization:
        return getRelations().size() == 0 ? false : (getPlacementRelation() != null);
    }
    
    /**
     * @return the {@link Relation} that specifies the {@link Placement] of this <code>Node</code>;
     *         <code>null</code> if no placement <code>Relation</code> exists.
     */
    /*@ pure */ public Relation getPlacementRelation() {
        final RelationList placementRelations = getRelations(1).withPlacement();
        return placementRelations.size() > 0 ? placementRelations.get(0) : null;
    }

    /**
     * Returns all <code>Node</code>s that have a {@link Relation} with <code>this</code> with a 
     * specific name.
     * 
     * @param direction    see {@link #getRelations(int)}
     * @param relationName the name of the relation
     * @return             all related <code>Node</code>s
     * @throws IllegalArgumentException if <code>direction</code> is invalid
     */
    //@ requires direction == -1 || direction == 0 || direction == 1;
    /*@ pure */ @NonNull public NodeList getRelatedNodes(int direction, 
                                                         @NonNull String relationName) {
        final NodeList list = new NodeList();
        for (Relation relation : getRelations(direction).withName(relationName)) {
            list.add(relation.getOtherNode(this));
        }
        return list;
    }

    /**
     * Returns all <code>Node</code>s that have a {@link Relation} with <code>this</code>.
     * 
     * @param direction see {@link #getRelations(int)}
     * @return          all related <code>Node</code>s
     * @throws IllegalArgumentException if <code>direction</code> is invalid
     */
    //@ requires direction == -1 || direction == 0 || direction == 1;
    /*@ pure */ @NonNull public NodeList getRelatedNodes(int direction) {
        final NodeList list = new NodeList();
        for (Relation relation : getRelations(direction)) {
            list.add(relation.getOtherNode(this));
        }
        return list;
    }

    /**
     * Returns all <code>Node</code>s that have a {@link Relation} with <code>this</code>.
     * 
     * @return all related <code>Node</code>s
     */
    /*@ pure */ @NonNull public NodeList getRelatedNodes() {
        return getRelatedNodes(0);
    }

    /**
     * Returns the <code>Node</code> that has a specific {@link Relation} with <code>this</code>.
     * 
     * @param direction    see {@link #getRelations(int)}
     * @param relationName the name of the <code>Relation</code>
     * @return             the related <code>Node</code>; <code>null</code> if the specified 
     *                     <code>Relation</code> does not exist
     * @throws IllegalArgumentException if <code>direction</code> is invalid
     * @see                #getRelatedNodes()
     */
    //@ requires direction == -1 || direction == 0 || direction == 1;
    /*@ pure */ public Node getRelatedNode(int direction, @NonNull String relationName) {
        final Relation rel = getRelation(direction, relationName);
        return rel == null ? null : rel.getOtherNode(this);
    }

    /**
     * Checks if there exists a {@link Relation} with <code>node</code>.
     * 
     * @param node the other <code>Node</code>
     * @return     <code>true</code> if a <code>Relation</code> exists
     * @see         #getRelatedNodes()
     */
    /*@ pure */ public boolean hasRelationWith(Node node) {
        return getRelations().stream()
                    .filter(relation -> relation.getOtherNode(this) == node)
                    .findFirst().isPresent();
    }

    /**
     * Checks if there exists a {@link Relation} with one of the <code>Node</code>s given in
     * <code>nodes</code>.
     * 
     * @param nodes the list to check for
     * @return      <code>true</code> if a <code>Relation</code> exists with one of the 
     *              <code>Node</code>s
     * @see         #getRelatedNodes()
     */
    /*@ pure */ public boolean hasRelationWith(@NonNull NodeList nodes) {
        return getRelatedNodes().stream()
                    .filter(relatedNode -> nodes.contains(relatedNode))
                    .findFirst().isPresent();
    }
    
    /**
     * @return a clear description of this <code>Node</code>
     */
    @Override @NonNull
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
    
    /** @param id this <code>Node</code>'s id to set */
    //@ ensures getId() == id;
    public void setId(Integer id) {
        this.id = id;
    }

    /**
     * @param type this <code>Node</code>'s type to set
     * @return     <code>this</code>
     */
    //@ ensures getType() == type;
    //@ ensures \result == this;
    @NonNull public Node setType(String type) {
        this.type = type;
        return this;
    }

    /**
     * @param name this <code>Node</code>'s name to set
     * @return     <code>this</code>
     */
    //@ ensures getName() == name;
    //@ ensures \result == this;
    @NonNull public Node setName(String name) {
        this.name = name;
        return this;
    }

    /**
     * @param label the label to add to this <code>Node</code>'s labels
     * @return      <code>this</code>
     */
    //@ ensures hasLabel(label);
    //@ ensures \result == this;
    @NonNull public Node addLabel(String label) {
        if (label != null) {
            getLabels().add(label);
        }
        return this;
    }
    
    /**
     * Removes a label. Optional operation.
     * 
     * @param label the label to remove from this <code>Node</code>'s labels
     * @return      <code>this</code>
     */
    //@ ensures !hasLabel(label);
    //@ ensures \result == this;
    @NonNull public Node removeLabel(String label) {
        getLabels().remove(label);
        return this;
    }

    /**
     * Adds a {@link Relation} to this <code>Node</code> and the <code>Node</code> on the other end.
     * The <code>Relation</code> should already have either node A or node B set to the other 
     * <code>Node</code>, so the current <code>Node</code> will be set to respectively node B or 
     * node A. If this <code>Node</code> already has <code>relation</code>, nothing happens.
     * If the this <code>node</code> already has a placement relation, this method replaces it
     * with the new relation.
     * In any case, it notifies the observers.
     * 
     * @param relation the <code>Relation</code> to add
     * @return         <code>this</code>
     * @throws IllegalArgumentException if node A or B are both null or both set 
     */
    /*@ requires (relation.getNodeA() == null && relation.getNodeB() != null) ||
      @          (relation.getNodeB() == null && relation.getNodeA() != null); */
    @NonNull public Node addRelation(@NonNull Relation relation) {
        if (getRelations().contains(relation)) {
            return this;
        }
        if ((relation.getNodeA() == null && relation.getNodeB() == null)
         || (relation.getNodeA() != null && relation.getNodeB() != null)) {
            throw new IllegalArgumentException("Only and exactly one of the two ends of "
                    + "the relation should be null.");
        }
        
        // Set this node on the empty spot.
        if (relation.getNodeA() == null) {
            relation.setNodeA(this);
        } else if (relation.getNodeB() == null) {
            relation.setNodeB(this);
        }
        
        if (hasPlacementRelation() && relation.getPlacement() != Placement.NONE) {
            //TODO: make this shared code (in Client, for example), so 
            // GreenMirrorGrooyBaseScript#SwitchPlacementRelation(Relation) can use the same.
            
            final Relation currentPlacementRelation = getPlacementRelation();
            
            // If placement was random, it has been changed to a custom placement, so we need to
            // address it as such (coordinate details are irrelevant at this point).
            if (currentPlacementRelation.getPlacement() instanceof RandomPlacement) {
                currentPlacementRelation.setPlacement(new CustomPlacement());
            }
            
            setChanged();
            notifyObservers(new SwitchPlacementRelationCommand(currentPlacementRelation, relation));
            currentPlacementRelation.removeFromNodes();
            relation.addToNodes();

        // It's a normal relation: just add it.
        } else {
            relation.addToNodes();
            setChanged();
            notifyObservers(new AddRelationCommand(relation));
        }
        
        return this;
    }

    /**
     * Removes <code>relation</code> from this <code>Node</code>. Optional operation.
     * It does NOT notify the observers.
     * 
     * @param relation the {@link Relation} to remove
     */
    //@ ensures !getRelations().contains(relation);
    public void removeRelation(Relation relation) {
        if (!getRelations().contains(relation)) {
            return;
        }
        relation.removeFromNodes();
    }
    
    /**
     * Sets the new {@link FxWrapper}. This can only be done once, although if the type is 
     * the same, it will re-set it. Observers get notified of the new <code>FxWrapper</code> 
     * and this <code>Node</code> starts observing the <code>FxWrapper</code>.
     * 
     * @param fxWrapper                 the new <code>FxWrapper</code>
     * @return                          <code>this</code>
     * @throws IllegalArgumentException if the <code>FxWrapper</code> was already set and
     *                                  the argument is of a different type
     */
    @NonNull public Node set(@NonNull FxWrapper fxWrapper) {
        
        if (getFxWrapper() != null
                && !getFxWrapper().getType().equals(
                        GreenMirrorUtils.capitalizeFirstChar(fxWrapper.getType()))) {
            throw new IllegalArgumentException("you have already set the FX type");
        }
        setFxWrapper(fxWrapper);
        getFxWrapper().addObserver(this);
        setChanged();
        notifyObservers(new SetNodeFxCommand(this));
        return this;
    }
    
    /**
     * @param fxWrapper the {@link FxWrapper} to set
     */
    //@ ensures getFxWrapper() == fxWrapper;
    private void setFxWrapper(FxWrapper fxWrapper) {
        this.fxWrapper = fxWrapper;
    }

    
    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * Tries to create a {@link FxWrapper} of the type passed in the argument and returns it.
     * If the <code>FxWrapper</code> was already set and <code>type</code> is the same, it
     * returns the set <code>FxWrapper</code>. If <code>type</code> is unknown or if it's a
     * different type than the alrady set <code>FxWrapper</code>, it throws an
     * <code>IllegalArgumentException</code>.
     * <p>
     * If a new instance is created, the observer get notified.
     * <p>
     * This method should be used in Groovy Scripts. For use in the GreenMirror application 
     * itself, see {@link #getFxWrapper()}.
     * 
     * @param type the type of the <code>FxWrapper</code>. Except for the first character, the
     *             case has to match
     * @return     the just created or previously set <code>FxWrapper</code>
     * @throws IllegalArgumentException if <code>type</code> is invalid or if it's a different
     *                                  type than the currently set <code>FxWrapper</code>
     * @see    FxWrapper#getNewInstance(String)
     */
    @NonNull public FxWrapper fx(@NonNull String type) {
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
     * Returns the previously set {@link FxWrapper}, or throws an 
     * <code>IllegalStateException</code> if it wasn't set yet. This method is meant to be used
     * in Groovy user scripts.
     * 
     * @return the <code>FxWrapper</code>
     * @throws IllegalStateException if the <code>FxWrapper</code> hasn't been set
     */
    /*@ pure */ @NonNull public FxWrapper fx() {
        final FxWrapper fxwr = getFxWrapper();
        if (fxwr == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        return fxwr;
    }

    /**
     * Sends updates of the observees to its own observers. This means that the {@link FxWrapper}
     * modified and the controller should know that so it can notify the server.
     * 
     * @param observable the <code>FxWrapper</code> we're observing
     * @param arg1       any passed object from the observee
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
     * Clones this <code>Node</code>, except for the relations.
     * 
     * @return a copy of this <code>Node</code>
     */
    @Override @NonNull
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