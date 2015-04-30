package greenmirror;

import greenmirror.commands.AddRelationCommand;
import greenmirror.commands.RemoveRelationCommand;
import greenmirror.commands.SetNodeAppearanceCommand;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Observable;
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
public class Node extends Observable {
    
    /**
     * A class to generalize the use of the <tt>Node</tt> identifiers. Possible values
     * are (without quotes): "type:name", "type:", "name".
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
     * The original and current appearance.
     */
    private VisualComponent originalAppearance;
    private VisualComponent appearance;
    
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
        Node.Identifier ir = new Node.Identifier(identifier);
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
     * @return The original appearance.
     */
    /*@ pure */ public VisualComponent getOriginalAppearance() {
        return originalAppearance;
    }

    /**
     * @return The current appearance.
     */
    /*@ pure */ public VisualComponent getAppearance() {
        return appearance;
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
     * Checks if there exists a <tt>Relation</tt> with on of the <tt>Node</tt>s given in
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
              "Node id=" + (getId() == null ? "" : getId().toString())
            + " | type=" + (getType() == null ? "" : getType().toString())
            + " | name=" + (getName() == null ? "" : getName().toString())
            + " | labels=" + getLabels().toString()
            + " | relations=" + getRelations().toString();
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
     * @param appearance The original appearance to set.
     * @return <tt>this</tt>
     */
    //@ ensures getOriginalAppearance() == appearance;
    //@ ensures \result == this;
    public Node setOriginalAppearance(VisualComponent appearance) {
        originalAppearance = appearance;
        //TODO: notify the observer (?).
        return this;
    }

    /**
     * @param appearance The current appearance to set.
     * @return <tt>this</tt>
     * @throws IllegalArgumentException If the new <tt>VisualComponent</tt> is not the same 
     *                                  as the old one.
     */
    //@ ensures getAppearance() == appearance;
    //@ ensures \result == this;
    public Node setAppearance(VisualComponent appearance) {
        if (getAppearance() != null
        && !getAppearance().getClass().getName().equals(appearance.getClass().getName())) {
            throw new IllegalArgumentException("The new appearance of a node has to be of the "
                    + "same type as the current appareance.");
        }
        Map<String, Object> changedValues = new HashMap<>();
        if (getAppearance() == null) {
            changedValues = appearance.toMap();
        } else {
            for (Map.Entry<String, Object> amap : appearance.toMap().entrySet()) {
                if (!amap.getValue().equals(getAppearance().toMap().get(amap.getKey()))) {
                    changedValues.put(amap.getKey(), amap.getValue());
                }
            }
        }
        this.appearance = appearance;
        appearance.setGreenMirrorNode(this);
        appearanceUpdated(changedValues);
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
        relation.remove();
    }

    
    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * Notify the observers that a <tt>Relation</tt> was removed.
     * @param relation
     */
    public void relationRemoved(Relation relation) {
        setChanged();
        notifyObservers(new RemoveRelationCommand(relation));
    }

    /**
     * Notify observers that the given appearance has been updated.
     */
    public void appearanceUpdated(Map<String, Object> changedValues) {
        setChanged();
        notifyObservers(new SetNodeAppearanceCommand(this, 
                changedValues == null ? getAppearance().toMap() : changedValues));
    }
    
    public void appearanceUpdated(String var, Object val) {
        appearanceUpdated(new HashMap<String, Object>() {
            {
                put(var, val);
            }
        });
    }

}