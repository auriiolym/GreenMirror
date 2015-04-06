package greenmirror;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Observable;
import java.util.Set;

/**
 * The <tt>Node</tt> class. This models any visual node on the visualizer.
 * 
 * Extends java.util.Observable.
 * 
 * @author Karim El Assal
 */
public class Node extends Observable {
    public static void main(String[] args) {
        System.out.println(Arrays.asList(":".split(":")));
        System.out.println(Arrays.asList(":".split(":", 2)));
        System.out.println(Arrays.asList("foo".split(":")));
        System.out.println(Arrays.asList("foo".split(":", 2)));
        System.out.println(Arrays.asList("foo:".split(":", 2)));
        System.out.println(Arrays.asList(":foo".split(":", 2)));
        String[] a = ":foo".split(":", 2);
        System.out.println(a[0].length());
    }
    
    /**
     * A class to generalize the use of the <tt>Node</tt> identifier. Possible values
     * are (without quotes): "type:name", "type:", "name".
     * 
     * @author Karim El Assal
     */
    public static class Identifier {
        
        /**
         * The name and type.
         */
        //@ private invariant name == getName();
        private String name;
        //@ private invariant type == getType();
        private String type;
        
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
    }

    private VisualComponent appearance;
    private RelationList relations;
    private VisualComponent originalAppearance;
    private Integer id = null;
    private String type;
    private String name;
    private Set<String> labels = new HashSet<String>();

    
    // -- Constructors -----------------------------------------------------------------------
    
    /**
     * Create a new <tt>Node</tt> instance with the given <tt>identifier</tt>.
     * @param identifier The name and/or type of this <tt>Node</tt>.
     */
    public Node(String identifier) {
        Node.Identifier ir = new Node.Identifier(identifier);
        if (ir.hasType()) {
            setType(ir.getType());
        }
        if (ir.hasName()) {
            setName(ir.getName());
        }
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
     * @return <tt>true</tt> if this <tt>Node</tt> has <tt>label</tt>
     */
    /*@ pure */ public boolean hasLabel(String label) {
        return labels.contains(label);
    }



    // -- Setters ----------------------------------------------------------------------------
    
    /**
     * @param idArg This <tt>Node</tt>'s id to set.
     */
    //@ ensures getId() == idArg;
    public void setId(Integer idArg) {
        id = idArg;
    }

    /**
     * @param type This <tt>Node</tt>'s type to set.
     * @return <tt>this</tt>
     */
    //@ ensures getType() == typeArg;
    public Node setType(String typeArg) {
        type = typeArg;
        return this;
    }

    /**
     * @param nameArg This <tt>Node</tt>'s name to set.
     * @return <tt>this</tt>
     */
    //@ ensures getName() == nameArg;
    public Node setName(String nameArg) {
        name = nameArg;
        return this;
    }

    /**
     * @param label Label to add to this <tt>Node</tt>'s labels.
     * @return <tt>this</tt>
     */
    //@ ensures getLabels().contains(label);
    public Node addLabel(String label) {
        labels.add(label);
        return this;
    }

    /**
     * 
     * @param appearance
     */
    public Node setAppearance(VisualComponent appearance) {
        // TODO - implement Node.setAppearance
        throw new UnsupportedOperationException();
    }

    public VisualComponent getAppearance() {
        return appearance;
    }

    public RelationList getRelations() {
        return relations;
    }

    /**
     * 
     * @param direction
     */
    public RelationList getRelations(int direction) {
        return relations;
    }

    /**
     * 
     * @param relation
     */
    public void removeRelation(Relation relation) {
        // TODO - implement Node.removeRelation
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param node
     */
    public boolean hasRelationWith(Node node) {
        // TODO - implement Node.hasRelationWith
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param nodes
     */
    public boolean hasRelationWith(NodeList nodes) {
        // TODO - implement Node.hasRelationWith
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param direction
     */
    public NodeList getRelatedNodes(int direction) {
        // TODO - implement Node.getRelatedNodes
        throw new UnsupportedOperationException();
    }

    public NodeList getRelatedNodes() {
        // TODO - implement Node.getRelatedNodes
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param direction
     * @param relationName
     */
    public Node getRelatedNode(int direction, String relationName) {
        // TODO - implement Node.getRelatedNode
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param direction
     * @param relationName
     */
    public Relation getRelation(int direction, String relationName) {
        // TODO - implement Node.getRelation
        throw new UnsupportedOperationException();
    }

    public void appearanceUpdated() {
        // TODO - implement Node.appearanceUpdated
        throw new UnsupportedOperationException();
    }

}