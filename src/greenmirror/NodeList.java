package greenmirror;

import java.util.LinkedList;
import java.util.function.Predicate;
import java.util.stream.Collectors;

// Extends java.util.LinkedList<Node>.
/**
 * A custom <tt>List</tt> implementation to apply specific filters.
 * 
 * @author Karim El Assal
 */
public class NodeList extends LinkedList<Node> {
    

    // -- Constructors -----------------------------------------------------------------------
    
    /**
     * Create an empty <tt>NodeList</tt>.
     */
    //@ ensures this.size() == 0;
    public NodeList() {}
    
    /**
     * Create a new <tt>NodeList</tt> with the given <tt>Node</tt>s.
     * @param nodes All <tt>Node</tt>s you automatically want to be added.
     */
    //@ ensures this.size() == nodes.length;
    public NodeList(Node... nodes) {
        for (Node node : nodes) {
            this.add(node);
        }
    }
    
    /**
     * Create a <tt>NodeList</tt> with elements from <tt>oldList</tt>.
     * @param oldList The old list.
     */
    //@ requires oldList != null;
    //@ ensures this.size() == oldList.size();
    //TODO: add forall condition.
    public NodeList(NodeList oldList) {
        super(oldList);
    }
    
    
    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @param currentNode The current <tt>Node</tt>.
     * @return            The next <tt>Node</tt> in the list; if <tt>currentNode</tt> is the
     *                    last in the list or <tt>currentNode</tt> doesn't appear in the list, 
     *                    the first <tt>Node</tt> will be returned.
     */
    //@ requires this.size() > 0;
    //@ ensures \result != null;
    /*@ pure */ public Node getCircularNext(Node currentNode) {
        int currentIndex = this.indexOf(currentNode); // Returns -1 if currentNode is not found.
        return this.get(this.size() - 1 == currentIndex ? 0 : currentIndex + 1);
    }

    /**
     * @param predicate The filter.
     * @return          A new <tt>NodeList</tt> with a filter applied.
     */
    //@ requires predicate != null;
    //@ ensures \result != null;
    //@ ensures \result.size() <= this.size();
    /*@ pure */ private NodeList withFilter(Predicate<Node> predicate) {
        return this.stream().filter(predicate)
                .collect(Collectors.toCollection(NodeList::new));
    }
    
    /**
     * Get a <tt>NodeList</tt> which contains <tt>Node</tt>s that correspond to the 
     * <tt>identifier</tt>.
     * @param identifier See {@link greenmirror.Node.Identifier}.
     * @return           A new <tt>NodeList</tt> with the matching <tt>Node</tt>s.
     */
    //@ requires identifier != null;
    //@ ensures \result != null;
    /*@ pure */ public NodeList withIdentifier(Node.Identifier identifier) {
        /*NodeList result = new NodeList();
        
        for (Node node : this) {
            if ((identifier.hasType() && !identifier.getType().equals(node.getType()))
             || (identifier.hasName() && !identifier.getName().equals(node.getName()))) {
                continue;
            }
            result.add(node);
        }*/
        
        return withFilter(node -> 
                    identifier.hasType() ? identifier.getType().equals(node.getType()) : true)
              .withFilter(node ->
                    identifier.hasName() ? identifier.getName().equals(node.getName()) : true);
        
    }
    
    /**
     * Get a <tt>NodeList</tt> which contains <tt>Node</tt>s that correspond to the 
     * <tt>identifier</tt>.
     * @param identifier See {@link greenmirror.Node.Identifier#Identifier(String)}.
     * @return           A new <tt>NodeList</tt> with the matching <tt>Node</tt>s.
     */
    //@ requires identifier != null;
    //@ ensures \result != null;
    /*@ pure */ public NodeList withIdentifier(String identifier) {
        return withIdentifier(new Node.Identifier(identifier));
    }
    
    /**
     * @param name The name part of a <tt>Node.Identifier</tt>.
     * @return     Every <tt>Node</tt> with <tt>name</tt>. 
     */
    //@ requires name != null;
    //@ ensures \result != null;
    /*@ pure */ public NodeList withName(String name) {
        Node.Identifier identifier = new Node.Identifier();
        identifier.setName(name);
        return withIdentifier(identifier);
    }

    /**
     * @param type The name part of a <tt>Node.Identifier</tt>.
     * @return     Every <tt>Node</tt> of <tt>type</tt>.
     */
    //@ requires type != null;
    //@ ensures \result != null;
    /*@ pure */ public NodeList ofType(String type) {
        Node.Identifier identifier = new Node.Identifier();
        identifier.setType(type);
        return withIdentifier(identifier);
    }

    /**
     * @param label The label to match for.
     * @return      Every <tt>Node</tt> that has <tt>label</tt>.
     */
    //@ requires label != null;
    //@ ensures \result != null;
    /*@ pure */ public NodeList withLabel(String label) {
        return withFilter(node -> node.hasLabel(label));
    }

    /**
     * Get <tt>Node</tt>s that have a <tt>Relation</tt> with any of <tt>nodes</tt> in the 
     * specified </tt>direction</tt>.
     * @param direction The direction of the <tt>Relation</tt>s. See 
     *                  {@link greenmirror.Node#getRelations(int)}.
     * @param nodes     Possible <tt>Node</tt>s on the other end of the <tt>Relation</tt>.
     * @return          The matching <tt>Node</tt>s.
     */
    //@ requires direction == -1 || direction == 0 || direction == 1;
    //@ requires nodes != null;
    //@ ensures \result != null;
    /*@ pure */ public NodeList withRelationTo(int direction, NodeList matchNodes) {
        return withFilter(node -> {
            for (Node relatedNode : node.getRelatedNodes(direction)) {
                if (matchNodes.contains(relatedNode)) {
                    return true;
                }
            }
            return false;
        });
    }
    
    /**
     * Get <tt>Node</tt>s that have a specific <tt>Relation</tt>.
     * @param direction    The direction of the <tt>Relation</tt>. See
     *                     {@link greenmirror.Node#getRelations(int)}.
     * @param relationName The name of the relation.
     * @return             The matching <tt>Node</tt>s.
     */
    //@ requires direction == -1 || direction == 0 || direction == 1;
    //@ requires relationName != null;
    //@ ensures \result != null;
    /*@ pure */ public NodeList withRelation(int direction, String relationName) {
        return withFilter(node -> node.getRelation(direction, relationName) != null);
    }

    /**
     * @return This <tt>NodeList</tt> truncated with only the first element left;
     *         or just an empty <tt>NodeList</tt> if <tt>this</tt> doesn't contain any 
     *         <tt>Node</tt>s.
     */
    //@ requires this.size() > 0;
    /*@ pure */ public NodeList one() {
        if (this.size() == 0) {
            return null;
        } else {
            return new NodeList(this.get(0));
        }
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    /**
     * Add a <tt>Relation</tt> to multiple <tt>Node</tt>s at once (although still sequential).
     * @param relation The <tt>Relation</tt> to add.
     * @return         <tt>this</tt>
     */
    //@ requires relation != null;
    public NodeList addRelation(Relation relation) {
        this.forEach(node -> node.addRelation(relation));
        return this;
    }

    /**
     * Remove a <tt>Relation</tt> from multiple <tt>Node</tt>s at once (altough still sequential).
     * @param relationName The name of the <tt>Relation</tt>.
     * @return             <tt>this</tt>
     */
    public NodeList removeRelation(String relationName) {
        this.forEach(node -> {
            node.removeRelation(node.getRelation(0, relationName));
        });
        return this;
    }
    
    /**
     * Set the appearance of all <tt>Node</tt>s in the list.
     * @param visualComponent {@link greenmirror.Node#setAppearance(VisualComponent)}
     * @return                <tt>this</tt>
     */
    public NodeList setAppearance(VisualComponent visualComponent) {
        this.forEach(node -> node.setAppearance(visualComponent));
        return this;
    }
}