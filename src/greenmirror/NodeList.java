package greenmirror;

import java.util.LinkedList;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import org.eclipse.jdt.annotation.NonNull;

// Extends java.util.LinkedList<Node>.
/**
 * A custom <code>List</code> implementation to apply specific filters.
 * 
 * @author Karim El Assal
 */
public class NodeList extends LinkedList<Node> {
    

    // -- Constructors -----------------------------------------------------------------------
    
    /**
     * Create an empty <code>NodeList</code>.
     */
    //@ ensures this.size() == 0;
    public NodeList() {}
    
    /**
     * Create a new <code>NodeList</code> with the given <code>Node</code>s.
     * @param nodes All <code>Node</code>s you automatically want to be added.
     */
    //@ ensures this.size() == nodes.length;
    public NodeList(Node... nodes) {
        for (Node node : nodes) {
            this.add(node);
        }
    }
    
    /**
     * Create a <code>NodeList</code> with elements from <code>oldList</code>.
     * @param oldList The old list.
     */
    //@ requires oldList != null;
    //@ ensures this.size() == oldList.size();
    //TODO: add forall condition.
    public NodeList(@NonNull NodeList oldList) {
        super(oldList);
    }
    
    
    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @param currentNode The current <code>Node</code>.
     * @return            The next <code>Node</code> in the list; if <code>currentNode</code> is the
     *                    last in the list or <code>currentNode</code> doesn't appear in the list, 
     *                    the first <code>Node</code> will be returned.
     */
    //@ requires this.size() > 0;
    //@ ensures \result != null;
    /*@ pure */ public Node getCircularNext(Node currentNode) {
        int currentIndex = this.indexOf(currentNode); // Returns -1 if currentNode is not found.
        return this.get(this.size() - 1 == currentIndex ? 0 : currentIndex + 1);
    }

    /**
     * @param predicate The filter.
     * @return          A new <code>NodeList</code> with a filter applied.
     */
    //@ ensures \result.size() <= this.size();
    /*@ pure */ private NodeList withFilter(@NonNull Predicate<Node> predicate) {
        return this.stream().filter(predicate)
                .collect(Collectors.toCollection(NodeList::new));
    }
    
    /**
     * Get a <code>NodeList</code> which contains <code>Node</code>s that correspond to the 
     * <code>identifier</code>.
     * @param identifier See {@link greenmirror.Node.Identifier}.
     * @return           A new <code>NodeList</code> with the matching <code>Node</code>s.
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
     * Get a <code>NodeList</code> which contains <code>Node</code>s that correspond to the 
     * <code>identifier</code>.
     * @param identifier See {@link greenmirror.Node.Identifier#Identifier(String)}.
     * @return           A new <code>NodeList</code> with the matching <code>Node</code>s.
     */
    //@ requires identifier != null;
    //@ ensures \result != null;
    /*@ pure */ public NodeList withIdentifier(String identifier) {
        return withIdentifier(new Node.Identifier(identifier));
    }
    
    /**
     * @param name The name part of a <code>Node.Identifier</code>.
     * @return     Every <code>Node</code> with <code>name</code>. 
     */
    //@ requires name != null;
    //@ ensures \result != null;
    /*@ pure */ public NodeList withName(String name) {
        Node.Identifier identifier = new Node.Identifier();
        identifier.setName(name);
        return withIdentifier(identifier);
    }

    /**
     * @param type The name part of a <code>Node.Identifier</code>.
     * @return     Every <code>Node</code> of <code>type</code>.
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
     * @return      Every <code>Node</code> that has <code>label</code>.
     */
    //@ requires label != null;
    //@ ensures \result != null;
    /*@ pure */ public NodeList withLabel(String label) {
        return withFilter(node -> node.hasLabel(label));
    }

    /**
     * Get <code>Node</code>s that have a <code>Relation</code> with any of <code>nodes</code> in the 
     * specified </code>direction</code>.
     * @param direction  The direction of the <code>Relation</code>s. See 
     *                   {@link greenmirror.Node#getRelations(int)}.
     * @param matchNodes Possible <code>Node</code>s on the other end of the <code>Relation</code>.
     * @return           The matching <code>Node</code>s.
     */
    //@ requires direction == -1 || direction == 0 || direction == 1;
    //@ requires matchNodes != null;
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
    
    public NodeList withRelationTo(int direction, @NonNull Node matchNode) {
        return withRelationTo(direction, new NodeList(matchNode));
    }
    
    /**
     * Get <code>Node</code>s that have a specific <code>Relation</code>.
     * @param direction    The direction of the <code>Relation</code>. See
     *                     {@link greenmirror.Node#getRelations(int)}.
     * @param relationName The name of the relation.
     * @return             The matching <code>Node</code>s.
     */
    //@ requires direction == -1 || direction == 0 || direction == 1;
    //@ requires relationName != null;
    //@ ensures \result != null;
    /*@ pure */ public NodeList withRelation(int direction, String relationName) {
        return withFilter(node -> node.getRelation(direction, relationName) != null);
    }
    
    /*@ pure */ public NodeList without(@NonNull NodeList nodes) {
        return withFilter(node -> !nodes.contains(node));
    }
    
    /*@ pure */ public NodeList without(@NonNull Node... nodes) {
        return without(new NodeList(nodes));
    }
    
    /*@ pure */ public NodeList not(@NonNull NodeList nodes) {
        return without(new NodeList(nodes));
    }
    
    /*@ pure */ public NodeList not(@NonNull Node... nodes) {
        return without(new NodeList(nodes));
    }
    

    /**
     * @return This <code>NodeList</code> truncated with only the first element left;
     *         or just an empty <code>NodeList</code> if <code>this</code> doesn't contain any 
     *         <code>Node</code>s.
     */
    //@ ensures (this.size() == 0) ? true : (\result.size() == 1);
    /*@ pure */ @NonNull public NodeList one() {
        return this.isEmpty() ? this : new NodeList(this.get(0));
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    /**
     * Add a <code>Relation</code> to multiple <code>Node</code>s at once (although still sequential).
     * @param relation The <code>Relation</code> to add.
     * @return         <code>this</code>
     */
    //@ requires relation != null;
    public NodeList addRelation(Relation relation) {
        this.forEach(node -> node.addRelation(relation));
        return this;
    }

    /**
     * Remove a <code>Relation</code> from multiple <code>Node</code>s at once (altough still sequential).
     * @param relationName The name of the <code>Relation</code>.
     * @return             <code>this</code>
     */
    public NodeList removeRelation(String relationName) {
        this.forEach(node -> {
            node.removeRelation(node.getRelation(0, relationName));
        });
        return this;
    }
}