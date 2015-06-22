package greenmirror;

import greenmirror.Node.Identifier;
import org.eclipse.jdt.annotation.NonNull;

import java.util.LinkedList;
import java.util.function.Predicate;
import java.util.stream.Collectors;

/**
 * A custom <code>List</code> extension to apply specific filters to a list of <code>Node</code>.
 * 
 * @author Karim El Assal
 */
public class NodeList extends LinkedList<Node> {
    
    // -- Constructors -----------------------------------------------------------------------
    
    /** Creates an empty <code>NodeList</code>. */
    //@ ensures this.size() == 0;
    public NodeList() {}
    
    /**
     * Creates a new <code>NodeList</code> with the given <code>Node</code>s.
     * 
     * @param nodes all <code>Node</code>s that should be added
     */
    //@ ensures this.size() == nodes.length;
    public NodeList(Node... nodes) {
        if (nodes == null) {
            return;
        }
        for (Node node : nodes) {
            this.add(node);
        }
    }
    
    /**
     * Creates a <code>NodeList</code> with all <code>Node</code>s from <code>oldList</code>.
     * 
     * @param oldList The old list.
     */
    //@ ensures this.size() == oldList.size();
    public NodeList(@NonNull NodeList oldList) {
        super(oldList);
    }
    
    
    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @param currentNode the current <code>Node</code>
     * @return            the next <code>Node</code> in the list; if <code>currentNode</code> is the
     *                    last in the list or <code>currentNode</code> doesn't appear in the list, 
     *                    the first <code>Node</code> will be returned
     * @throws NullPointerException if <code>this</code> list is empty
     */
    //@ requires this.size() > 0;
    //@ ensures \result != null;
    /*@ pure */ public Node getCircularNext(Node currentNode) {
        final int currentIndex = this.indexOf(currentNode); // == -1 if currentNode is not found.
        return this.get(this.size() - 1 == currentIndex ? 0 : currentIndex + 1);
    }

    /**
     * Returns a new list with only the nodes that pass through the filter.
     * 
     * @param predicate the filter
     * @return          a new <code>NodeList</code> with a filter applied
     */
    //@ ensures \result.size() <= this.size();
    /*@ pure */ @NonNull private NodeList withFilter(@NonNull Predicate<Node> predicate) {
        final NodeList list = this.stream().filter(predicate)
                                  .collect(Collectors.toCollection(NodeList::new));
        return list == null ? new NodeList() : list;
    }
    
    /**
     * Gets a <code>NodeList</code> which contains <code>Node</code>s that correspond to the 
     * <code>identifier</code>.
     * 
     * @param identifier see {@link Identifier}
     * @return           a new <code>NodeList</code> with the matching <code>Node</code>s
     */
    /*@ pure */ @NonNull public NodeList withIdentifier(@NonNull Identifier identifier) { 
        return withFilter(node -> 
                    identifier.hasType() ? identifier.getType().equals(node.getType()) : true)
              .withFilter(node ->
                    identifier.hasName() ? identifier.getName().equals(node.getName()) : true);
    }
    
    /**
     * Gets a <code>NodeList</code> which contains <code>Node</code>s that correspond to the 
     * <code>identifier</code>.
     * 
     * @param identifier see {@link greenmirror.Node.Identifier#Identifier(String)}
     * @return           a new <code>NodeList</code> with the matching <code>Node</code>s
     */
    /*@ pure */ @NonNull public NodeList withIdentifier(String identifier) {
        return withIdentifier(new Identifier(identifier));
    }
    
    /**
     * @param name the name part of a <code>Node.Identifier</code>
     * @return     every <code>Node</code> with <code>name</code> that is on the current list 
     */
    /*@ pure */ @NonNull public NodeList withName(String name) {
        final Identifier identifier = new Identifier();
        identifier.setName(name);
        return withIdentifier(identifier);
    }

    /**
     * @param type the name part of a <code>Node.Identifier</code>
     * @return     every <code>Node</code> of <code>type</code> that is on the current list
     */
    /*@ pure */ @NonNull public NodeList ofType(String type) {
        final Identifier identifier = new Identifier();
        identifier.setType(type);
        return withIdentifier(identifier);
    }

    /**
     * @param label the label to match for
     * @return      every <code>Node</code> that has <code>label</code> that is on the current list
     */
    /*@ pure */ @NonNull public NodeList withLabel(String label) {
        return withFilter(node -> node.hasLabel(label));
    }

    /**
     * Gets <code>Node</code>s that have a {@link Relation} with any of <code>nodes</code> 
     * in the specified <code>direction</code>.
     * 
     * @param direction  see {@link Node#getRelations(int)}
     * @param matchNodes possible <code>Node</code>s on the other end of the <code>Relation</code>
     * @return           the matching <code>Node</code>s
     * @throws IllegalArgumentException if <code>direction</code> is invalid
     */
    //@ requires direction == -1 || direction == 0 || direction == 1;
    /*@ pure */ @NonNull public NodeList withRelationTo(int direction, 
                                                        @NonNull NodeList matchNodes) {
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
     * The same as {{@link #withRelationTo(int, NodeList)}, but with one <code>Node</code>.
     * 
     * @param direction  see {@link Node#getRelations(int)}
     * @param matchNode  possible <code>Node</code> on the other end of the <code>Relation</code>
     * @return           the matching <code>Node</code>s
     * @throws IllegalArgumentException if <code>direction</code> is invalid
     * @see #withRelationTo(int, NodeList)
     */
    //@ requires direction == -1 || direction == 0 || direction == 1;
    /*@ pure */ @NonNull public NodeList withRelationTo(int direction, @NonNull Node matchNode) {
        return withRelationTo(direction, new NodeList(matchNode));
    }
    
    /**
     * Gets <code>Node</code>s that have a specific {@link Relation}.
     * 
     * @param direction    see {@link Node#getRelations(int)}
     * @param relationName the name of the relation
     * @return             the matching <code>Node</code>s
     * @throws IllegalArgumentException if <code>direction</code> is invalid
     */
    //@ requires direction == -1 || direction == 0 || direction == 1;
    /*@ pure */ @NonNull public NodeList withRelation(int direction, @NonNull String relationName) {
        return withFilter(node -> node.getRelation(direction, relationName) != null);
    }
    
    /**
     * Gets the list without the nodes passed in the argument.
     * 
     * @param nodes the <code>Node</code>s that won't be in the result
     * @return      the list not matching <code>nodes</code>
     */
    /*@ pure */ @NonNull public NodeList without(@NonNull NodeList nodes) {
        return withFilter(node -> !nodes.contains(node));
    }
    
    /**
     * @param nodes the <code>Node</code>s that won't be in the result
     * @return      the list not matching <code>nodes</code>
     * @see #without(NodeList)
     */
    /*@ pure */ @NonNull public NodeList without(@NonNull Node... nodes) {
        return without(new NodeList(nodes));
    }
    
    /**
     * @param nodes the <code>Node</code>s that won't be in the result
     * @return      the list not matching <code>nodes</code>
     * @see #without(NodeList)
     */
    /*@ pure */ @NonNull public NodeList not(@NonNull NodeList nodes) {
        return without(new NodeList(nodes));
    }
    
    /**
     * @param nodes the <code>Node</code> that won't be in the result
     * @return      the list not matching <code>nodes</code>
     * @see #without(NodeList)
     */
    /*@ pure */ @NonNull public NodeList not(@NonNull Node... nodes) {
        return without(new NodeList(nodes));
    }
    
    /**
     * @return this <code>NodeList</code> truncated to only the first element;
     *         or just an empty <code>NodeList</code> if <code>this</code> doesn't contain any 
     *         <code>Node</code>s
     */
    //@ ensures (this.size() == 0) ? true : (\result.size() == 1);
    /*@ pure */ @NonNull public NodeList one() {
        return this.isEmpty() ? this : new NodeList(this.get(0));
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    /**
     * Adds a {@link Relation} to multiple <code>Node</code>s.
     * 
     * @param relation the <code>Relation</code> to add
     * @return         <code>this</code>
     */
    @NonNull public NodeList addRelation(@NonNull Relation relation) {
        this.forEach(node -> node.addRelation(relation));
        return this;
    }

    /**
     * Removes a {@link Relation} from multiple <code>Node</code>s.
     * 
     * @param relationName the name of the <code>Relation</code>
     * @return             <code>this</code>
     */
    @NonNull public NodeList removeRelation(@NonNull String relationName) {
        this.forEach(node -> {
            node.removeRelation(node.getRelation(0, relationName));
        });
        return this;
    }
}