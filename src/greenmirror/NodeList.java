package greenmirror;

import java.util.LinkedList;

/**
 * Extends java.util.LinkedList<Node>.
 */
public class NodeList extends LinkedList<Node> {
    private static final long serialVersionUID = 0;
    
    /**
     * 
     * @param name
     */
    public NodeList withName(String name) {
        // TODO - implement NodeList.withName
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param type
     */
    public NodeList ofType(String type) {
        // TODO - implement NodeList.ofType
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param label
     */
    public NodeList withLabel(String label) {
        // TODO - implement NodeList.withLabel
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param direction
     * @param nodes
     */
    public NodeList withRelation(int direction, NodeList nodes) {
        // TODO - implement NodeList.withRelation
        throw new UnsupportedOperationException();
    }

    public NodeList one() {
        // TODO - implement NodeList.one
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param relation
     */
    public NodeList addRelation(Relation relation) {
        // TODO - implement NodeList.addRelation
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param relationName
     */
    public NodeList removeRelations(String relationName) {
        // TODO - implement NodeList.removeRelations
        throw new UnsupportedOperationException();
    }

}