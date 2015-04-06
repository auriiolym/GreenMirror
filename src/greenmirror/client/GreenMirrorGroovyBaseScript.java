package greenmirror.client;

import greenmirror.*;

/**
 * Extends groovy.lang.Script.
 */
public class GreenMirrorGroovyBaseScript {

    private GMClient controller;

    /**
     * 
     * @param controller
     */
    public GreenMirrorGroovyBaseScript(GMClient controller) {
        // TODO - implement GreenMirrorGroovyBaseScript.GreenMirrorGroovyBaseScript
        throw new UnsupportedOperationException();
    }

    private GMClient getController() {
        return controller;
    }

    /**
     * 
     * @param width
     * @param height
     */
    public void initialize(int width, int height) {
        // TODO - implement GreenMirrorGroovyBaseScript.initialize
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param name
     */
    public Node addNode(String name) {
        // TODO - implement GreenMirrorGroovyBaseScript.addNode
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param node
     */
    public Node addNode(Node node) {
        // TODO - implement GreenMirrorGroovyBaseScript.addNode
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param transition
     * @param code
     */
    public void addTransition(String transition, Closure code) {
        // TODO - implement GreenMirrorGroovyBaseScript.addTransition
        throw new UnsupportedOperationException();
    }

    public NodeList nodes() {
        // TODO - implement GreenMirrorGroovyBaseScript.nodes
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param name
     */
    public NodeList nodes(String name) {
        // TODO - implement GreenMirrorGroovyBaseScript.nodes
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param name
     */
    public NodeList node(String name) {
        // TODO - implement GreenMirrorGroovyBaseScript.node
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param nodes
     */
    public void removeNodes(NodeList nodes) {
        // TODO - implement GreenMirrorGroovyBaseScript.removeNodes
        throw new UnsupportedOperationException();
    }

}