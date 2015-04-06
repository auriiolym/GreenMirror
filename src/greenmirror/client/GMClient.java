package greenmirror.client;

import greenmirror.*;

/**
 * Implements java.util.Observer.
 */
public class GMClient extends GreenMirrorController {

    private Map<String, Closure> transitions;

    /**
     * 
     * @param host
     * @param port
     */
    public void connect(String host, int port) {
        // TODO - implement GMClient.connect
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param handler
     * @param script
     */
    public void initialize(ScriptHandler handler, String script) {
        // TODO - implement GMClient.initialize
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param traceSelector
     */
    public void executeTrace(TraceSelector traceSelector) {
        // TODO - implement GMClient.executeTrace
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param o
     * @param cmd
     */
    public void update(java.util.Observable o, Object cmd) {
        // TODO - implement GMClient.update
        throw new UnsupportedOperationException();
    }

    public Map<String, Closure> getTransitions() {
        return transitions;
    }

    /**
     * 
     * @param data
     */
    public void handlePeerData(String data) {
        // TODO - implement GMClient.handlePeerData
        throw new UnsupportedOperationException();
    }

}