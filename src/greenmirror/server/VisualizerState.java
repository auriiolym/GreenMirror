package greenmirror.server;

import greenmirror.Node;
import greenmirror.NodeList;

import java.util.LinkedHashMap;
import java.util.Map;

import javafx.animation.SequentialTransition;

/**
 * A class to store a system state of the visualizer.
 * Memento part of the memento design pattern: https://sourcemaking.com/design_patterns/memento
 * 
 * @author Karim El Assal
 */
public class VisualizerState {

    // -- Instance variables -----------------------------------------------------------------
    
    /**
     * The states of the nodes. They are set by node id and their visual component state is
     * stored.
     */
    //@ private invariant nodes != null;
    private Map<Integer, Map<String, Object>> nodes = new LinkedHashMap<>();
    
    /**
     * The transition needed to go to the next state.
     */
    private SequentialTransition transition;

    // -- Constructors -----------------------------------------------------------------------

    public VisualizerState(NodeList nodes, SequentialTransition transition) {
        for (Node node : nodes) {
            getNodes().put(node.getId(),
                       node.getFxWrapper() == null
                       ? new LinkedHashMap<String, Object>() : node.getFxWrapper().toMap());
        }
        this.transition = transition;
    }

    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @return {@link greenmirror.server.VisualizerState#nodes}
     */
    //@ ensures \result != null;
    /*@ pure */ public Map<Integer, Map<String, Object>> getNodes() {
        return this.nodes;
    }
    
    /**
     * @return {@link greenmirror.server.VisualizerState#transition}
     */
    /*@ pure */ public SequentialTransition getTransition() {
        return this.transition;
    }
    
    // -- Setters ----------------------------------------------------------------------------

}
