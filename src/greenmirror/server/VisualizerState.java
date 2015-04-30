package greenmirror.server;

import greenmirror.Node;
import greenmirror.NodeList;

import java.util.HashMap;
import java.util.Map;

import javafx.animation.Transition;

/**
 * A class to store a system state of the visualizer.
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
    private Map<Integer, Map<String, Object>> nodes = new HashMap<>();
    
    /**
     * The transition needed to go to the next state.
     */
    private Transition transition;

    // -- Constructors -----------------------------------------------------------------------

    public VisualizerState(NodeList nodes, Transition transition) {
        for (Node node : nodes) {
            
            this.nodes.put(node.getId(),
                        node.getAppearance() == null
                        ? new HashMap<String, Object>() : node.getAppearance().toMap());
        }
        this.transition = transition;
    }

    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @return {@link greenmirror.server.VisualizerState#nodes}
     */
    //@ ensures \result != null;
    /*@ pure */ public Map<Integer, Map<String, Object>> getNodes() {
        return nodes;
    }
    
    /**
     * @return {@link greenmirror.server.VisualizerState#transition}
     */
    /*@ pure */ public Transition getTransition() {
        return transition;
    }
    
    // -- Setters ----------------------------------------------------------------------------

}
