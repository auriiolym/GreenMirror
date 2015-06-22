package greenmirror.server;

import greenmirror.NodeList;

import org.eclipse.jdt.annotation.NonNull;

import java.util.LinkedHashMap;
import java.util.Map;

import javafx.animation.SequentialTransition;

/**
 * A class to store a system state of the visualizer. This class fulfills the memento role of the
 * memento design pattern and contains the originator and caretaker interfaces that should be
 * implemented by classes that accept those roles. More information on the pattern is found
 * <a href="https://sourcemaking.com/design_patterns/memento">here</a>.
 * 
 * @author Karim El Assal
 */
public class VisualizerMemento {
    
    /**
     * The originator role of the memento design pattern.
     * 
     * @author Karim El Assal
     */
    public static interface Originator {
        
        /**
         * Saves the current state into a memento object.
         * 
         * @param transition more data to save in the memento
         * @return           the memento instance
         */
        @NonNull public VisualizerMemento saveToMemento(@NonNull SequentialTransition transition);
        
        /**
         * Restores the state from a memento.
         * 
         * @param memento the memento that provides the data for the state.
         */
        public void restoreFromMemento(@NonNull VisualizerMemento memento);
    }
    
    /**
     * The caretaker role from the memento design pattern.
     * 
     * @author Karim El Assal
     */
    public static interface Caretaker {
        
        /**
         * Adds a memento to its collection.
         * 
         * @param memento the memento to add
         */
        public void addMemento(VisualizerMemento memento);
        
        /**
         * Retrieves a memento from its collection.
         * 
         * @param index the index of the state belonging to the memento (0 = state 0)
         * @return      the memento; <code>null</code> if it wasn't found on that index
         */
        public VisualizerMemento getMemento(int index);
        
        /**
         * Deletes all saved mementos.
         */
        public void resetSavedMementos();
    }

    // -- Instance variables -----------------------------------------------------------------
    
    /** the states of the nodes. They are set by node id. Their FX state is also stored. */
    @NonNull private Map<Integer, Map<String, Object>> nodes = new LinkedHashMap<>();
    
    /** the transition needed to go to the next state */
    @NonNull private SequentialTransition transition;

    
    // -- Constructors -----------------------------------------------------------------------

    /**
     * Creates a new memento instance. The storage of the node data is not supported in this
     * version of GreenMirror.
     * 
     * @param nodes      the node data to store in the memento
     * @param transition the data to transition to the next state, which will also be stored in 
     *                   the memento
     */
    public VisualizerMemento(NodeList nodes, @NonNull SequentialTransition transition) {
        /*for (Node node : nodes) {
            
        }*/
        this.transition = transition;
    }

    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * Returns the states of the nodes. They are set by node id. Their FX state is also stored.
     * 
     * @return the states of the nodes
     */
    /*@ pure */ @NonNull public Map<Integer, Map<String, Object>> getNodes() {
        return this.nodes;
    }
    
    /**
     * @return the transition needed to go to the next state
     */
    /*@ pure */ @NonNull public SequentialTransition getTransition() {
        return this.transition;
    }

}
