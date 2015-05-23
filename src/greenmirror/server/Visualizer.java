package greenmirror.server;

import greenmirror.CommunicationFormat;
import greenmirror.FxContainer;
import greenmirror.Log;
import greenmirror.Node;
import greenmirror.Placement;
import greenmirror.Relation;
import greenmirror.WindowLogger;
import greenmirror.server.playbackstates.PausedState;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import javafx.animation.Animation;
import javafx.animation.FadeTransition;
import javafx.animation.ParallelTransition;
import javafx.animation.SequentialTransition;
import javafx.animation.Transition;
import javafx.application.Application;
import javafx.application.Platform;
import javafx.collections.ObservableList;
import javafx.geometry.Point3D;
import javafx.scene.layout.Pane;
import javafx.scene.text.Text;
import javafx.stage.Stage;
import javafx.util.Duration;


/**
 * The main visualizer class and JavaFX application. It starts the log window and waits for 
 * connections. 
 * 
 * @author Karim El Assal
 */
public class Visualizer extends Application {
    
    // -- Inner classes ----------------------------------------------------------------------
    
    /**
     * An abstract state class in accordance with the state design pattern.
     * 
     * @author Karim El Assal
     */
    public abstract static class PlaybackState {
        
        /**
         * The method that determines the toolbar button operation in accordance with 
         * <tt>hasPreviousState</tt> and <tt>hasNextState</tt>.
         * @param hasPreviousState
         * @param hasNextState
         */
        public abstract void determineButtonOperation(boolean hasPreviousState, 
                boolean hasNextState);
        
        /**
         * @return Whether this <tt>PlaybackState</tt> is a continuous one.
         */
        public abstract boolean isContinuous();
        
        /**
         * @return A simple explanation of this state.
         */
        @Override
        public abstract String toString();
    }
    
    // -- Enumerations -----------------------------------------------------------------------
    
    // -- Constants --------------------------------------------------------------------------
    
    private static final double DEFAULT_ANIMATION_DURATION = 1000.0;
    
    private static final double DEFAULT_TRANSITION_DELAY = 300.0;
    
    // -- Class variables --------------------------------------------------------------------

    // -- Instance variables -----------------------------------------------------------------

    /**
     * The controller.
     */
    private ServerController controller;
    
    /**
     * The current playback state of the visualizer.
     */
    private PlaybackState currentPlaybackState = new PausedState();
    
    /**
     * The <tt>Stage</tt> of the visualizer.
     */
    private Stage stage;
    
    /**
     * The default duration of animations. -1 for unspecified duration.
     */
    //@ private invariant defaultAnimationDuration >= -1.0;
    private double defaultAnimationDuration = DEFAULT_ANIMATION_DURATION;
    
    
    private double currentAnimationDuration = -1.0;
    
    private double currentTransitionDelay = DEFAULT_TRANSITION_DELAY;
    
    /**
     * The current queue of visualizations.
     */
    //@ private invariant visualizationsQueue != null;
    private SequentialTransition visualizationsQueue;
    
    //@ private invariant states != null;
    private List<VisualizerState> states = new LinkedList<>();
    
    //@ private invariant currentStateIndex >= 0;
    private int currentStateIndex = 0;

    
    // -- Constructors -----------------------------------------------------------------------
    
    public Visualizer() {
        super();
        resetVisualizationQueue();
    }

    // -- Queries ----------------------------------------------------------------------------

    /**
     * @return The controller.
     */
    /*@ pure */ public ServerController getController() {
        return controller;
    }
    
    /**
     * @return The current status of the visualizer.
     */
    //@ ensures \result != null;
    /*@ pure */ public PlaybackState getPlaybackState() {
        return currentPlaybackState;
    }

    /**
     * @return The <tt>Stage</tt> of the visualizer.
     */
    /*@ pure */ public Stage getStage() {
        return stage;
    }
    
    /**
     * @return The Pane containing all visualization elements of the visualizer.
     * @throws IllegalStateException If the FX node pane wasn't found.
     */
    //@ requires getStage() != null;
    /*@ pure */ public Pane getFxNodePane() {
        Pane container = (Pane) getStage().getScene().lookup("#FxNodePane");
        if (container == null) {
            throw new IllegalStateException("The stage hasn't been set up properly (yet).");
        }
        return container;
    }
    
    /**
     * @return The default animation duration.
     */
    //@ ensures \result >= -1.0;
    /*@ pure */ public double getDefaultAnimationDuration() {
        return defaultAnimationDuration;
    }
    
    /**
     * @return The current animation duration or, if not set, the default animation duration.
     */
    //@ ensures \result >= 0;
    /*@ pure */ public double getCurrentAnimationDuration() {
        return currentAnimationDuration >= 0
                ? currentAnimationDuration : getDefaultAnimationDuration();
    }
    
    /**
     * @return The currently set delay between transitions.
     */
    //@ ensures \result >= 0;
    /*@ pure */ public double getCurrentTransitionDelay() {
        return currentTransitionDelay >= 0
                ? currentTransitionDelay : DEFAULT_TRANSITION_DELAY;
    }

    /**
     * @return The visualizations queue.
     */
    //@ ensures \result != null;
    /*@ pure */ public SequentialTransition getVisualizationsQueue() {
        return this.visualizationsQueue;
    }
    
    /**
     * @return The current 'sub'-queue of visualizations.
     */
    //@ requires getVisualizationsQueue() != null;
    //@ requires getVisualizationsQueue().getChildren().size() > 0;
    //@ ensures \result != null;
    /*@ pure */ private ParallelTransition getCurrentSubVisualizationQueue() {
        ObservableList<Animation> rootTransitions = getVisualizationsQueue().getChildren();
        return (ParallelTransition) rootTransitions.get(rootTransitions.size() - 1);
    }
    
    /**
     * @return All states of the visualizer.
     */
    //@ ensures \result != null;
    /*@ pure */ private List<VisualizerState> getStates() {
        return this.states;
    }
    
    /**
     * @return The amount of states currently stored.
     */
    //@ ensures \result >= 0;
    /*@ pure */ public int getStateCount() {
        return getStates().size();
    }
    
    //@ ensures \result >= 0;
    /*@ pure */ public int getCurrentStateIndex() {
        return this.currentStateIndex;
    }
    
    /*@ pure */ public int getCurrentStateNumber() {
        return getCurrentStateIndex();
    }
    
    /*@ pure */ public boolean hasNextState() {
        return getCurrentStateNumber() < getStateCount();
    }
    
    /*@ pure */ public boolean hasPreviousState() {
        return getCurrentStateNumber() > 1;
    }
    
    /**
     * @return The <tt>Transition</tt> that transitions to the next state.
     */
    //@ requires hasNextState();
    /*@ pure */ public SequentialTransition getNextTransition() {
        return getStates().get(getCurrentStateIndex()).getTransition();
    }
    
    /**
     * @return The <tt>Transition</tt> that transitions to the previous state.
     */
    //@ requires hasPreviousState();
    /*@ pure */ public SequentialTransition getPreviousTransition() {
        return getStates().get(getCurrentStateIndex() - 1).getTransition();
    }

    
    
    // -- Setters ----------------------------------------------------------------------------
    
    /**
     * @param playbackState The new current status of the visualizer.
     */
    //@ requires playbackState != null;
    //@ ensures getPlaybackState() == playbackState;
    public void setPlaybackState(PlaybackState playbackState) {
        this.currentPlaybackState = playbackState;
        updatePlaybackStateInfo();
    }

    /**
     * @param stage The <tt>Stage</tt> of the visualizer to set.
     */
    //@ ensures getStage() == stage;
    public void setStage(Stage stage) {
        this.stage = stage;
    }
    
    /**
     * @param defaultAnimationDuration The defaultAnimationDuration to set.
     */
    //@ requires defaultAnimationDuration >= -1.0;
    //@ ensures getDefaultAnimationDuration() == defaultAnimationDuration;
    public void setDefaultAnimationDuration(double defaultAnimationDuration) {
        this.defaultAnimationDuration = defaultAnimationDuration;
    }
    
    /**
     * @param currentAnimationDuration The currentAnimationDuration to set.
     */
    //@ requires currentAnimationDuration >= -1.0;
    public void setCurrentAnimationDuration(double currentAnimationDuration) {
        this.currentAnimationDuration = currentAnimationDuration;
    }
    
    /**
     * @param transition The transition to add.
     */
    //@ requires transition != null;
    //@ ensures getCurrentSubVisualizationQueue().getChildren().contains(transition);
    public void addToVisualizationsQueue(Transition transition) {
        getCurrentSubVisualizationQueue().getChildren().add(transition);
    }
    
    //@ ensures \old(getCurrentStateIndex()) + 1 = getCurrentStateIndex();
    public void incrementCurrentStateIndex() {
        currentStateIndex++;
    }
    
    //@ ensures \old(getCurrentStateIndex()) - 1 = getCurrentStateIndex();
    public void decrementCurrentStateIndex() {
        currentStateIndex--;
    }

    
    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * Save the current state with the passed <tt>transition</tt> that holds the animations
     * to go to the next state.
     * @param transitions
     */
    public void saveState(SequentialTransition transition) {
        getStates().add(new VisualizerState(getController().getNodes(), transition));
    }
    
    /**
     * Transition to the next state. Any code that needs to be executed after the transition 
     * has finished should be set with getNextTransition().setOnFinished(...).
     */
    public void toNextState() {
        toState(getNextTransition());
    }
    
    /**
     * Transition to the previous state. Any code that needs to be executed after the transition 
     * has finished should be set with getNextTransition().setOnFinished(...).
     */
    public void toPreviousState() {
        toState(getPreviousTransition());
    }
    
    private void toState(Transition transition) {
        executeOnCorrectThread(() -> {
            setFadeTransitionFxNodesToVisible(transition);
            transition.play();
        });
    }
    
    /**
     * Execute when a transition has finished. It also enables or disables the toolbar buttons 
     * based on the current playback state and transitions to the next state if the playback state
     * is continuous (and a next state exists).
     * @param forward <tt>true</tt> if we are/were going forward; <tt>false</tt> if backward.
     */
    public void transitionFinished(boolean forward) {
        
        // State index and number.
        if (forward) {
            incrementCurrentStateIndex();
        } else {
            decrementCurrentStateIndex();
        }

        // Add log.
        Log.add("State " + getCurrentStateNumber() + " reached.");
        
        // Toolbar buttons.
        getPlaybackState().determineButtonOperation(hasPreviousState(), hasNextState());
        
        // State info.
        updateStateNumberInfo();

        // Next state if wanted.
        if (getPlaybackState().isContinuous() &&  forward && hasNextState()) {
            ToolbarButton.PLAY.action();
        } else
        if (getPlaybackState().isContinuous() && !forward && hasPreviousState()) {
            ToolbarButton.PLAY_BACK.action();
        } else {
            // There is no next state available. Pause!
            setPlaybackState(new PausedState());
            getPlaybackState().determineButtonOperation(hasPreviousState(), hasNextState());
        }
    }
    
    /**
     * Update the state number in the toolbar.
     */
    public void updateStateNumberInfo() {
        if (getStage() == null) {
            return;
        }
        Text stateInfoNode = (Text) getStage().getScene().lookup("#stateInfo");

        if (stateInfoNode == null) {
            return;
        }
        executeOnCorrectThread(() -> {
            stateInfoNode.setText("Current state number: " + getCurrentStateNumber() 
                    + " out of " + getStateCount());
        });
    }
    
    /**
     * Update the playback state information in the toolbar.
     */
    public void updatePlaybackStateInfo() {
        if (getStage() == null) {
            return;
        }
        Text playbackInfo = (Text) getStage().getScene().lookup("#playbackInfo");
        
        if (playbackInfo == null) {
            return;
        }
        executeOnCorrectThread(() -> {
            playbackInfo.setText(getPlaybackState().toString());
        });
    }
    
    /**
     * Set the JavaFX nodes that are in a <tt>FadeTransition</tt> to visible. It recursively 
     * searches for any <tt>FadeTransition</tt>s.
     * @param transition Any kind of <tt>Transition</tt>.
     */
    //@ requires transition != null;
    private void setFadeTransitionFxNodesToVisible(Transition transition) {
        ObservableList<Animation> childTransitions;
        if (transition instanceof SequentialTransition) {
            childTransitions = ((SequentialTransition) transition).getChildren();
        } else
        if (transition instanceof ParallelTransition) {
            childTransitions = ((ParallelTransition) transition).getChildren();
        } else
        if (transition instanceof FadeTransition) {
            ((FadeTransition) transition).getNode().setVisible(true);
            return;
        } else {
            return;
        }
        for (Animation anim : childTransitions) {
            setFadeTransitionFxNodesToVisible((Transition) anim);
        }
    }
    
    /**
     * Execute the placing of Node A onto Node B according to the settings of a Relation.
     * @param relation The Relation.
     * @return         The animation that executes the placement.
     */
    public void doPlacement(Relation relation) {
        // If no placement is set, do nothing.
        if (relation.getPlacement() == Placement.NONE) {
            return;
        }
        
        // Shorthands.
        final FxContainer nodeAfxCont = relation.getNodeA().getFxContainer();
        final FxContainer nodeBfxCont = relation.getNodeB().getFxContainer();
        
        // Get the duration of the animation.
        final Duration duration = Duration.millis(getCurrentAnimationDuration());
    
        // Calculate the middle point (the new location) and adjust for rotation.
        Point3D tempNewMiddlePoint = nodeBfxCont.calculatePoint(relation.getPlacement());
        if (nodeBfxCont.getRotate() > 0 && relation.getPlacement() != Placement.MIDDLE) {
            tempNewMiddlePoint = nodeBfxCont.getPointAdjustedForRotation(tempNewMiddlePoint);
        }
        final Point3D newMiddlePoint = tempNewMiddlePoint;
        
        /**
         * The conditionals:
         */
        // Only move if node A is visible and the new location is different from the old.
        final boolean doMove = !nodeAfxCont.isPositionSet() 
                || !nodeAfxCont.calculatePoint(Placement.MIDDLE).equals(newMiddlePoint);
        final boolean doRotate = nodeBfxCont.getRotate() != nodeAfxCont.getRotate();
        // Animate if node A is already visible.
        final boolean animateMovement = nodeAfxCont.isPositionSet();
        
        
        // If nothing has to happen, do nothing.
        if (!doMove && !doRotate) {
            return;
        }
        
        // If the node was already visible, animate it.
        if (animateMovement) {
            
            // Create the animation and add it to the returned collection.
            addToVisualizationsQueue(nodeAfxCont.animateToMiddlePoint(
                                                                newMiddlePoint, 
                                                                duration));
            
         
        // If it wasn't visible yet, make it appear at the correct location.
        } else {
            executeOnCorrectThread(() -> {
                // Set the FX node to correct position.
                nodeAfxCont.setFxToPositionWithMiddlePoint(newMiddlePoint);
    
                // Make sure its opacity is set to zero.
                nodeAfxCont.getFxNode().setOpacity(0);
            });
            // Add appearing animation.
            addToVisualizationsQueue(nodeAfxCont.animateAppearing(duration));
        }
        
        // And set the position of the node (in the model) to the new position.
        nodeAfxCont.setToPositionWithMiddlePoint(newMiddlePoint);

        if (doRotate) {
            addToVisualizationsQueue(nodeAfxCont.animateRotate(nodeBfxCont.getRotate(), duration));
        }

        // Add a log entry.
        Log.add("Placement of node " + relation.getNodeA().getId() + " changed to " 
                + relation.getPlacement().toData() + " on node " 
                + relation.getNodeB().getId());
        
        // Do the same with all nodes that are rigidly connected to Node A.
        for (Relation rigidRelation : relation.getNodeA().getRelations(-1).withIsRigid(true)) {
            doPlacement(rigidRelation);
        }
    }
    
    public void changeFx(Node node, Map<String, Object> newFxMap) {

        // Get the FxContainer.
        FxContainer fxContainer = node.getFxContainer();
        Duration duration = Duration.millis(getCurrentAnimationDuration());
        
        // Clone it so we can compare old and new values.
        FxContainer newFx = fxContainer.clone();
        newFx.setFromMap(newFxMap);

        // If the FX node hasn't been shown yet, set the values
        if (!fxContainer.isPositionSet()) {
            fxContainer.setFromMap(newFxMap);
            // Execute this on FX thread.
            executeOnCorrectThread(() -> {
                newFxMap.put("opacity", 0);
                fxContainer.setFxNodeValuesFromMap(newFxMap);
            });
            
            // If the FX node will be shown, make it 'appear'.
            if (newFx.isPositionSet()) {
                addToVisualizationsQueue(fxContainer.animateAppearing(duration));
            }
            
        // If it is already showing, animate the changes.
        } else {
            addToVisualizationsQueue(fxContainer.animateFromMap(newFxMap, duration));
            fxContainer.setFromMap(newFxMap);
        }
        
        // Possibly also re-set the placement of rigidly connected nodes.
        for (Relation relation : node.getRelations(-1).withIsRigid(true)) {
            doPlacement(relation);
        }
    }
    
    
    /**
     * Execute code for the visualizer on the correct thread.
     * @param code The <tt>Runnable</tt> code to be executed.
     */
    //@ requires code != null;
    public void executeOnCorrectThread(Runnable code) {
        try {
            if (Platform.isFxApplicationThread()) {
                code.run();
            } else {
                Platform.runLater(code);
            }
        } catch (IllegalStateException e) {
            //TODO: do something with this.
        }
    }

    /**
     * Start the log window, parse the arguments and if the arguments are valid, start
     * listening for connections.
     */
    @Override
    public void start(Stage primaryStage) {
        final String[] args = getParameters().getRaw().toArray(new String[]{});

        // Open the log window.
        Log.addOutput(new WindowLogger());
        Log.addOutput(Log.DEFAULT);
        
        // Start controller.
        this.controller = new ServerController(this);
        getController().setCommunicationFormat(CommunicationFormat.JSON);
        

        // Process the command line startup.
        boolean successfulStartup = getController().processCommandLine(args);
        
        if (!successfulStartup) {
            // Listen for connections.
            getController().listenForConnections();
        } else {
            // Exit.
            getController().closeStreams();
        }
        
    }
    
    /**
     * Reset the visualizer as a preparation for a new connection.
     */
    /*@ ensures getStage() == null && getNodes().size() == 0 && getStates().size() == 0;
      @ ensures getCurrentStateIndex() == 0 && !hasNextState() && !hasPreviousState();
      @ ensures getVisualizationsQueue() != null;
      @ ensures getVisualizationsQueue().getChildren().size() == 1; 
      @ ensures getVisualizationsQueue().getChildren().get(0) instanceof ParallelTransition; */
    public void reset() {
        setStage(null);
        getController().getNodes().clear();
        currentStateIndex = 0;
        if (hasNextState() && getNextTransition() != null) {
            getNextTransition().stop();
        }
        if (hasPreviousState() && getPreviousTransition() != null) {
            getPreviousTransition().stop();
        }
        getStates().clear();
        resetVisualizationQueue();
        setPlaybackState(new PausedState());
        
        getController().relistenForConnections();
    }
    
   /**
    * Reset the visualization queue.
    */
   //@ ensures getVisualizationsQueue() != null;
   //@ ensures getVisualizationsQueue().getChildren().size() == 1; 
   //@ ensures getVisualizationsQueue().getChildren().get(0) instanceof ParallelTransition;
   public void resetVisualizationQueue() {
       visualizationsQueue = new SequentialTransition();
       visualizationsQueue.getChildren().add(new ParallelTransition());
   }
    
    public static void main(String[] args) {
        launch(args);
    }
    
    
    /**
     * A (recursive) debug method for checking which transitions are inside transitions.
     * @param transitions The main transition. Probably a sequential or parallel one.
     * @return            A <tt>Map</tt> if it's a <tt>SequentialTransition</tt> of 
     *                    <tt>ParallelTransition</tt>; a <tt>String</tt> if it's any other
     *                    (standalone) transition.
     */
    public static Object listTransitions(Transition transitions) {
        Map<String, Object> map = new HashMap<>();
        List<Object> subTransitions = new LinkedList<>();
        if (transitions instanceof SequentialTransition) {
            for (Animation transition : ((SequentialTransition) transitions).getChildren()) {
                subTransitions.add(listTransitions((Transition) transition));
            }
        } else if (transitions instanceof ParallelTransition) {
            for (Animation transition : ((ParallelTransition) transitions).getChildren()) {
                subTransitions.add(listTransitions((Transition) transition));
            }
        } else {
            return transitions.getClass().getSimpleName();
        }
        map.put(transitions.getClass().getSimpleName(), subTransitions);
        return map;
    }
    
    
    

}