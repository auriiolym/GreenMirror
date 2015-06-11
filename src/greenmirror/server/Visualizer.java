package greenmirror.server;

import greenmirror.CommunicationFormat;
import greenmirror.FxWrapper;
import greenmirror.FxWrapper.FadeTransition;
import greenmirror.Log;
import greenmirror.Node;
import greenmirror.Placement;
import greenmirror.Relation;
import greenmirror.WindowLogger;
import greenmirror.placements.CustomPlacement;
import greenmirror.placements.RandomPlacement;
import greenmirror.server.VisualizerMemento.Caretaker;
import greenmirror.server.VisualizerMemento.Originator;
import greenmirror.server.playbackstates.PausedState;

import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import javafx.animation.Animation;
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
 * Memento design pattern: https://sourcemaking.com/design_patterns/memento
 * Originator role: toState(Transition), saveState(SequentialTransition)
 * Caretaker role: (addMemento(Memento) ->) saveState(SequentialTransition), getPreviousState(), 
 *                  getNextState()
 * 
 * @author Karim El Assal
 */
public class Visualizer extends Application implements Caretaker, Originator {
    
    // -- Inner classes ----------------------------------------------------------------------
    
    /**
     * An abstract state class in accordance with the state design pattern.
     * 
     * @author Karim El Assal
     */
    public interface PlaybackState {
        
        /**
         * The method that determines the toolbar button operation in accordance with 
         * <code>hasPreviousState</code> and <code>hasNextState</code>.
         * @param hasPreviousMemento
         * @param hasNextMemento
         */
        public void determineButtonOperation(boolean hasPreviousMemento, boolean hasNextMemento);
        
        /**
         * @return Whether this <code>PlaybackState</code> is a continuous one.
         */
        public default boolean isContinuous() {
            return false;
        }
        
        /**
         * @return A simple explanation of this state.
         */
        @Override
        public String toString();
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
     * The <code>Stage</code> of the visualizer.
     */
    private Stage stage;
    
    /**
     * The default duration of animations. -1 for unspecified duration.
     */
    //@ private invariant defaultAnimationDuration >= -1.0;
    private double defaultAnimationDuration = DEFAULT_ANIMATION_DURATION;
    
    
    private double currentAnimationDuration = -1.0;
    
    private double currentTransitionDelay = DEFAULT_TRANSITION_DELAY;
    
    private boolean rotateRigidlyRelatedNodesRigidly = true;
    
    /**
     * The current queue of visualizations.
     */
    //@ private invariant visualizationsQueue != null;
    private SequentialTransition visualizationsQueue;
    
    //@ private invariant savedMementos != null;
    private LinkedList<VisualizerMemento> savedMementos = new LinkedList<>();
    
    //@ private invariant currentMementoIndex >= 0;
    private int currentMementoIndex = 0;

    
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
     * @return The <code>Stage</code> of the visualizer.
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
     * @return The rotateRigidlyRelatedNodesRigidly.
     */
    public boolean isRotateRigidlyRelatedNodesRigidly() {
        return rotateRigidlyRelatedNodesRigidly;
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
     * @return All savedMementos of the visualizer.
     */
    //@ ensures \result != null;
    /*@ pure */ private List<VisualizerMemento> getMementos() {
        return this.savedMementos;
    }

    @Override
    /*@ pure */ public VisualizerMemento getMemento(int index) {
        return getMementos().get(index);
    }
    
    /**
     * @return The amount of savedMementos currently stored.
     */
    //@ ensures \result >= 0;
    /*@ pure */ public int getMementoCount() {
        return getMementos().size();
    }
    
    //@ ensures \result >= 0;
    /*@ pure */ public int getCurrentMementoIndex() {
        return this.currentMementoIndex;
    }
    
    /*@ pure */ public int getCurrentMementoNumber() {
        return getCurrentMementoIndex();
    }
    
    /*@ pure */ public boolean hasNextMemento() {
        return getCurrentMementoNumber() < getMementoCount();
    }
    
    /*@ pure */ public boolean hasPreviousMemento() {
        return getCurrentMementoNumber() > 1;
    }
    
    /**
     * @return The <code>Transition</code> that transitions to the next state.
     */
    //@ requires hasNextMemento();
    /*@ pure */ public VisualizerMemento getNextMemento() {
        return getMementos().get(getCurrentMementoIndex());
    }
    
    /**
     * @return The <code>Transition</code> that transitions to the previous state.
     */
    //@ requires hasPreviousMemento();
    /*@ pure */ public VisualizerMemento getPreviousMemento() {
        return getMementos().get(getCurrentMementoIndex() - 1);
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
     * @param stage The <code>Stage</code> of the visualizer to set.
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
     * @param rotateRigidlyRelatedNodesRigidly The rotateRigidlyRelatedNodesRigidly to set.
     */
    public void setRotateRigidlyRelatedNodesRigidly(
            boolean rotateRigidlyRelatedNodesRigidly) {
        this.rotateRigidlyRelatedNodesRigidly = rotateRigidlyRelatedNodesRigidly;
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
    public void incrementCurrentMementoIndex() {
        currentMementoIndex++;
    }
    
    //@ ensures \old(getCurrentStateIndex()) - 1 = getCurrentStateIndex();
    public void decrementCurrentMementoIndex() {
        currentMementoIndex--;
    }

    
    // -- Commands ---------------------------------------------------------------------------
    
    @Override
    public void addMemento(VisualizerMemento memento) {
        getMementos().add(memento);
    }
    
    /**
     * Save the current state with the passed <code>transition</code> that holds the animations
     * to go to the next state.
     * @param transitions
     * @return TODO
     */
    @Override
    public VisualizerMemento saveToMemento(SequentialTransition transition) {
        return new VisualizerMemento(getController().getNodes(), transition);
    }
    
    
    /**
     * Transition to the next state. Any code that needs to be executed after the transition 
     * has finished should be set with getNextMemento().getTransition().setOnFinished(...).
     */
    public void toNextMemento() {
        restoreFromMemento(getNextMemento());
    }
    
    /**
     * Transition to the previous state. Any code that needs to be executed after the transition 
     * has finished should be set with getPreviousMemento().getTransition().setOnFinished(...).
     */
    public void toPreviousMemento() {
        restoreFromMemento(getPreviousMemento());
    }

    @Override
    public void restoreFromMemento(VisualizerMemento memento) {
        executeOnCorrectThread(() -> {
            setFxNodeVisibility(memento.getTransition(), true);
            memento.getTransition().play();
        });
    }
    
    /**
     * Execute when a transition has finished. It also enables or disables the toolbar buttons 
     * based on the current playback state and transitions to the next state if the playback state
     * is continuous (and a next state exists).
     * @param transition   The <code>Transition</code> that just finished.
     * @param goingForward <code>true</code> if we are/were going forward; <code>false</code> if backward.
     */
    public void transitionFinished(Transition transition, boolean goingForward) {
        
        // Update FX node visibility.
        setFxNodeVisibility(transition, false);
        
        // State index and number.
        if (goingForward) {
            incrementCurrentMementoIndex();
        } else {
            decrementCurrentMementoIndex();
        }

        // Add log.
        Log.add("State " + getCurrentMementoNumber() + " reached.");
        
        // Toolbar buttons.
        getPlaybackState().determineButtonOperation(hasPreviousMemento(), hasNextMemento());
        
        // State info.
        updateMementoNumberInfo();

        // Next state if wanted.
        if (getPlaybackState().isContinuous() &&  goingForward && hasNextMemento()) {
            ToolbarButton.PLAY.action();
        } else
        if (getPlaybackState().isContinuous() && !goingForward && hasPreviousMemento()) {
            ToolbarButton.PLAY_BACK.action();
        } else {
            // There is no next state available. Pause!
            setPlaybackState(new PausedState());
            getPlaybackState().determineButtonOperation(hasPreviousMemento(), hasNextMemento());
        }
    }
    
    /**
     * Update the memento number in the toolbar.
     */
    public void updateMementoNumberInfo() {
        if (getStage() == null) {
            return;
        }
        Text mementoInfoNode = (Text) getStage().getScene().lookup("#stateInfo");

        if (mementoInfoNode == null) {
            return;
        }
        executeOnCorrectThread(() -> {
            mementoInfoNode.setText("Current state number: " + getCurrentMementoNumber() 
                    + " out of " + getMementoCount());
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
     * Set the JavaFX nodes that will appear or disappear to (respectively) visible or invisible. 
     * It recursively searches for any <code>FadeTransition</code>s. If <code>isStarting</code> 
     * is set to true, we assume this method is executed right before the start of an animation. 
     * If set to false, we assume this method is executed right after the and of an amination.
     * @param transition Any kind of <code>Transition</code>.
     * @param isStarting <code>true</code> if we're starting an animation; <code>false</code> 
     *                   if an animation has just ended. 
     */
    //@ requires transition != null;
    private void setFxNodeVisibility(Transition transition, boolean isStarting) {
        setFxNodeVisibilityRecursively(transition, isStarting, transition.getRate());
    }

    /**
     * The actual recursive method of {@link #setFxNodeVisibility(Transition, boolean)}. This
     * method takes an extra parameter: the rate of the animation which is only set at the root
     * animation. This is done because when the <code>FadeTransition</code> is found, the direction
     * of the animation is determined via the rate of the root animation.
     * @param transition Any kind of <code>Transition</code>.
     * @param isStarting <code>true</code> if we're starting an animation; <code>false</code> 
     *                   if an animation has just ended.
     * @param rate       The rate with which the animation will progress.
     */
    //@ requires transition != null;
    private void setFxNodeVisibilityRecursively(Transition transition, boolean isStarting, 
            double rate) {
        
        ObservableList<Animation> childTransitions;
        if (transition instanceof SequentialTransition) {
            childTransitions = ((SequentialTransition) transition).getChildren();
        } else
        if (transition instanceof ParallelTransition) {
            childTransitions = ((ParallelTransition) transition).getChildren();
        } else
        if (transition instanceof FadeTransition) {
            final FadeTransition ft = (FadeTransition) transition;
            final Double fr = ft.getFromValue();
            final Double to = ft.getToValue();
            
            /**
             * Explanation of the logic below:
             * The rate determines if we have to see the 'from' and 'to' values actually as the 
             * 'from' and 'to' values. When the rate is negative, the 'from' and 'to' values stay 
             * the same, so we need to take this into account.
             * The null value of the 'from' value is a possibility because the animation can be
             * created with only a 'to' value. After playing the animation, the 'from' value is
             * automatically filled in. 
             */
            if (isStarting  && (rate > 0 && (fr == null || fr == 0) && to > 0 
                             || rate < 0 &&  fr != null && fr > 0 && to == 0)) {
                ft.getNode().setVisible(true);
            } else
            if (!isStarting && (rate > 0 &&   fr != null && fr  > 0  && to == 0
                             || rate < 0 &&  (fr == null || fr == 0) && to  > 0)) {
                ft.getNode().setVisible(false);
            }
            return;
        } else {
            return;
        }
        for (Animation anim : childTransitions) {
            setFxNodeVisibilityRecursively((Transition) anim, isStarting, rate);
        }
    }
    
    /**
     * Execute the placing of Node A onto Node B according to the settings of a Relation.
     * @param relation            The Relation.=
     * @return                    The animation that executes the placement.
     */
    public void doPlacement(Relation relation) {
        
        // If no placement is set (or node B hasn't even got an FxWrapper), do nothing.
        if (relation.getPlacement().equals(Placement.NONE) 
                || relation.getNodeB().getFxWrapper() == null) {
            return;
        }
        
        // Shorthands.
        final FxWrapper nodeAFxWrapper = relation.getNodeA().getFxWrapper();
        final FxWrapper nodeBFxWrapper = relation.getNodeB().getFxWrapper();
        
        
        // Get the duration of the animation.
        final Duration duration = Duration.millis(getCurrentAnimationDuration());
    
        // Calculate the middle point (the new location) and adjust for rotation.
        Point3D tempNewMiddlePoint = nodeBFxWrapper.calculatePoint(relation.getPlacement());
        if (relation.getPlacement() instanceof RandomPlacement) {
            final Point3D relativeToNodeB = tempNewMiddlePoint
                    .subtract(nodeBFxWrapper.calculatePoint(Placement.MIDDLE))
                    .add(relation.getPlacement().getRelativePosition());
            relation.setPlacement(new CustomPlacement().withRelativePosition(relativeToNodeB));
        }
        if (nodeBFxWrapper.getRotate() != 0 && !relation.getPlacement().equals(Placement.MIDDLE)) {
            tempNewMiddlePoint = nodeBFxWrapper.getPointAdjustedForRotation(tempNewMiddlePoint);
        }
        final Point3D newMiddlePoint = tempNewMiddlePoint;
        
        /**
         * The conditionals:
         */
        // Only move if node A is visible and the new location is different from the old.
        final boolean doMove = !nodeAFxWrapper.isPositionSet() 
                || !nodeAFxWrapper.calculatePoint(Placement.MIDDLE).equals(newMiddlePoint);
        final boolean doRotate = nodeBFxWrapper.getRotate() != nodeAFxWrapper.getRotate() 
                && isRotateRigidlyRelatedNodesRigidly();
        // Animate if node A is already visible.
        final boolean animateMovement = nodeAFxWrapper.isPositionSet();
        
        
        // If nothing has to happen, do nothing.
        if (!doMove && !animateMovement && !doRotate) {
            return;
        }
        
        // If the node was already visible, animate it.
        if (animateMovement) {
            
            // Create the animation and add it to the returned collection.
            addToVisualizationsQueue(nodeAFxWrapper.animateToMiddlePoint(newMiddlePoint, duration));
            
         
        // If it wasn't visible yet, make it appear at the correct location.
        } else {
            executeOnCorrectThread(() -> {
                // Set the FX node to correct position.
                nodeAFxWrapper.setFxToPositionWithMiddlePoint(newMiddlePoint);
    
                // Make sure its opacity is set to zero.
                nodeAFxWrapper.getFxNode().setOpacity(0);
            });
            // Add appearing animation.
            addToVisualizationsQueue(
                    nodeAFxWrapper.animateOpacity(0.0, nodeAFxWrapper.getOpacity(), duration));
        }
        
        // And set the position of the node (in the model) to the new position.
        nodeAFxWrapper.setToPositionWithMiddlePoint(newMiddlePoint);

        if (doRotate) {
            final double rotateTo = nodeBFxWrapper.getRotate();
            addToVisualizationsQueue(nodeAFxWrapper.animateRotate(rotateTo, duration));
            nodeAFxWrapper.setRotate(rotateTo);
        }

        // Add a log entry.
        Log.add("Placement of node " + Log.n(relation.getNodeA()) + " changed to " 
                + relation.getPlacement().toData() + " on node " 
                + Log.n(relation.getNodeB()));
        
        // Do the same with all nodes that are rigidly connected to Node A.
        for (Relation rigidRelation : relation.getNodeA().getRelations(-1).withIsRigid(true)) {
            doPlacement(rigidRelation);
        }
    }
    
    public void changeFx(Node node, Map<String, Object> newFxMap) {

        // Get the FxWrapper.
        FxWrapper fxWrapper = node.getFxWrapper();
        Duration duration = Duration.millis(getCurrentAnimationDuration());
        
        // Clone it so we can compare old and new values.
        FxWrapper newFx = fxWrapper.clone();
        newFx.setFromMap(newFxMap);


        // If the FX node hasn't been shown yet, set the values
        if (!fxWrapper.isPositionSet()) {
            fxWrapper.setFromMap(newFxMap);
            // Execute this on FX thread.
            executeOnCorrectThread(() -> {
                newFxMap.put("opacity", 0);
                fxWrapper.setFxNodeValuesFromMap(newFxMap);
            });
            
            // If the FX node will be shown, make it 'appear'.
            if (newFx.isPositionSet()) {
                addToVisualizationsQueue(
                        fxWrapper.animateOpacity(0.0, fxWrapper.getOpacity(), duration));
            }
            
        // If it is already showing, animate the changes.
        } else {
            addToVisualizationsQueue(fxWrapper.animateFromMap(newFxMap, duration));
            fxWrapper.setFromMap(newFxMap);
        }
        
        // Possibly also re-set the placement of rigidly connected nodes.
        for (Relation relation : node.getRelations(-1).withIsRigid(true)) {
            doPlacement(relation);
        }
    }
    
    
    /**
     * Execute code for the visualizer on the correct thread.
     * @param code The <code>Runnable</code> code to be executed.
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

        
        if (successfulStartup && getController().getPort() != null) {
            getController().listenForConnections();
        }
        
    }
    
    /**
     * Reset the visualizer as a preparation for a new connection.
     */
    /*@ ensures getStage() == null && getNodes().size() == 0 && getStates().size() == 0;
      @ ensures getCurrentStateIndex() == 0 && !hasNextState() && !hasPreviousState();
      @ ensures getVisualizationsQueue() != null;
      @ ensures getVisualizationsQueue().getChildren().size() == 1; 
      @ ensures getVisualizationsQueue().getChildren().get(0) instanceof ParallelTransition;
      @ ensures getDefaultAnimationDuration() == DEFAULT_ANIMATION_DURATION;
      @ ensures getCurrentAnimationDuration() == getDefaultAnimationDuration(); */
    public void reset() {
        setStage(null);
        getController().getNodes().clear();
        if (hasNextMemento() && getNextMemento() != null) {
            getNextMemento().getTransition().stop();
        }
        if (hasPreviousMemento() && getPreviousMemento() != null) {
            getPreviousMemento().getTransition().stop();
        }
        resetSavedMementos();
        resetVisualizationQueue();
        setPlaybackState(new PausedState());
        setDefaultAnimationDuration(DEFAULT_ANIMATION_DURATION);
        setCurrentAnimationDuration(-1.0);
        
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

   @Override
   public void resetSavedMementos() {
       currentMementoIndex = 0;
       getMementos().clear();
   }
    
    public static void main(String[] args) {
        launch(args);
    }
    
    
    /**
     * A (recursive) debug method for checking which transitions are inside transitions.
     * @param transitions The main transition. Probably a sequential or parallel one.
     * @return            A <code>Map</code> if it's a <code>SequentialTransition</code> of 
     *                    <code>ParallelTransition</code>; a <code>String</code> if it's any other
     *                    (standalone) transition.
     */
    public static Object listTransitions(Transition transitions) {
        Map<String, Object> map = new LinkedHashMap<>();
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