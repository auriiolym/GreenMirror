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
import greenmirror.server.playbackstates.PausedState;
import greenmirror.server.VisualizerMemento.Caretaker;
import greenmirror.server.VisualizerMemento.Originator;
import org.eclipse.jdt.annotation.NonNull;

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
import javafx.event.EventHandler;
import javafx.geometry.Point3D;
import javafx.scene.layout.Pane;
import javafx.scene.text.Text;
import javafx.stage.Stage;
import javafx.stage.WindowEvent;
import javafx.util.Duration;

/**
 * The main visualizer class and JavaFX application. It starts the log window and waits for 
 * connections.
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
         * 
         * @param hasPreviousMemento whether the visualizer has a previous memento
         * @param hasNextMemento     whether the visualizer has a next memento
         */
        public void determineButtonOperation(boolean hasPreviousMemento, boolean hasNextMemento);
        
        /** @return whether this <code>PlaybackState</code> is a continuous one */
        public default boolean isContinuous() {
            return false;
        }
        
        /** @return a simple explanation of this state, used in the visualizer to indicate 
         *          which playback state is currently active */
        @Override @NonNull
        public String toString();
    }
    
    
    // -- Constants --------------------------------------------------------------------------
    
    /** The default animation duration, chosen if no other duration is set. */ 
    private static final double DEFAULT_ANIMATION_DURATION = 1000.0;
    
    /** The default delay between state-transitions when a continuous playback state is active. */
    private static final double DEFAULT_TRANSITION_DELAY = 300.0;
    
    
    // -- Class variables --------------------------------------------------------------------

    // -- Instance variables -----------------------------------------------------------------

    /** The controller. */
    private ServerController controller;
    
    /** The current playback state of the visualizer. */
    @NonNull private PlaybackState currentPlaybackState = new PausedState();
    
    /** The <code>Stage</code> of the visualizer. */
    private Stage stage;
    
    /** The default duration of animations.
     *  @see greenmirror.commands.SetAnimationDurationCommand */
    //@ private invariant defaultAnimationDuration >= -1.0;
    private double defaultAnimationDuration = DEFAULT_ANIMATION_DURATION;
    
    /** The chosen duration of animations.
     *  @see greenmirror.commands.SetAnimationDurationCommand */
    private double currentAnimationDuration = -1.0;
    
    /** The chosen delay between state-transitions when a continuous playback state is active. */
    private double currentTransitionDelay = DEFAULT_TRANSITION_DELAY;
    
    /** @see greenmirror.commands.InitializationCommand */
    private boolean rotateRigidlyRelatedNodesRigidly = true;
    
    /** The current queue of visualizations. */
    @NonNull private SequentialTransition visualizationsQueue = new SequentialTransition();
    
    /** The currently saved mementos (model states). */
    @NonNull private LinkedList<VisualizerMemento> savedMementos = new LinkedList<>();
    
    /** The current memento (model state). */
    //@ private invariant currentMementoIndex >= 0;
    private int currentMementoIndex = 0;

    
    // -- Constructors -----------------------------------------------------------------------
    
    /**
     * Creates a new instance and resets the visualizations queue.
     */
    public Visualizer() {
        super();
        resetVisualizationQueue();
    }

    // -- Queries ----------------------------------------------------------------------------

    /** @return the controller */
    /*@ pure */ public ServerController getController() {
        return controller;
    }
    
    /** @return the current playback state of the visualizer */
    /*@ pure */ @NonNull public PlaybackState getPlaybackState() {
        return currentPlaybackState;
    }

    /** @return the <code>Stage</code> of the visualizer */
    /*@ pure */ public Stage getStage() {
        return stage;
    }
    
    /**
     * @return the pane containing all visualization elements of the visualizer
     * @throws IllegalStateException if the FX node pane wasn't found
     */
    //@ requires getStage() != null;
    /*@ pure */ public Pane getFxNodePane() {
        final Pane container = (Pane) getStage().getScene().lookup("#FxNodePane");
        if (container == null) {
            throw new IllegalStateException("the stage hasn't been set up properly (yet)");
        }
        return container;
    }
    
    /** 
     * @return the default animation duration
     * @see    greenmirror.commands.SetAnimationDurationCommand 
     */
    //@ ensures \result >= -1.0;
    /*@ pure */ public double getDefaultAnimationDuration() {
        return this.defaultAnimationDuration;
    }
    
    /**
     * @return the currently set animation duration or, if not set, the default animation duration
     * @see    greenmirror.commands.SetAnimationDurationCommand
     */
    //@ ensures \result >= 0;
    /*@ pure */ public double getCurrentAnimationDuration() {
        return this.currentAnimationDuration >= 0
                ? this.currentAnimationDuration : getDefaultAnimationDuration();
    }
    
    /** @return the currently set delay between transitions or if not set, the default value */
    //@ ensures \result >= 0;
    /*@ pure */ public double getCurrentTransitionDelay() {
        return this.currentTransitionDelay >= 0
                ? this.currentTransitionDelay : DEFAULT_TRANSITION_DELAY;
    }

    /**
     * @return the rotateRigidlyRelatedNodesRigidly setting
     * @see    greenmirror.commands.InitializationCommand
     */
    public boolean isRotateRigidlyRelatedNodesRigidly() {
        return this.rotateRigidlyRelatedNodesRigidly;
    }

    /** @return the visualizations queue */
    /*@ pure */ @NonNull public SequentialTransition getVisualizationsQueue() {
        return this.visualizationsQueue;
    }
    
    /**
     * @return the current parallel 'sub'-queue of visualizations
     * @throws IllegalStateException if the structure of the queue is wrong
     */
    //@ requires getVisualizationsQueue().getChildren().size() > 0;
    /*@ pure */ @NonNull private ParallelTransition getCurrentSubVisualizationQueue() {
        final ObservableList<Animation> root = getVisualizationsQueue().getChildren();
        final Animation last;
        if (root.size() == 0 || (last = root.get(root.size() - 1)) == null) {
            throw new IllegalStateException("visualizations queue structure error");
        }
        return (ParallelTransition) last;
    }
    
    /** @return all saved mementos of the visualizer */
    /*@ pure */ @NonNull private List<VisualizerMemento> getMementos() {
        return this.savedMementos;
    }

    @Override
    /*@ pure */ public VisualizerMemento getMemento(int index) {
        if (index < 0 || index >= getMementos().size()) {
            return null;
        } else {
            return getMementos().get(index);
        }
    }
    
    /** @return the amount of saved mementos currently stored */
    //@ ensures \result >= 0;
    /*@ pure */ public int getMementoCount() {
        return getMementos().size();
    }
    
    /**
     * Returns the index of the current memento. Mementos store the transition data to transition
     * to the next memento. This means that if we're at the final state (memento), there is no
     * saved memento, only a previous one.
     *  
     * @return the current memento index(/number)
     */
    //@ ensures \result >= 0;
    /*@ pure */ public int getCurrentMementoIndex() {
        return this.currentMementoIndex;
    }
    
    /** @return whether there exists a next memento */
    /*@ pure */ public boolean hasNextMemento() {
        return getCurrentMementoIndex() < getMementoCount();
    }
    
    /** @return whether there exists a previous memento */
    /*@ pure */ public boolean hasPreviousMemento() {
        return getCurrentMementoIndex() > 1;
    }
    
    /** 
     * @return the current memento that has the transition data to transition to the next memento
     * @throws IllegalStateException if there is no current memento 
     */
    //@ requires hasNextMemento();
    /*@ pure */ @NonNull public VisualizerMemento getNextMemento() {
        try {
            final VisualizerMemento mem = getMementos().get(getCurrentMementoIndex());
            if (mem == null) {
                throw new IndexOutOfBoundsException();
            }
            return mem;
        } catch (IndexOutOfBoundsException e) {
            throw new IllegalStateException("there is no memento for the current index");
        }
    }
    
    /**
     * @return the previous memento
     * @throws IllegalStateException if there is no previous memento 
     */
    //@ requires hasPreviousMemento();
    /*@ pure */ @NonNull public VisualizerMemento getPreviousMemento() {
        try {
            final VisualizerMemento mem = getMementos().get(getCurrentMementoIndex() - 1);
            if (mem == null) {
                throw new IndexOutOfBoundsException();
            }
            return mem;
        } catch (IndexOutOfBoundsException e) {
            throw new IllegalStateException("there is no memento for the previous index");
        }
    }

    
    
    // -- Setters ----------------------------------------------------------------------------
    
    /** @param playbackState the new current playback state of the visualizer */
    //@ ensures getPlaybackState() == playbackState;
    public void setPlaybackState(@NonNull PlaybackState playbackState) {
        this.currentPlaybackState = playbackState;
        updatePlaybackStateInfo();
    }

    /** @param stage the <code>Stage</code> of the visualizer to set */
    //@ ensures getStage() == stage;
    public void setStage(Stage stage) {
        this.stage = stage;
    }
    
    /** 
     * @param defaultAnimationDuration the defaultAnimationDuration to set
     * @see   greenmirror.commands.SetAnimationDurationCommand
     */
    //@ requires defaultAnimationDuration >= -1.0;
    //@ ensures getDefaultAnimationDuration() == defaultAnimationDuration;
    public void setDefaultAnimationDuration(double defaultAnimationDuration) {
        this.defaultAnimationDuration = defaultAnimationDuration;
    }
    
    /**
     * @param currentAnimationDuration the currentAnimationDuration to set
     * @see   greenmirror.commands.SetAnimationDurationCommand
     */
    //@ requires currentAnimationDuration >= -1.0;
    public void setCurrentAnimationDuration(double currentAnimationDuration) {
        this.currentAnimationDuration = currentAnimationDuration;
    }
    
    /**
     * @param rotateRigidlyRelatedNodesRigidly the rotateRigidlyRelatedNodesRigidly to set
     * @see   greenmirror.commands.InitializationCommand
     */
    public void setRotateRigidlyRelatedNodesRigidly(boolean rotateRigidlyRelatedNodesRigidly) {
        this.rotateRigidlyRelatedNodesRigidly = rotateRigidlyRelatedNodesRigidly;
    }

    /**
     * @param transition the transition to add to the current visualizations sub-queue
     */
    //@ ensures getCurrentSubVisualizationQueue().getChildren().contains(transition);
    public void addToVisualizationsQueue(@NonNull Transition transition) {
        getCurrentSubVisualizationQueue().getChildren().add(transition);
    }
    
    /**
     * Increments the current memento index.
     */
    //@ ensures \old(getCurrentStateIndex()) + 1 = getCurrentStateIndex();
    public void incrementCurrentMementoIndex() {
        currentMementoIndex++;
    }
    
    /**
     * Decrements the current memento index.
     */
    //@ ensures \old(getCurrentStateIndex()) - 1 = getCurrentStateIndex();
    public void decrementCurrentMementoIndex() {
        currentMementoIndex--;
    }

    
    // -- Commands ---------------------------------------------------------------------------
    
    @Override
    public void addMemento(VisualizerMemento memento) {
        getMementos().add(memento);
    }
    
    @Override @NonNull 
    public VisualizerMemento saveToMemento(@NonNull SequentialTransition transition) {
        return new VisualizerMemento(getController().getNodes(), transition);
    }
    
    /**
     * Transitions to the next state. Any code that needs to be executed after the transition 
     * has finished should be set with getNextMemento().getTransition().setOnFinished(...).
     */
    public void toNextMemento() {
        restoreFromMemento(getNextMemento());
    }
    
    /**
     * Transitions to the previous state. Any code that needs to be executed after the transition 
     * has finished should be set with getPreviousMemento().getTransition().setOnFinished(...).
     */
    public void toPreviousMemento() {
        restoreFromMemento(getPreviousMemento());
    }

    @Override
    public void restoreFromMemento(@NonNull VisualizerMemento memento) {
        executeOnCorrectThread(() -> {
            setFxNodeVisibility(memento.getTransition(), true);
            memento.getTransition().play();
        });
    }
    
    /**
     * Executes when a transition has finished. It also enables or disables the toolbar buttons 
     * based on the current playback state and transitions to the next state if the playback state
     * is continuous (and a next state exists).
     * 
     * @param transition   the <code>Transition</code> that just finished
     * @param goingForward <code>true</code> if we are/were going forward; <code>false</code> if 
     *                     backward
     */
    public void transitionFinished(@NonNull Transition transition, boolean goingForward) {
        
        // Update FX node visibility.
        setFxNodeVisibility(transition, false);
        
        // State index and number.
        if (goingForward) {
            incrementCurrentMementoIndex();
        } else {
            decrementCurrentMementoIndex();
        }

        // Add log.
        Log.add("State " + getCurrentMementoIndex() + " reached.");
        
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
            // There is no next state available. Pause.
            setPlaybackState(new PausedState());
            getPlaybackState().determineButtonOperation(hasPreviousMemento(), hasNextMemento());
        }
    }
    
    /**
     * Updates the memento number in the toolbar.
     */
    public void updateMementoNumberInfo() {
        if (getStage() == null) {
            return;
        }
        final Text mementoInfoNode = (Text) getStage().getScene().lookup("#stateInfo");

        if (mementoInfoNode == null) {
            return;
        }
        executeOnCorrectThread(() -> {
            mementoInfoNode.setText("Current state number: " + getCurrentMementoIndex() 
                    + " out of " + getMementoCount());
        });
    }
    
    /**
     * Updates the playback state information in the toolbar.
     */
    public void updatePlaybackStateInfo() {
        if (getStage() == null) {
            return;
        }
        final Text playbackInfo = (Text) getStage().getScene().lookup("#playbackInfo");
        
        if (playbackInfo == null) {
            return;
        }
        executeOnCorrectThread(() -> {
            playbackInfo.setText(getPlaybackState().toString());
        });
    }
    
    /**
     * Sets the JavaFX nodes that will appear or disappear to (respectively) visible or invisible. 
     * It recursively searches for any <code>FadeTransition</code>s. If <code>isStarting</code> 
     * is set to true, we assume this method is executed right before the start of an animation. 
     * If set to false, we assume this method is executed right after the and of an animation.
     * 
     * @param transition any kind of <code>Transition</code>
     * @param isStarting <code>true</code> if we're starting an animation; <code>false</code> 
     *                   if an animation has just ended 
     */
    private void setFxNodeVisibility(@NonNull Transition transition, boolean isStarting) {
        setFxNodeVisibilityRecursively(transition, isStarting, transition.getRate());
    }

    /**
     * The actual recursive method of {@link #setFxNodeVisibility(Transition, boolean)}. This
     * method takes an extra parameter: the rate of the animation which is only set at the root
     * animation. This is done because when the <code>FadeTransition</code> is found, the direction
     * of the animation is determined via the rate of the root animation.
     * 
     * @param transition any kind of <code>Transition</code>
     * @param isStarting <code>true</code> if we're starting an animation; <code>false</code> 
     *                   if an animation has just ended
     * @param rate       the rate with which the animation will progress or has progressed
     */
    private void setFxNodeVisibilityRecursively(@NonNull Transition transition, 
                                                boolean isStarting, double rate) {
        
        final ObservableList<Animation> childTransitions;
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
            if (anim != null) { // @NonNull annotation formality.
                setFxNodeVisibilityRecursively((Transition) anim, isStarting, rate);
            }
        }
    }
    
    /**
     * Executes the placing of node A onto node B according to the settings of a Relation.
     * 
     * @param relation the Relation
     */
    //@ requires relation.getNodeA() != null && relation.getNodeB() != null;
    public void doPlacement(@NonNull Relation relation) {
        
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
        if (duration == null) { // @NonNull annotation formality.
            return;
        }
    
        // Calculate the middle point (the new location) and adjust for rotation.
        Point3D tempNewMiddlePoint = nodeBFxWrapper.calculatePoint(relation.getPlacement());
        if (relation.getPlacement() instanceof RandomPlacement) {
            final Point3D relativeToNodeB = tempNewMiddlePoint
                    .subtract(nodeBFxWrapper.calculatePoint(Placement.MIDDLE))
                    .add(relation.getPlacement().getRelativePosition());
            if (relativeToNodeB == null) { // @NonNull annotation formality.
                return;
            }
            relation.setPlacement(new CustomPlacement().withRelativePosition(relativeToNodeB));
        }
        if (nodeBFxWrapper.getRotate() != 0 && !relation.getPlacement().equals(Placement.MIDDLE)) {
            tempNewMiddlePoint = nodeBFxWrapper.getPointAdjustedForRotation(tempNewMiddlePoint);
        }
        final Point3D newMiddlePoint = tempNewMiddlePoint;
        
        /*
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
            if (rigidRelation != null) { // @NonNull annotation formality.
                doPlacement(rigidRelation);
            }
        }
    }
    
    /**
     * Changes the FX of a node according to a given map of values. <code>null</code> values
     * are ignored. If the node is already shown on the canvas (its position was set), then
     * the changes are animated. If it isn't already shown, the changes are simply set and if
     * it's shown after the new values are set, a fade in is added. Also, the placement is 
     * re-calculated of rigidly related nodes.
     * 
     * @param node     the node that will have its FX changed
     * @param newFxMap the map with new values
     */
    public void changeFx(@NonNull Node node, @NonNull Map<String, Object> newFxMap) {

        // Get the FxWrapper.
        final FxWrapper fxWrapper = node.getFxWrapper();
        final Duration duration = Duration.millis(getCurrentAnimationDuration());
        if (duration == null) { // @NonNull annotation formality.
            return;
        }
        
        // Clone it so we can easily compare old and new values.
        final FxWrapper newFx = fxWrapper.clone();
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
        for (Relation rigidRelation : node.getRelations(-1).withIsRigid(true)) {
            if (rigidRelation != null) { // @NonNull annotation formality.
                doPlacement(rigidRelation);
            }
        }
    }
    
    /**
     * Executes code for the visualizer on the correct thread.
     * 
     * @param code the <code>Runnable</code> code to be executed
     */
    public void executeOnCorrectThread(@NonNull Runnable code) {
        try {
            if (Platform.isFxApplicationThread()) {
                code.run();
            } else {
                Platform.runLater(code);
            }
        } catch (IllegalStateException e) {
            throw new RuntimeException("JavaFX related code was tried to be run, but no "
                    + "application thread was found");
        }
    }

    /**
     * This is the main entry point for the JavaFX application. It starts the log window, 
     * parses the arguments and if the arguments are valid, starts listening for connections.
     * 
     * @param primaryStage the primary stage received from the JavaFX thread
     */
    @Override
    public void start(Stage primaryStage) {
        final String[] args = getParameters().getRaw().toArray(new String[]{});
        
        // Start controller.
        this.controller = new ServerController(this);
        getController().setCommunicationFormat(CommunicationFormat.JSON);
        
        // Open the log window.
        Log.addOutput(new WindowLogger(new EventHandler<WindowEvent>() {
            // On log window close, exit.
            @Override public void handle(WindowEvent a0) {
                getController().exit();
            }
        }));
        Log.addOutput(Log.DEFAULT);

        // Process the command line startup.
        boolean successfulStartup = getController().processCommandLine(args);

        // Start listening for connections if we've initialized correctly.
        if (successfulStartup && getController().getPort() != null) {
            getController().listenForConnections();
        }
        
    }
    
    /**
     * Resets the visualizer as a preparation for a new connection.
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
    }
    
    /**
     * Resets the visualization queue.
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
     
    /**
     * Launches the application with the options passed via the command line.
     *  
     * @param args command line arguments
     */
    public static void main(String[] args) {
        launch(args);
    }
    
    
    /**
     * A (recursive) debug method for checking which transitions are inside sequential 
     * and parallel transitions.
     * 
     * @param transitions the main transition. Probably a sequential or parallel one
     * @return            a <code>Map</code> if it's a <code>SequentialTransition</code> or 
     *                    <code>ParallelTransition</code>; a <code>String</code> if it's any other
     *                    (standalone) transition.
     */
    public static Object listTransitions(Transition transitions) {
        final Map<String, Object> map = new LinkedHashMap<>();
        final List<Object> subTransitions = new LinkedList<>();
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