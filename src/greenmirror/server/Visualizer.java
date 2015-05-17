package greenmirror.server;

import greenmirror.CommunicationFormat;
import greenmirror.FxContainer;
import greenmirror.Log;
import greenmirror.Node;
import greenmirror.Placement;
import greenmirror.Relation;
import greenmirror.commands.AddNodeCommandHandler;
import greenmirror.commands.AddRelationCommandHandler;
import greenmirror.commands.ChangeNodeFxCommandHandler;
import greenmirror.commands.EndTransitionCommandHandler;
import greenmirror.commands.FlushCommandHandler;
import greenmirror.commands.InitializationCommandHandler;
import greenmirror.commands.SetCurrentAnimationDurationCommandHandler;
import greenmirror.commands.SetNodeFxCommandHandler;
import greenmirror.commands.StartVisualizationCommandHandler;
import greenmirror.commands.SwitchRelationCommandHandler;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

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


// Extends javafx.application.Application.
/**
 * The main visualizer class. It starts the log window and waits for connections. 
 * 
 * @author Karim El Assal
 */
public class Visualizer extends Application {
    
    // -- Enumerations -----------------------------------------------------------------------

    public static enum Status {
        PLAYING_REVERSE_ONE_FAST,
        PLAYING_REVERSE_ONE,
        PLAYING_REVERSE,
        PAUSED,
        PLAYING,
        PLAYING_ONE,
        PLAYING_ONE_FAST,
    }
    
    // -- Constants --------------------------------------------------------------------------

    /**
     * The current GreenMirror server application version.
     */
    private static final double VERSION = 1.0;
    
    /**
     * The help message, shown in the log when -help is used as an argument.
     */
    private static final String HELP_MSG = 
          "\nGreenMirror State-Transition Visualization server v" + VERSION + "."
        + "\n"
        + "\nThe following arguments are available:"
        + "\n  -port:<port>        Specifies the port of the server. <port> should be a number."
        + "\n  [-verbose]          Outputs verbose data to the logs. Optional."
        + "\n  [-help]             Display this help message."
        + "\n ";
    
    private static final double DEFAULT_ANIMATION_DURATION = 1000.0;
    
    private static final double DEFAULT_TRANSITION_DELAY = 300.0;
    
    // -- Class variables --------------------------------------------------------------------

    // -- Instance variables -----------------------------------------------------------------

    /**
     * The controller.
     */
    private ServerController controller;
    
    /**
     * The current status of the visualizer.
     */
    private Status currentStatus = Status.PAUSED;
    
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
    //@ ensures currentStatus != null;
    /*@ pure */ public Status getStatus() {
        return currentStatus;
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
     * @param status The new current status of the visualizer.
     */
    //@ requires status != null;
    //@ ensures getStatus() == status;
    public void setStatus(Status status) {
        executeOnCorrectThread(() -> {
            Text statusInfo = (Text) getStage().getScene().lookup("#statusInfo");
            statusInfo.setText(status.toString());
        });
        this.currentStatus = status;
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
     * Execute when a transition has finished. It enabled or disabled the toolbar buttons based
     * on the current visualizer status and transition to the next state if the status isn't
     * paused (and a next state exists).
     * @param forward <tt>true</tt> if we are/were going forward; <tt>false</tt> if backward.
     */
    public void transitionFinished(boolean forward) {
        
        // State index and number.
        if (forward) {
            incrementCurrentStateIndex();
        } else {
            decrementCurrentStateIndex();
        }
        
        // Toolbar buttons.
        ToolbarButton.setAllFromStatus(getStatus());
        
        // State info.
        updateStateInfo();

        // Next state if wanted.
        if (!getStatus().equals(Visualizer.Status.PAUSED)) {
            if (forward && hasNextState()) {
                //toNextState(); 
                //TODO: check if this is the right way.
                ToolbarButton.PLAY.action();
            } else if (!forward && hasPreviousState()) {
                //toPreviousState();
                ToolbarButton.PLAY_REVERSE.action();
            } else {
                // There is no next state available. Pause!
                setStatus(Status.PAUSED);
                ToolbarButton.setAllFromStatus(Status.PAUSED);
            }
        }
    }
    
    /**
     * Update the state number in the toolbar.
     */
    public void updateStateInfo() {
        Text stateInfoNode = (Text) getStage().getScene().lookup("#stateInfo");

        if (stateInfoNode != null) {
            executeOnCorrectThread(() -> {
                stateInfoNode.setText("Current state number: " + getCurrentStateNumber() 
                        + " out of " + getStateCount());
            });
        }
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
        
        // Shorthand.
        Node nodeA = relation.getNodeA();
        
        // Get the duration of the animation.
        Duration duration = Duration.millis(getCurrentAnimationDuration());
    
        // Calculate the middle point (the new location).
        Point3D newMiddlePoint = relation.getNodeB().getFxContainer()
                                                    .calculatePoint(relation.getPlacement());
        
        // If no movement will take place, do nothing.
        if (nodeA.getFxContainer().isPositionSet() 
               && nodeA.getFxContainer().calculatePoint(Placement.MIDDLE).equals(newMiddlePoint)) {
            return;
        }
        
        // If the node was already visible, animate it.
        if (nodeA.getFxContainer().isPositionSet()) {
            
            // Create the animation and add it to the returned collection.
            addToVisualizationsQueue(nodeA.getFxContainer().animateToMiddlePoint(
                                                                newMiddlePoint, 
                                                                duration));
         
        // If it wasn't visible yet, make it appear at the correct location.
        } else {
            executeOnCorrectThread(() -> {
                // Set the FX node to correct position.
                nodeA.getFxContainer().setFxToPositionWithMiddlePoint(newMiddlePoint);
                // Make sure its opacity is set to zero.
                nodeA.getFxContainer().getFxNode().setOpacity(0);
            });
            // Add appearing animation.
            addToVisualizationsQueue(nodeA.getFxContainer().animateAppearing(duration));
        }
        // And set the position of the node (in the model) to the new position.
        nodeA.getFxContainer().setToPositionWithMiddlePoint(newMiddlePoint);

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
        
        this.controller = new ServerController(this);
        getController().setCommunicationFormat(CommunicationFormat.JSON);
        //TODO: Register CommandHandlers.
        getController().register(new InitializationCommandHandler());
        getController().register(new EndTransitionCommandHandler());
        getController().register(new SetCurrentAnimationDurationCommandHandler());
        getController().register(new FlushCommandHandler());
        getController().register(new AddNodeCommandHandler());
        getController().register(new SetNodeFxCommandHandler());
        getController().register(new ChangeNodeFxCommandHandler());
        getController().register(new AddRelationCommandHandler());
        getController().register(new StartVisualizationCommandHandler());
        getController().register(new SwitchRelationCommandHandler());


        
        // Open the log window.
        Log.addOutput(Log.Output.WINDOW);
        Log.addOutput(Log.Output.DEFAULT);
        
        // Parse the arguments.
        final Map<String, Pattern> possibleArguments = new HashMap<String, Pattern>() {
            {
                put("help",    Pattern.compile("(?i)^-help$"));
                put("verbose", Pattern.compile("(?i)^-verbose$"));
                put("port",    Pattern.compile("(?i)^-port:(?<port>.*)$"));
            }
        };
        
        List<String> args = getParameters().getRaw();
        

        boolean exit = false;
        Matcher matcher = null;
        Integer port = null;
        
        // Loop through arguments.
        for (String argument : args) {
            argument = argument.trim();
            // Match the argument to a possible argument.
            
            // -help
            matcher = possibleArguments.get("help").matcher(argument);
            if (matcher.find()) {
                Log.add(HELP_MSG);
                continue;
            }
            
            // -verbose
            matcher = possibleArguments.get("verbose").matcher(argument);
            if (matcher.find()) {
                Log.setVerbose(true);
                Log.add("Verbose setting set to true.");
                continue;
            }
            
            // -port
            matcher = possibleArguments.get("port").matcher(argument);
            if (matcher.find()) {
                try {
                    port = Integer.valueOf(matcher.group("port"));
                } catch (NumberFormatException e) {
                    Log.add("The port number is invalid.");
                    exit = true;
                }
                continue;
            }
        }

        Log.addVerbose("Arguments passed: " + args.toString());
        
            
        // Now check if all required arguments were set and parsed.
        if (port == null) {
            Log.add("You did not (correctly) pass all required arguments.");
            exit = true;
        }
            
        if (exit) {
            Log.add("For (more) help, type -help");
            return;
        }
        
        // Now execute!
        getController().setPort(port);
        getController().listenForConnections();
    }
    
    public void windowClosed() {
        setStage(null);
        getController().getNodes().clear();
        getStates().clear();
        currentStateIndex = 0;
        getController().relistenForConnections();
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