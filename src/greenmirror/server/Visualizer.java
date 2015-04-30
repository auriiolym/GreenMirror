package greenmirror.server;

import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.VisualComponent;
import greenmirror.commands.AddNodeCommandHandler;
import greenmirror.commands.FlushCommandHandler;
import greenmirror.commands.InitializationCommandHandler;
import greenmirror.commands.SetCurrentAnimationDurationCommandHandler;
import greenmirror.commands.SetNodeAppearanceCommandHandler;
import greenmirror.commands.StartTransitionCommandHandler;

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
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.scene.Group;
import javafx.scene.layout.BorderPane;
import javafx.stage.Stage;


// Extends javafx.application.Application.
/**
 * The main visualizer class. It starts the log window and waits for connections. 
 * 
 * @author Karim El Assal
 */
public class Visualizer extends Application {
    
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
    
    // -- Class variables --------------------------------------------------------------------

    // -- Instance variables -----------------------------------------------------------------

    /**
     * The controller.
     */
    private ServerController controller;
    
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
    
    /**
     * The current queue of visualizations.
     */
    //@ private invariant visualizationsQueue != null;
    private SequentialTransition visualizationsQueue;
    
    //@ private invariant visualizerStates != null;
    private List<VisualizerState> visualizerStates = new LinkedList<>();

    
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
     * @return The <tt>Stage</tt> of the visualizer.
     */
    /*@ pure */ public Stage getStage() {
        return stage;
    }
    
    /**
     * @return The Group of all visualization elements on the visualizer.
     */
    //@ requires getStage() != null;
    /*@ pure */ public Group getVisGroup() {
        return ((Group) ((BorderPane) getStage().getScene().getRoot()).getCenter());
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
    /*@ pure */ public ParallelTransition getCurrentSubVisualizationQueue() {
        ObservableList<Animation> rootTransitions = getVisualizationsQueue().getChildren();
        return (ParallelTransition) rootTransitions.get(rootTransitions.size() - 1);
    }

    
    
    // -- Setters ----------------------------------------------------------------------------

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
    //@ requires currentAnimationDuration > 0;
    //@ ensures getCurrentAnimationDuration() == currentAnimationDuration;
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

    
    // -- Commands ---------------------------------------------------------------------------
    
    
    /**
     * Go to the next state: store the current state with the transitions needed to go to the
     * next one. Also actually go to the next one.
     * @param transition The (parallel) transitions needed to go to the next state.
     */
    //@ requires transition != null;
    //@ ensures getVisualizerStates().size() == \old(getVisualizerStates().size()) + 1;
    public void toNextState(SequentialTransition transition) {
        visualizerStates.add(new VisualizerState(getController().getNodes(), transition));
        executeOnCorrectThread(() -> {
            // Do something when it's finished.
            transition.setOnFinished(new EventHandler<ActionEvent>() {
                public void handle(ActionEvent event) {
            
                }
            });
            transition.playFromStart();
        });
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
        getController().register(new StartTransitionCommandHandler());
        getController().register(new SetCurrentAnimationDurationCommandHandler());
        getController().register(new FlushCommandHandler());
        getController().register(new AddNodeCommandHandler());
        getController().register(new SetNodeAppearanceCommandHandler());


        
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
        getController().relistenForConnections();
    }
    
    public static void main(String[] args) {
        launch(args);
    }

}