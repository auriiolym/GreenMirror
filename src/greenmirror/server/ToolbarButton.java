package greenmirror.server;

import greenmirror.Log;
import greenmirror.server.playbackstates.PausedState;
import greenmirror.server.playbackstates.PlayingBackState;
import greenmirror.server.playbackstates.PlayingState;
import greenmirror.server.playbackstates.SteppingBackState;
import greenmirror.server.playbackstates.SteppingState;
import greenmirror.server.Visualizer.PlaybackState;

import org.eclipse.jdt.annotation.NonNull;

import javafx.animation.Transition;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.scene.control.Button;
import javafx.scene.control.Tooltip;
import javafx.util.Duration;

/**
 * The toolbar buttons.
 * 
 * @author Karim El Assal
 */
public enum ToolbarButton {

    STEP_BACK_FAST {
        @Override @NonNull public Button build() {
            return setFxNode(build("|≪", "Rewind one transition."));
        }

        @Override public void action() {
            executeVisualizerTransition(new SteppingBackState(), -1.0 * FAST_RATE);
        }
    },
   
    STEP_BACK {
        @Override @NonNull public Button build() {
            return setFxNode(build("|<", "Play back one transition."));
        }

        @Override public void action() {
            executeVisualizerTransition(new SteppingBackState(), -1.0 * NORMAL_RATE);
        }
    },
    
    PLAY_BACK {
        @Override @NonNull public Button build() {
            return setFxNode(build("<", "Play back transitions."));
        }

        @Override public void action() {
            executeVisualizerTransition(new PlayingBackState(), -1.0 * NORMAL_RATE);
        }
        
    },
    
    PAUSE {
        @Override @NonNull public Button build() {
            return setFxNode(build("||", "Pause further transition."));
        }

        @Override public void action() {
            Log.add("Visualizer paused.");
            
            /* Only update the status. The rest is handled by 
             * Visualizer#transitionFinished(boolean) (which is executed after this method)
             */
            getVisualizer().setPlaybackState(new PausedState());
        }
    },
    
    PLAY {
        @Override @NonNull public Button build() {
            return setFxNode(build(">", "Play transitions."));
        }

        @Override  public void action() {
            executeVisualizerTransition(new PlayingState(), NORMAL_RATE);
        }
    },
    
    STEP {
        @Override @NonNull public Button build() {
            return setFxNode(build(">|", "Play one transition."));
        }

        @Override public void action() {
            executeVisualizerTransition(new SteppingState(), NORMAL_RATE);
        }
        
    },
    
    STEP_FAST {

        @Override @NonNull public Button build() {
            return setFxNode(build("≫|", "Forward one transition."));
        }

        @Override public void action() {
            executeVisualizerTransition(new SteppingState(), FAST_RATE);
        }
    };
    
    // -- Constants --------------------------------------------------------------------------
    
    /** 
     * The rate used when fast forwarding or rewinding. Don't make this too high, or the
     * interpolate method of {@link Transition} won't get a chance to change its relevant value.
     * 
     * @see javafx.animation.Animation#rateProperty() 
     */
    private static final double FAST_RATE = 50;
    
    /**
     * The normal rate of progress of an animation.
     * 
     * @see javafx.animation.Animation#rateProperty()
     */
    private static final double NORMAL_RATE = 1.0;
    
    
    // -- Instance variables -----------------------------------------------------------------

    /** The visualizer. */
    private Visualizer visualizer;
    
    /** The JavaFX node that holds the button */
    private Button fxNode;
    
    /** The click event that gets called */
    @NonNull protected final EventHandler<ActionEvent> clickEvent = new EventHandler<ActionEvent>(){
        @Override public void handle(ActionEvent arg0) {
            action();
        }
    };

    
    // -- Queries ----------------------------------------------------------------------------
    
    /** @return the visualizer instance */
    public Visualizer getVisualizer() {
        return visualizer;
    }
    
    /** @return the JavaFX node that holds the button */
    public Button getFxNode() {
        return fxNode;
    }
    

    // -- Setters ----------------------------------------------------------------------------
    
    /** @param visualizer the {@link greenmirror.server.Visualizer} to remember for later use */
    //@ ensures getVisualizer() == visualizer;
    public void setVisualizer(@NonNull Visualizer visualizer) {
        this.visualizer = visualizer;
    }
    
    /**
     * @param fxNode the JavaFX node that holds the button
     * @return       the JavaFX node
     */
    //@ ensures getFxNode() == fxNode;
    @NonNull protected Button setFxNode(@NonNull Button fxNode) {
        this.fxNode = fxNode;
        return fxNode;
    }

    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * Sets whether the button is enabled or not.
     * 
     * @param enabled <code>true</code> if the button should be enabled
     */
    public void setEnabled(boolean enabled) {
        getVisualizer().executeOnCorrectThread(() -> {
            ((Button) getFxNode()).setDisable(!enabled);
        });
    }
    
    /**
     * Creates a prototype toolbar button. It's disabled by default. Specific customization
     * can be done by overriding {@link #build(String, String)}.
     * 
     * @return the button
     */
    @NonNull private Button create() {
        final Button button = new Button();
        button.setStyle("-fx-base: lightgreen; -fx-font-family: monospace;");
        button.setOnAction(this.clickEvent);
        button.setDisable(true);
        final Tooltip tooltip = new Tooltip();
        tooltip.setStyle(
                  "-fx-background-radius: 1 1 1 1;"
                + "-fx-background-color: linear-gradient(lightgreen, darkgreen);"
                + "-fx-text-fill: black;"
                + "-fx-font: 14px Arial;");
        button.setTooltip(tooltip);
        return button;
    }
    
    /**
     * Builds the button from the prototype created by {@link #create()}.
     * 
     * @param text        the text displayed on the button
     * @param tooltipText the text displayed by the tooltip
     * @return            the button
     */
    @NonNull protected Button build(@NonNull String text, @NonNull String tooltipText) {
        final Button button = create();
        button.setText(text);
        button.getTooltip().setText(tooltipText);
        return button;
    }
    
    /** @return the created toolbar button */
    @NonNull public abstract Button build();
    
    /**
     * Do something when the button is clicked. 
     */
    public abstract void action();

    /**
     * Execute a visualizer (state-)transition. This method assumes a forward or backward 
     * transition is possible. If <code>rate</code> is positive, a forward transition is 
     * assumed. If the <code>pbStateWhilePlaying</code> is NOT continuous, a 'stepping' 
     * transition is assumed: the delay is removed and after the transition is finished, 
     * the playback state is set to paused.
     * 
     * @param pbStateWhilePlaying  the playback state set during the transition
     * @param rate                 the rate with which the transition will take place. See
     *                             {@link javafx.animation.Animation#rateProperty()}
     */
    public void executeVisualizerTransition(@NonNull PlaybackState pbStateWhilePlaying, 
                                            double rate) {

        final boolean goingForward = rate > 0;
        final boolean isStep = !pbStateWhilePlaying.isContinuous();
        final int newStateNumber = getVisualizer().getCurrentMementoIndex() 
                + (goingForward ? 1 : -1);
        final Transition toTransition = goingForward 
                ? getVisualizer().getNextMemento().getTransition() 
                : getVisualizer().getPreviousMemento().getTransition(); 
    
        Log.add("Transition to state " + newStateNumber + " started.");
        
        // Update status.
        getVisualizer().setPlaybackState(pbStateWhilePlaying);
        getVisualizer().getPlaybackState().determineButtonOperation(
                getVisualizer().hasPreviousMemento(), getVisualizer().hasNextMemento());
        
        // Set what to do when the transition finishes.
        toTransition.setOnFinished(new EventHandler<ActionEvent>() {
            @Override public void handle(ActionEvent arg0) {
                
                // Execute visualizer actions on finishing.
                getVisualizer().transitionFinished(toTransition, goingForward);
            }
        });
        
        // Indicate with which rate we're transitioning.
        toTransition.setRate(rate);
        
        // Set the delay.
        final double delay = isStep ? 0 : getVisualizer().getCurrentTransitionDelay();
        toTransition.setDelay(Duration.millis(delay));
        
        // And go to the next or previous state.
        if (goingForward) {
            getVisualizer().toNextMemento();
        } else {
            getVisualizer().toPreviousMemento(); 
        }
    }
}
