package greenmirror.server;

import greenmirror.Log;
import greenmirror.server.Visualizer.PlaybackState;
import greenmirror.server.playbackstates.PausedState;
import greenmirror.server.playbackstates.PlayingBackState;
import greenmirror.server.playbackstates.PlayingState;
import greenmirror.server.playbackstates.SteppingBackState;
import greenmirror.server.playbackstates.SteppingState;
import javafx.animation.Transition;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.scene.control.Button;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.Pane;
import javafx.scene.layout.StackPane;
import javafx.util.Duration;

import org.eclipse.jdt.annotation.NonNull;

/**
 * All the toolbar buttons.
 * 
 * @author Karim El Assal
 */
public enum ToolbarButton {

    STEP_BACK_FAST {

        @Override
        public Button build() {
            Button button = super.build();
            button.setText("|≪");
            button.getTooltip().setText("Rewind one transition.");
            
            setPane(new StackPane(button));
            return button;
        }

        @Override
        public void action() {
            executeVisualizerTransition(new SteppingBackState(), -1.0 * FAST_RATE);
        }
        
        
    },
   
    STEP_BACK {

        @Override
        public Button build() {
            Button button = super.build();
            button.setText("|<");
            button.getTooltip().setText("Play back one transition.");
            
            setPane(new StackPane(button));
            return button;
        }

        @Override
        public void action() {
            executeVisualizerTransition(new SteppingBackState(), -1.0 * NORMAL_RATE);
        }
        
    },
    
    PLAY_BACK {

        @Override
        public Button build() {
            Button button = super.build();
            button.setText("<");
            button.getTooltip().setText("Play back transitions.");
            
            setPane(new StackPane(button));
            return button;
        }

        @Override
        public void action() {
            executeVisualizerTransition(new PlayingBackState(), -1.0 * NORMAL_RATE);
        }
        
    },
    
    PAUSE {

        @Override
        public Button build() {
            Button button = super.build();
            button.setText("||");
            button.getTooltip().setText("Pause further transitions.");
            
            setPane(new StackPane(button));
            return button;
        }

        @Override
        public void action() {
            Log.add("Visualizer paused.");
            
            /* Only update the status. The rest is handled by 
             * Visualizer#transitionFinished(boolean) (which is executed after this method)
             */
            getVisualizer().setPlaybackState(new PausedState());
        }
        
    },
    
    PLAY {

        @Override
        public Button build() {
            Button button = super.build();
            button.setText(">");
            button.getTooltip().setText("Play transitions.");
            button.setDefaultButton(true);
            
            setPane(new StackPane(button));
            return button;
        }

        @Override
        public void action() {
            executeVisualizerTransition(new PlayingState(), NORMAL_RATE);
        }
    },
    
    STEP {

        @Override
        public Button build() {
            Button button = super.build();
            button.setText(">|");
            button.getTooltip().setText("Play one transition.");
            
            setPane(new StackPane(button));
            return button;
        }

        @Override
        public void action() {
            executeVisualizerTransition(new SteppingState(), NORMAL_RATE);
        }
        
    },
    
    STEP_FAST {

        @Override
        public Button build() {
            Button button = super.build();
            button.setText("≫|");
            button.getTooltip().setText("Forward one transition.");
            
            setPane(new StackPane(button));
            return button;
        }

        @Override
        public void action() {
            executeVisualizerTransition(new SteppingState(), FAST_RATE);
        }
    };
    
    // -- Constants --------------------------------------------------------------------------
    
    private static final double FAST_RATE = 1000;
    private static final double NORMAL_RATE = 1.0;
    
    
    // -- Instance variables -----------------------------------------------------------------

    private Visualizer visualizer;
    private Pane pane;
    private boolean enabled = false;
    protected final EventHandler<ActionEvent> clickEvent = new EventHandler<ActionEvent>() {
        @Override public void handle(ActionEvent arg0) {
            action();
        }
    };

    
    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @return The Visualizer instance.
     */
    public Visualizer getVisualizer() {
        return visualizer;
    }
    
    /**
     * @return The Pane that holds the button's elements.
     */
    public Pane getPane() {
        return pane;
    }
    
    /**
     * @return Whether the button is enabled.
     */
    public boolean isEnabled() {
        return enabled;
    }

    // -- Setters ----------------------------------------------------------------------------
    
    /**
     * @param visualizer The Visualizer to remember for later use.
     */
    //@ requires visualizer != null;
    //@ ensures getVisualizer() == visualizer;
    public void setVisualizer(Visualizer visualizer) {
        this.visualizer = visualizer;
    }
    
    /**
     * @param pane The Pane that holds the button's elements.
     */
    //@ ensures getPane() == pane;
    protected void setPane(Pane pane) {
        this.pane = pane;
    }

    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * Set whether the button is enabled or not. It also changes the appearance of the button.
     * @param enabled
     */
    //@ ensures isEnabled() == enabled;
    public void setEnabled(boolean enabled) {
        this.enabled = enabled;
        getVisualizer().executeOnCorrectThread(() -> {
            ((Button) getPane().getChildren().get(0)).setDisable(!isEnabled());
        });
    }
    
    /**
     * Retrieve a prototype toolbar button. It's disabled by default. Specific customization
     * can be done by the overriding methods.
     * @param inst The current instance of <code>ToolbarButton</code>, so the click event can be 
     *             registered.
     * @return     The button.
     */
    //@ ensures getPane() != null;
    //@ ensures \result != null;
    public Button build() {
        Button button = new Button();
        button.setStyle("-fx-base: lightgreen; -fx-font-family: monospace;");
        button.setOnAction(this.clickEvent);
        button.setDisable(true);
        Tooltip tooltip = new Tooltip();
        tooltip.setStyle(
                  "-fx-background-radius: 1 1 1 1;"
                + "-fx-background-color: linear-gradient(lightgreen, darkgreen);"
                + "-fx-text-fill: black;"
                + "-fx-font: 14px Arial;");
        button.setTooltip(tooltip);
        return button;
    }
    
    /**
     * Do something when the button is clicked. 
     */
    public abstract void action();

    /**
     * Execute a visualizer transition. This method assumes a forward or backward transition
     * is possible. If <code>rate</code> is positive, a forward transition is assumed. If the 
     * <code>pbStateWhilePlaying</code> is NOT
     * continuous, a 'stepping' transition is assumed: the delay is removed and after the
     * transition is finished, the playback state is set to paused.
     * @param pbStateWhilePlaying The playback status set during the transition.
     * @param rate The rate with which the transition will take place. 
     *        {@see javafx.animation.Animation#rateProperty()}
     */
    public void executeVisualizerTransition(@NonNull PlaybackState pbStateWhilePlaying, double rate) {

        final boolean goingForward = rate > 0;
        final boolean isStep = !pbStateWhilePlaying.isContinuous();
        final int newStateNumber = getVisualizer().getCurrentMementoNumber() 
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
