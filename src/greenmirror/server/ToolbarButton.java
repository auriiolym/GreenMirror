package greenmirror.server;

import greenmirror.Log;
import greenmirror.server.Visualizer.Status;
import javafx.animation.Transition;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.scene.control.Button;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.Pane;
import javafx.scene.layout.StackPane;
import javafx.util.Duration;

public enum ToolbarButton {

    PLAY_REVERSE_ONE_FAST {

        /* (non-Javadoc)
         * @see greenmirror.server.ToolbarButton#setFromStatus(greenmirror.server.Visualizer.Status)
         */
        @Override
        public void setFromStatus(Status status) {
            final boolean trueIfPossible = getVisualizer().hasPreviousState();
            
            switch (status) {
            case PAUSED:
                setEnabled(trueIfPossible);
                break;
            default:
                setEnabled(false);
                break;
            }
        }

        /* (non-Javadoc)
         * @see greenmirror.server.ToolbarButton#build()
         */
        @Override
        public void build() {
            
            Button button = getNewButton(this);
            button.setText("|≪");
            button.setTooltip(new Tooltip("Rewind one transition."));
            
            setPane(new StackPane(button));
        }

        /* (non-Javadoc)
         * @see greenmirror.server.ToolbarButton#buttonClicked()
         */
        @Override
        public void action() {
            executeVisualizerTransition(Visualizer.Status.PLAYING_REVERSE_ONE_FAST, 
                    Visualizer.Status.PAUSED, -10.0, false, true);
        }
        
        
    },
   
    PLAY_REVERSE_ONE {

        /* (non-Javadoc)
         * @see greenmirror.server.ToolbarButton#setFromStatus(greenmirror.server.Visualizer.Status)
         */
        @Override
        public void setFromStatus(Status status) {
            final boolean trueIfPossible = getVisualizer().hasPreviousState();
            
            switch (status) {
            case PAUSED:
                setEnabled(trueIfPossible);
                break;
            default:
                setEnabled(false);
                break;
            }
        }

        /* (non-Javadoc)
         * @see greenmirror.server.ToolbarButton#build()
         */
        @Override
        public void build() {
            
            Button button = getNewButton(this);
            button.setText("|<");
            button.setTooltip(new Tooltip("Play back one transition."));
            
            setPane(new StackPane(button));
        }

        /* (non-Javadoc)
         * @see greenmirror.server.ToolbarButton#buttonClicked()
         */
        @Override
        public void action() {
            
            executeVisualizerTransition(Visualizer.Status.PLAYING_REVERSE_ONE, 
                    Visualizer.Status.PAUSED, -1.0, false, true);
        }
        
    },
    
    PLAY_REVERSE {

        /* (non-Javadoc)
         * @see greenmirror.server.ToolbarButton#setFromStatus(greenmirror.server.Visualizer.Status)
         */
        @Override
        public void setFromStatus(Status status) {
            final boolean trueIfPossible = getVisualizer().hasPreviousState();
            
            switch (status) {
            // Only set enabled if the visualizer is paused and it's got a previous state.
            case PAUSED:
                setEnabled(trueIfPossible);
                break;
            default:
                setEnabled(false);
                break;
            }
        }

        /* (non-Javadoc)
         * @see greenmirror.server.ToolbarButton#build()
         */
        @Override
        public void build() {
            
            Button button = getNewButton(this);
            button.setText("<");
            button.setTooltip(new Tooltip("Play transitions reversed."));
            
            setPane(new StackPane(button));
        }

        /* (non-Javadoc)
         * @see greenmirror.server.ToolbarButton#buttonClicked()
         */
        @Override
        public void action() {
            //TODO: fix this.
            // Update status.
            getVisualizer().setStatus(Visualizer.Status.PLAYING_REVERSE);
            setAllFromStatus(getVisualizer().getStatus());
            
            // To next states.
            getVisualizer().getPreviousTransition().setOnFinished(new EventHandler<ActionEvent>() {
                @Override public void handle(ActionEvent arg0) {
                    // Don't do anything other than the default actions.
                    getVisualizer().transitionFinished(false);
                }
            });
            // Indicate that we're going forward with a regular speed.
            getVisualizer().getPreviousTransition().setRate(-1.0);
            getVisualizer().toPreviousState();
        }
        
    },
    
    PAUSE {

        /* (non-Javadoc)
         * @see greenmirror.server.ToolbarButton#setFromStatus(greenmirror.server.Visualizer.Status)
         */
        @Override
        public void setFromStatus(Status status) {
            switch (status) {
            case PAUSED: default:
                setEnabled(false);
                break;
            // Only enable pause button when the visualizer isn't stopping automatically.
            case PLAYING: case PLAYING_REVERSE:
                setEnabled(true);
                break;
            }
        }

        /* (non-Javadoc)
         * @see greenmirror.server.ToolbarButton#build()
         */
        @Override
        public void build() {
            
            Button button = getNewButton(this);
            button.setText("||");
            button.setTooltip(new Tooltip("Pause the transitions (after the current "
                    + "transition has finished)."));
            
            setPane(new StackPane(button));
        }

        /* (non-Javadoc)
         * @see greenmirror.server.ToolbarButton#buttonClicked()
         */
        @Override
        public void action() {
            Log.add("Visualizer paused.");
            
            /* Only update the status. The rest is handled by 
             * Visualizer#transitionFinished(boolean) (which is executed after this method)
             */
            getVisualizer().setStatus(Visualizer.Status.PAUSED);
        }
        
    },
    
    PLAY {

        /* (non-Javadoc)
         * @see greenmirror.server.ToolbarButton#setFromStatus(greenmirror.server.Visualizer.Status)
         */
        @Override
        public void setFromStatus(Status status) {
            final boolean trueIfPossible = getVisualizer().hasNextState();
            
            switch (status) {
            // Only set enabled if the visualizer is paused and it's got a next state.
            case PAUSED:
                setEnabled(trueIfPossible);
                break;
            default:
                setEnabled(false);
                break;
            }
        }

        /* (non-Javadoc)
         * @see greenmirror.server.ToolbarButton#build()
         */
        @Override
        public void build() {
            
            Button button = getNewButton(this);
            button.setText(">");
            button.setTooltip(new Tooltip("Play transitions."));
            button.setDefaultButton(true);
            
            setPane(new StackPane(button));
        }

        /* (non-Javadoc)
         * @see greenmirror.server.ToolbarButton#buttonClicked()
         */
        @Override
        public void action() {
            //TODO: fix this.
            // Update status.
            getVisualizer().setStatus(Visualizer.Status.PLAYING);
            setAllFromStatus(getVisualizer().getStatus());
            
            // To next states.
            getVisualizer().getNextTransition().setOnFinished(new EventHandler<ActionEvent>() {
                @Override public void handle(ActionEvent arg0) {
                    // Don't do anything other than the default actions.
                    getVisualizer().transitionFinished(true);
                }
            });
            // Indicate that we're going forward with a regular speed.
            getVisualizer().getNextTransition().setRate(1.0);
            getVisualizer().toNextState();
        }
        
    },
    
    PLAY_ONE {

        /* (non-Javadoc)
         * @see greenmirror.server.ToolbarButton#setFromStatus(greenmirror.server.Visualizer.Status)
         */
        @Override
        public void setFromStatus(Status status) {
            final boolean trueIfPossible = getVisualizer().hasNextState();
            
            switch (status) {
            // Only set enabled if the visualizer is paused and it's got a next state.
            case PAUSED:
                setEnabled(trueIfPossible);
                break;
            default:
                setEnabled(false);
            }
        }

        /* (non-Javadoc)
         * @see greenmirror.server.ToolbarButton#build()
         */
        @Override
        public void build() {
            Button button = getNewButton(this);
            button.setText(">|");
            button.setTooltip(new Tooltip("Play one transition."));
            
            setPane(new StackPane(button));
        }

        /* (non-Javadoc)
         * @see greenmirror.server.ToolbarButton#buttonClicked()
         */
        @Override
        public void action() {
            
            executeVisualizerTransition(Visualizer.Status.PLAYING_ONE, 
                    Visualizer.Status.PAUSED, 1.0, true, true);
        }
        
    },
    
    PLAY_ONE_FAST {

        /* (non-Javadoc)
         * @see greenmirror.server.ToolbarButton#setFromStatus(greenmirror.server.Visualizer.Status)
         */
        @Override
        public void setFromStatus(Status status) {
            final boolean trueIfPossible = getVisualizer().hasNextState();
            
            switch (status) {
            // Only set enabled if the visualizer is paused and it's got a next state.
            case PAUSED:
                setEnabled(trueIfPossible);
                break;
            default:
                setEnabled(false);
            }
        }

        /* (non-Javadoc)
         * @see greenmirror.server.ToolbarButton#build()
         */
        @Override
        public void build() {
            Button button = getNewButton(this);
            button.setText("≫|");
            button.setTooltip(new Tooltip("Forward one transition."));
            
            setPane(new StackPane(button));
        }

        /* (non-Javadoc)
         * @see greenmirror.server.ToolbarButton#buttonClicked()
         */
        @Override
        public void action() {
            
            executeVisualizerTransition(Visualizer.Status.PLAYING_ONE_FAST, 
                    Visualizer.Status.PAUSED, 10.0, true, true);
        }
        
    }
    ;
    
    // -- Instance variables -----------------------------------------------------------------

    private Visualizer visualizer;
    private Pane pane;
    private boolean enabled = false;
    protected final EventHandler<ActionEvent> clickEvent = new EventHandler<ActionEvent>() {
        @Override
        public void handle(ActionEvent arg0) {
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
    public boolean getEnabled() {
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
    //@ ensures getEnabled() == enabled;
    public void setEnabled(boolean enabled) {
        this.enabled = enabled;
        getVisualizer().executeOnCorrectThread(() -> {
            ((Button) getPane().getChildren().get(0)).setDisable(!getEnabled());
        });
    }

    /**
     * Set several properties of this <tt>ToolbarButton</tt> on the basis of the passed status,
     * like the looks and whether the button is enabled or not.
     * @param status The visualizer's status.
     */
    //@ requires status != null;
    public abstract void setFromStatus(Visualizer.Status status);
    
    /**
     * Build the button.
     */
    //@ ensures getPane() != null;
    public abstract void build();
    
    /**
     * Do something when the button is clicked. 
     */
    public abstract void action();

    /**
     * Execute a visualizer transition. This method assumes a forward or backward transition 
     * is possible.
     * @param statusWhilePlaying
     * @param statusAfterPlaying
     * @param rate
     * @param forward
     */
    public void executeVisualizerTransition(Visualizer.Status statusBeforePlaying, 
            Visualizer.Status statusAfterPlaying, double rate, boolean forward, boolean step) {

        
        Transition toTransition = forward 
                ? getVisualizer().getNextTransition() : getVisualizer().getPreviousTransition();
        int newStateNumber = getVisualizer().getCurrentStateNumber() + (forward ? 1 : -1); 
    
        Log.add("Transition to state " + newStateNumber + " started.");
        
        // Update status.
        if (statusBeforePlaying != null) {
            getVisualizer().setStatus(statusBeforePlaying);
            setAllFromStatus(getVisualizer().getStatus());
        }
        
        // Set what to do when the transition finishes.
        toTransition.setOnFinished(new EventHandler<ActionEvent>() {
            @Override public void handle(ActionEvent arg0) {
                // Change status when the state is reached.
                if (statusAfterPlaying != null) {
                    getVisualizer().setStatus(statusAfterPlaying);
                }
                
                // Add log.
                Log.add("State " + newStateNumber + " reached.");
                
                // Execute default actions on finishing.
                getVisualizer().transitionFinished(forward);
            }
        });
        
        // Indicate with which rate we're transitioning.
        toTransition.setRate(rate);
        
        // Set the delay.
        double delay = step ? 0 : getVisualizer().getCurrentTransitionDelay();
        toTransition.setDelay(Duration.millis(delay));
        
        // And go to the next or previous state.
        if (forward) {
            getVisualizer().toNextState();
        } else {
            getVisualizer().toPreviousState(); 
        }
    }
    

    // -- Class usage ------------------------------------------------------------------------
    
    public static Button getNewButton(ToolbarButton inst) {
        Button button = new Button();
        button.setStyle("-fx-base: lightgreen; -fx-font-family: monospace;");
        button.setOnAction(inst.clickEvent);
        button.setDisable(true);
        return button;
    }
    
    public static void setAllFromStatus(Status status) {
        for (ToolbarButton button : values()) {
            button.setFromStatus(status);
        }
    }
}
