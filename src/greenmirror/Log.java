package greenmirror;

import java.text.SimpleDateFormat;
import java.util.Calendar;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import javafx.application.Platform;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.ScrollPane;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;
import javafx.scene.text.Text;
import javafx.stage.Stage;


/**
 * The class handling the log.
 * 
 * @author Karim El Assal
 */
public class Log {
    
    // -- Enumerations -----------------------------------------------------------------------

    /**
     * The different types of output.
     * 
     * @author Karim El Assal
     */
    public static enum Output {
        
        /**
         * The default output: <tt>System.out</tt>.
         */
        DEFAULT {
            
            /**
             * The default output type does not have to be initialized.
             */
            @Override
            public void initialize() {}
            
            /**
             * Add a <tt>String</tt> to the default output.
             * @param str The <tt>String</tt>.
             */
            @Override 
            public void addToOutput(String str) {
                System.out.println("[" + getTimestamp() + "] " + str);
            }
            
            /**
             * Close the default log.
             */
            @Override
            public void close() {
                addToOutput("Default log output closed.");
            }
        },
        
        /**
         * The output window. Only available if we're already running a JavaFX application.
         */
        WINDOW {
            
            private static final double WIDTH  = 800;
            private static final double HEIGHT = 250;
            private static final String TEXTSTYLE = "-fx-font-size: 13px; "
                                                  + "-fx-font-family: monospace;";
            
            private VBox vbox;
            private ScrollPane scrollpane;
            private Stage stage;
            private Scene scene;
            
            /**
             * Initialize the window, if possible.
             */
            @Override
            public void initialize() {
                
                try {
                    Runnable startWindow = () -> {
                        stage = new Stage();
                        stage.setTitle("Log");
                        
                        scrollpane = new ScrollPane();
                        scrollpane.setFitToWidth(true);
                        //scrollPane.setFitToHeight(true);
                        
                        Pane pane = new Pane();
                        pane.setStyle("-fx-background-color: white;");
                        scrollpane.setContent(pane); 

                        vbox = new VBox();
                        vbox.setStyle("-fx-padding: 5px; -fx-spacing: 4px;");
                        vbox.setAlignment(Pos.BOTTOM_LEFT);
                        vbox.setMinHeight(HEIGHT);
                        // Enable automatic scrolling to the bottom.
                        vbox.heightProperty().addListener(new ChangeListener<Number>() {
                            @Override
                            public void changed(ObservableValue<? extends Number> observable,
                                                Number oldvalue, 
                                                Number newValue) {
                                scrollpane.setVvalue((Double) newValue);
                            }
                        });
                        pane.getChildren().add(vbox);

                        scene = new Scene(scrollpane, WIDTH, HEIGHT);
                        stage.setScene(scene);     
                        stage.show();
                        
                        // Alter values according to new sizes.
                        ChangeListener<Number> changeListener = new ChangeListener<Number>() {
                            @Override 
                            public void changed(ObservableValue<? extends Number> observableValue,
                                                Number oldValue,
                                                Number newValue) {
                                updateValues();
                            }
                        };
                        scene.widthProperty().addListener(changeListener);
                        scene.heightProperty().addListener(changeListener);

                        addToOutput("Log opened.");
                    };
                    
                    // Start the Stage if we're on the correct thread. If not, try to run later.
                    if (Platform.isFxApplicationThread()) {
                        startWindow.run();
                    } else {
                        Platform.runLater(startWindow);
                    }
                } catch (IllegalStateException e) {
                    addOutput(Output.DEFAULT);
                    add("A new log window could not be created. The JavaFX application has "
                      + "probably not been initialized (yet). The default output is selected "
                      + "in stead.");
                }
            }
            
            private void updateValues() {
                for (javafx.scene.Node node : vbox.getChildren()) {
                    Text textNode = (Text) node;
                    textNode.setWrappingWidth(scene.getWidth() - 10);
                }
                vbox.setMinHeight(scene.getHeight() - 3);
            }
            
            /**
             * Add a <tt>String</tt> to the output window.
             * @param str The <tt>String</tt>.
             */
            @Override 
            public void addToOutput(String str) {
                try {
                    Runnable addOutput = () -> {
                        Text text = new Text("[" + getTimestamp() + "] " + str);
                        text.setStyle(TEXTSTYLE);
                        //text.setWrappingWidth(scene.getWidth() - 10);
                        vbox.getChildren().add(text);
                        updateValues();
                    };
                    // This should be running on JavaFX thread if we're not already.
                    if (Platform.isFxApplicationThread()) {
                        addOutput.run();
                    } else {
                        Platform.runLater(addOutput);
                    }
                } catch (IllegalStateException e) {
                    //TODO: do something with this.
                }
            }
            
            /**
             * Close the window.
             */
            @Override
            public void close() {
                stage.close();
            }
        };
        
        /**
         * The initialization method for any output type.
         */
        public abstract void initialize();
        
        /**
         * The method that will add a <tt>String</tt> to the selected output.
         * @param str The <tt>String</tt>.
         */
        public abstract void addToOutput(String str);
        
        /**
         * The method that will close the selected output.
         */
        public abstract void close();
    }

    // -- Class variables --------------------------------------------------------------------
    
    /**
     * Entries of the log.
     */
    //@ private invariant entries != null;
    private static List<String> entries = new LinkedList<String>();
    
    /**
     * The selected log output types.
     */
    //@ private invariant outputs != null;
    private static Set<Output> outputs = new TreeSet<Output>();
    
    /**
     * Whether to log verbose data.
     */
    private static boolean verbose = false;
    

    // -- Class usage ------------------------------------------------------------------------
 


    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @return The log entries.
     */
    //@ private ensures \result != null && \result == entries;
    /*@ pure */ private static List<String> getEntries() {
        return entries;
    }
    
    /**
     * @return The current date and time.
     */
    /*@ pure */ private static String getTimestamp() {
        return new SimpleDateFormat("YYYY-MM-dd HH:mm:ss.SSS")
                    .format(Calendar.getInstance().getTime());
    }
    
    /**
     * @return Whether to output verbose data.
     */
    /*@ pure */ public static boolean isVerbose() {
        return verbose;
    }
    
    // -- Setters ----------------------------------------------------------------------------

    /**
     * @param verbose Set whether to be verbose.
     */
    //@ ensures isVerbose() == verbose;
    public static void setVerbose(boolean verbose) {
        Log.verbose = verbose;
    }
    
    /**
     * Add <tt>output</tt> to the list of outputs and prepare the type of output.
     * @param output The type of output.
     */
    //@ requires output != null;
    public static void addOutput(Output output) {
        if (!outputs.contains(output)) {
            output.initialize();
        }
        outputs.add(output);
    }
    
    
    // -- Commands ---------------------------------------------------------------------------
    
    
    /**
     * Remove the selected output and clean up if necessary.
     * @param output The output.
     */
    public static void removeOutput(Output output) {
        if (outputs.contains(output)) {
            output.close();
        }
        outputs.remove(output);
    }
    
    
    /**
     * Add data to the log.
     * @param obj Any (stringifiable) data.
     */
    public static void add(Object obj) {
        // Get String value.
        String data = String.valueOf(obj);
        
        // Store in the list.
        getEntries().add(data);
        
        // Output to every selected output type.
        for (Output outputType : outputs) {
            outputType.addToOutput(data);
        }
        
        // Add to default output if there were no output types selected.
        if (outputs.size() == 0) {
            Output.DEFAULT.addToOutput(data);
        }
    }
    
    /**
     * Add data to the log with the information of an <tt>Exception</tt> appended.
     * @param obj       Any (stringifiable) data.
     * @param exception The thrown exception.
     */
    //@ requires obj != null && exception != null;
    public static void add(Object obj, Exception exception) {
        String data = String.valueOf(obj) + String.valueOf(exception) + "\nWith stacktrace:";
        for (StackTraceElement stElement : exception.getStackTrace()) {
            data += "\n    " + stElement.toString();
        }
        add(data);
    }
    
    /**
     * Add verbose data to the log, but only if the verbose setting is enabled.
     * @param obj Any (stringifiable) data.
     */
    public static void addVerbose(Object obj) {
        if (isVerbose()) {
            add(obj);
        }
    }
}