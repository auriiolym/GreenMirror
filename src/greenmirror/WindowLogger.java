package greenmirror;

import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;

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
 * The logger that prints entries to a window.
 * 
 * @author Karim El Assal
 */
public class WindowLogger extends PrintStream {
    
    // -- Constants --------------------------------------------------------------------------
    
    /** The width of the window in pixels. */
    private static final double WIDTH  = 800;
    
    /** The height of the window in pixels. */
    private static final double HEIGHT = 250;
    
    /** The title of the window. */
    private static final String TITLE = "Log";
    
    /** The CSS style of the javafx.scene.Text nodes. */
    private static final String TEXTSTYLE = "-fx-font-size: 13px; "
                                          + "-fx-font-family: monospace;";


    // -- Constructors -----------------------------------------------------------------------
    
    /**
     * Create a new <tt>WindowLogger</tt>.
     */
    public WindowLogger() {
        super(new WindowOutputStream());
    }
    
    
    // -- Inner (auxilary) classes -----------------------------------------------------------
    
    /**
     * The <tt>OutputStream</tt> implementation that writes to the log window.
     * 
     * @author Karim El Assal
     */
    private static class WindowOutputStream extends OutputStream {
        
        // -- Instance variables --------------------------
        
        /** The JavaFX stage. */
        private Stage stage;
        
        /** The JavaFX node that holds all Text entries of the stage. */
        private VBox vbox;
        
        /** The entry of the writer. */
        private String buffer = "";
        
        
        // -- Constructors --------------------------------
        
        /**
         * Create a new window.
         */
        public WindowOutputStream() {

            try {
                Runnable startWindow = () -> {
                    stage = new Stage();
                    stage.setTitle(TITLE);
                    
                    ScrollPane scrollpane = new ScrollPane();
                    scrollpane.setFitToWidth(true);
                    
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

                    Scene scene = new Scene(scrollpane, WIDTH, HEIGHT);
                    stage.setScene(scene);     
                    stage.show();
                    
                    // Alter values according to new sizes.
                    ChangeListener<Number> changeListener = new ChangeListener<Number>() {
                        @Override 
                        public void changed(ObservableValue<? extends Number> observableValue,
                                            Number oldValue, Number newValue) {
                            updateValues();
                        }
                    };
                    scene.widthProperty().addListener(changeListener);
                    scene.heightProperty().addListener(changeListener);

                    Log.add("Log window opened.");
                };
                
                // Start the Stage if we're on the correct thread. If not, try to run later.
                if (Platform.isFxApplicationThread()) {
                    startWindow.run();
                } else {
                    Platform.runLater(startWindow);
                }
            } catch (IllegalStateException e) {
                Log.addOutput(Log.DEFAULT);
                Log.add("A new log window could not be created. The JavaFX application has "
                  + "probably not been initialized (yet). The default output is selected "
                  + "in stead.");
            }
        }
        
        /**
         * Update certain layout values. Can be used when the window has been resized. This has
         * to be executed on the JavaFX thread.
         */
        private void updateValues() {
            for (javafx.scene.Node node : vbox.getChildren()) {
                Text textNode = (Text) node;
                textNode.setWrappingWidth(stage.getScene().getWidth() - 10);
            }
            vbox.setMinHeight(stage.getScene().getHeight() - 3);
        }

        /* (non-Javadoc)
         * @see java.io.OutputStream#write(int)
         */
        @Override
        public synchronized void write(int arg0) throws IOException {
            buffer += (char) arg0;
        }
        
        /**
         * Flush the buffer to the output window.
         */
        @Override
        public synchronized void flush() {
            
            // Remove the optional newline: our FX structure takes care of the newline.
            if (buffer.length() > 0 && buffer.substring(buffer.length() - 1).equals("\n")) {
                buffer = buffer.substring(0, buffer.length() - 2);
            }
            try {
                final String outputString = buffer;
                Runnable addOutput = () -> {
                    Text text = new Text("[" + Log.getTimestamp() + "] " + outputString);
                    text.setStyle(TEXTSTYLE);
                    vbox.getChildren().add(text);
                    updateValues();
                };
                // This should be running on JavaFX thread if we're not already.
                if (Platform.isFxApplicationThread()) {
                    addOutput.run();
                } else {
                    Platform.runLater(addOutput);
                }
                buffer = "";
                
            } catch (IllegalStateException e) {
                Log.addOutput(Log.DEFAULT);
                Log.add("Something went wrong with adding a log entry to the log window:", e);
            }
        }
        
        /**
         * Close the window.
         */
        @Override
        public void close() {
            stage.close();
        }   
    }
}
