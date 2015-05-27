package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.server.ServerController;
import greenmirror.server.ToolbarButton;

import java.math.BigDecimal;
import java.util.Map;

import javafx.event.EventHandler;
import javafx.geometry.Orientation;
import javafx.scene.Scene;
import javafx.scene.control.ToolBar;
import javafx.scene.layout.Background;
import javafx.scene.layout.BackgroundFill;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Pane;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;
import javafx.scene.layout.VBox;
import javafx.scene.paint.Paint;
import javafx.scene.text.Text;
import javafx.stage.Stage;
import javafx.stage.WindowEvent;


/**
 * The handler that initializes the visualizer. This command is received from the client.
 * 
 * @author Karim El Assal
 */
@CommandHandler.ServerSide
public class InitializationCommandHandler extends CommandHandler {

    // -- Queries ----------------------------------------------------------------------------
    
    /* (non-Javadoc)
     * @see greenmirror.CommandHandler#getController()
     */
    @Override
    //@ ensures \result != null;
    /*@ pure */ public ServerController getController() {
        return (ServerController) super.getController();
    }

    
    // -- Commands ---------------------------------------------------------------------------

    /**
     * Handle the received command. 
     * @param format The format in which the data is received.
     * @param data   The (raw) received data.
     * @throws DataParseException When parsing the data went wrong.
     */
    //@ requires getController() != null && format != null && data != null;
    public void handle(CommunicationFormat format, String data) 
            throws DataParseException {
        

        Double width;
        Double height;
        Double duration;
        
        switch (format) {
        default: case JSON:
            Map<String, Object> map = CommandHandler.parseJson(data);
            // Parse received data.
            if (!map.containsKey("width") || !map.containsKey("height") 
                                          || !map.containsKey("defaultTransitionDuration")) {
                throw new DataParseException("The received data does not contain the width, "
                        + "height and/or the default transition duration.");
            }
            
            width = ((BigDecimal) map.get("width")).doubleValue();
            height = ((BigDecimal) map.get("height")).doubleValue();
            duration = ((BigDecimal) map.get("defaultTransitionDuration")).doubleValue();
            
            if (!(width > 0 
                    && height > 0 
                    && duration >= -1)) {
                throw new DataParseException("The received data is of the wrong format. "
                        + "Data: " + data);
            }
        }
        
        // Save data and initialize the visualizer.
        if (duration >= 0) {
            getController().getVisualizer().setDefaultAnimationDuration(duration);
        }
        initialize(width, height);
    }
    
    
    private void initialize(double width, double height) {
        getController().getVisualizer().executeOnCorrectThread(() -> {
            
            final double toolbarHeight = 30;
            
            // Create window.
            Stage stage = new Stage();
            stage.setTitle("GreenMirror Visualizer");
            getController().getVisualizer().setStage(stage);
            

            
            // ToolBar.
            ToolBar toolBar = new ToolBar();
            toolBar.setOrientation(Orientation.HORIZONTAL);
            toolBar.setPrefHeight(toolbarHeight);
            // Add toolBar buttons.
            for (ToolbarButton button : ToolbarButton.values()) {
                button.setVisualizer(getController().getVisualizer());
                button.build();
                toolBar.getItems().add(button.getPane());
            }
            // Add status info.
            Text playbackInfo = new Text();
            playbackInfo.setId("playbackInfo");
            toolBar.getItems().add(playbackInfo);
            // Add spacer.
            Region spacer = new Region();
            HBox.setHgrow(spacer, Priority.ALWAYS);
            toolBar.getItems().add(spacer);
            // Add stateInfo node.
            Text stateInfo = new Text();
            stateInfo.setId("stateInfo");
            toolBar.getItems().add(stateInfo);
            
            
            // Visualizer.
            Pane vis = new Pane();
            vis.setMaxWidth(Region.USE_PREF_SIZE);
            vis.setMaxHeight(Region.USE_PREF_SIZE);
            vis.setPrefSize(width, height);
            vis.setId("FxNodePane");
            vis.setBackground(new Background(new BackgroundFill(
                    Paint.valueOf("linear-gradient(to top, #F5F5F5, #C2C2C2)"), null, null)));
            
            
            // Root Node
            VBox root = new VBox();
            root.setSpacing(0);
            root.getChildren().addAll(toolBar, vis);
            
            
            // Do some cleanup after the window has been closed.
            stage.setOnHidden(new EventHandler<WindowEvent>() {
                @Override
                public void handle(WindowEvent arg0) {
                    getController().getVisualizer().reset();
                }
            });

            // Finish up and display.
            Scene scene = new Scene(root, width, height + toolbarHeight, 
                    Paint.valueOf("linear-gradient(to bottom, #F5F5F5, #C2C2C2)"));
            stage.setScene(scene);
            stage.show();
            getController().getVisualizer().updateMementoNumberInfo();
            
            Log.add("Visualizer initialized with width " + width + "px and height " 
                    + height + "px.");

        });
    }
}