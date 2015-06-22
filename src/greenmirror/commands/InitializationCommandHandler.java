package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.ServerSide;
import greenmirror.server.ServerController;
import greenmirror.server.ToolbarButton;
import greenmirror.server.Visualizer;

import org.eclipse.jdt.annotation.NonNull;

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
 * @author  Karim El Assal
 * @see     InitializationCommand
 */
@ServerSide
public class InitializationCommandHandler extends CommandHandler {

    // -- Queries ----------------------------------------------------------------------------
    
    @Override
    //@ ensures \result != null;
    /*@ pure */ public ServerController getController() {
        return (ServerController) super.getController();
    }

    
    // -- Commands ---------------------------------------------------------------------------


    @Override
    public void handle(@NonNull CommunicationFormat format, @NonNull String data) 
            throws DataParseException {

        final Double width;
        final Double height;
        final Double duration;
        final boolean rotateRigidlyRelatedNodesRigidly;
        
        switch (format) {
        default: case JSON:
            Map<String, Object> map = CommandHandler.parseJson(data);
            // Check data existence.
            if (!map.containsKey("width") || !map.containsKey("height") 
                                          || !map.containsKey("defaultAnimationDuration")
                                          || !map.containsKey("rotateRigidlyRelatedNodesRigidly")) {
                throw new DataParseException("The received data does not contain the width, "
                        + "height, default animation duration or the "
                        + "rotateRigidlyRelatedNodesRigidly setting.");
            }
            
            width = ((BigDecimal) map.get("width")).doubleValue();
            height = ((BigDecimal) map.get("height")).doubleValue();
            duration = ((BigDecimal) map.get("defaultAnimationDuration")).doubleValue();
            rotateRigidlyRelatedNodesRigidly 
                = (Boolean) map.get("rotateRigidlyRelatedNodesRigidly");
            
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
        getController().getVisualizer()
            .setRotateRigidlyRelatedNodesRigidly(rotateRigidlyRelatedNodesRigidly);
        initialize(width, height);
    }
    
    
    private void initialize(double width, double height) {
        final Visualizer visualizer = getController().getVisualizer();
        if (visualizer == null) { // @NonNull annotation formality
            throw new RuntimeException("Visualizer is null");
        }
        visualizer.executeOnCorrectThread(() -> {
            
            final double toolbarHeight = 30;
            
            // Create window.
            final Stage stage = new Stage();
            stage.setTitle("GreenMirror Visualizer");
            visualizer.setStage(stage);
            
            // ToolBar.
            final ToolBar toolBar = new ToolBar();
            toolBar.setOrientation(Orientation.HORIZONTAL);
            toolBar.setPrefHeight(toolbarHeight);
            // Add toolBar buttons.
            for (ToolbarButton button : ToolbarButton.values()) {
                button.setVisualizer(visualizer);
                toolBar.getItems().add(button.build());
            }
            // Add status info.
            final Text playbackInfo = new Text();
            playbackInfo.setId("playbackInfo");
            toolBar.getItems().add(playbackInfo);
            // Add spacer.
            final Region spacer = new Region();
            HBox.setHgrow(spacer, Priority.ALWAYS);
            toolBar.getItems().add(spacer);
            // Add stateInfo node.
            final Text stateInfo = new Text();
            stateInfo.setId("stateInfo");
            toolBar.getItems().add(stateInfo);
            
            
            // Visualizer.
            final Pane vis = new Pane();
            vis.setMaxWidth(Region.USE_PREF_SIZE);
            vis.setMaxHeight(Region.USE_PREF_SIZE);
            vis.setPrefSize(width, height);
            vis.setId("FxNodePane");
            vis.setBackground(new Background(new BackgroundFill(
                    Paint.valueOf("linear-gradient(to top, #F5F5F5, #C2C2C2)"), null, null)));
            
            
            // Root Node
            final VBox root = new VBox();
            root.setSpacing(0);
            root.getChildren().addAll(toolBar, vis);
            
            
            // Do some cleanup after the window has been closed.
            stage.setOnHidden(new EventHandler<WindowEvent>() {
                @Override
                public void handle(WindowEvent arg0) {
                    visualizer.reset();
                }
            });

            // Finish up and display.
            final Scene scene = new Scene(root, width, height + toolbarHeight, 
                    Paint.valueOf("linear-gradient(to bottom, #F5F5F5, #C2C2C2)"));
            stage.setScene(scene);
            stage.show();
            visualizer.updateMementoNumberInfo();
            
            // Add to log
            Log.add("Visualizer initialized with width " + width + "px and height " 
                    + height + "px.");

        });
    }
}