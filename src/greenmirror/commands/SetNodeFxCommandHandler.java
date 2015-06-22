package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.FxWrapper;
import greenmirror.Log;
import greenmirror.Node;
import greenmirror.ServerSide;
import greenmirror.server.ServerController;
import greenmirror.server.Visualizer;
import groovy.json.internal.LazyValueMap;

import org.eclipse.jdt.annotation.NonNull;

import java.util.Map;

import javafx.util.Duration;

/**
 * The handler that sets the initial FX of a node. This command is received from the client.
 * 
 * @author  Karim El Assal
 * @see     SetNodeFxCommand
 */
@ServerSide
public class SetNodeFxCommandHandler extends CommandHandler {

    
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public void handle(@NonNull CommunicationFormat format, @NonNull String data) 
            throws MissingDataException, DataParseException {
        
        final Node node;
        final LazyValueMap fxMap;
        final String fxType;
        
        switch (format) {
        default: case JSON:
            final Map<String, Object> map = CommandHandler.parseJson(data);
            // Check data existence.
            if (!map.containsKey("id") || !map.containsKey("fx")
                    || !(map.get("fx") instanceof LazyValueMap)
                    || !((LazyValueMap) map.get("fx")).containsKey("type")) {
                throw new MissingDataException();
            }
            
            // Parse data.
            try {
                // Node id.
                node = getController().getNode(Integer.parseInt(String.valueOf(map.get("id"))));
            } catch (NumberFormatException e) {
                throw new DataParseException("the id of the node is invalid: " + map.get("id"));
            } catch (IllegalArgumentException e) {
                throw new DataParseException("the node with id " + map.get("id") + " is not "
                        + "found on the visualizer");
            }
            
            // FX map.
            fxMap = (LazyValueMap) map.get("fx");
            
            fxType = String.valueOf(fxMap.get("type"));
            if (fxType == null) {
                throw new DataParseException("FX type is null");
            }
            break;
        }
        
            
        // We're assuming here that the FX of the node has not been set yet.

        final Visualizer visualizer = ((ServerController) getController()).getVisualizer();
        final Duration duration = Duration.millis(visualizer.getCurrentAnimationDuration());
        if (duration == null) { // @NonNull annotation formality.
            throw new RuntimeException("Duration.millis(double) returned null");
        }
            
        // Get new instance.
        final FxWrapper fxWrapper;
        try {
            fxWrapper = node.fx(fxType);
        } catch (IllegalArgumentException e) {
            throw new DataParseException("an unknown FX type was selected or the FX was "
                    + "already set to a different type");
        }
        
        // Set the initial values in the wrapper.
        fxWrapper.setFromMap(fxMap);

        // Create the FX Node.
        fxWrapper.createFxNode();
        final javafx.scene.Node fxNode = fxWrapper.getFxNode();
        
        // Set the initial values in the FX node, except the opacity.
        // At this point, it's invisible.
        fxWrapper.setFxNodeValuesFromMap(fxMap);
        fxNode.setOpacity(0);
        fxNode.setVisible(false); // This is updated before each fade animation.
        
        // Add the FX Node to the stage.
        visualizer.executeOnCorrectThread(() -> {
            visualizer.getFxNodePane().getChildren().add(fxNode);
            
            // Add a log entry.
            Log.add("Node " + Log.n(node) + " added to the visualizer.");
        });
        
        // If a position is set, add the fade in transition to the queue.
        if (fxWrapper.isPositionSet()) {
            visualizer.addToVisualizationsQueue(
                    fxWrapper.animateOpacity(0.0, fxWrapper.getOpacity(), duration));
        }
    }
}