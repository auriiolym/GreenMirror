package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.FxWrapper;
import greenmirror.Log;
import greenmirror.Node;
import greenmirror.server.ServerController;
import greenmirror.server.Visualizer;
import groovy.json.internal.LazyValueMap;

import java.util.Map;

import javafx.animation.FadeTransition;
import javafx.util.Duration;

/**
 * The handler that sets the FX of a node. This command is received from the client.
 */
@CommandHandler.ServerSide
public class SetNodeFxCommandHandler extends CommandHandler {

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
     * @throws MissingDataException When the data is incomplete.
     * @throws DataParseException   When parsing the data went wrong.
     */
    //@ requires getController() != null && format != null && data != null;
    public void handle(CommunicationFormat format, String data) 
            throws MissingDataException, DataParseException {
        
        final Node node;
        final LazyValueMap fxMap;
        
        switch (format) {
        default: case JSON:
            Map<String, Object> map = CommandHandler.parseJson(data);
            if (!map.containsKey("id") || !map.containsKey("fx")
                    || !(map.get("fx") instanceof LazyValueMap)
                    || !((LazyValueMap) map.get("fx")).containsKey("type")) {
                throw new MissingDataException();
            }
            node = getController().getNode((int) map.get("id"));
            if (node == null) {
                throw new DataParseException("Unknown Node with id " + map.get("id"));
            }
            
            fxMap = (LazyValueMap) map.get("fx");
            break;
        }
            
            
        // We're assuming here that the FX of the Node has not been set yet.

        final Visualizer visualizer = getController().getVisualizer();
        final Duration duration = Duration.millis(visualizer.getCurrentAnimationDuration());
            
        // Get new instance.
        final FxWrapper fxWrapper;
        try {
            fxWrapper = node.fx(String.valueOf(fxMap.get("type")));
        } catch (IllegalArgumentException e) {
            throw new DataParseException("An unknown FX type was selected or the FX was "
                    + "already set.");
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
        fxNode.setVisible(false); // Is updated before each fade animation.
        
        // Add the FX Node to the stage.
        visualizer.executeOnCorrectThread(() -> {
            visualizer.getFxNodePane().getChildren().add(fxNode);
            
            // Add a log entry.
            Log.add("Node " + Log.n(node) + " added to the visualization.");
        });
        
        
        // If a position is set, add the fade in transition to the queue.
        if (fxWrapper.isPositionSet()) {
            visualizer.addToVisualizationsQueue(
                    fxWrapper.animateOpacity(0.0, fxWrapper.getOpacity(), duration));
        }

    }

}