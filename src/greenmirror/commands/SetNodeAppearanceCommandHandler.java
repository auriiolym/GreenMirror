package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.Node;
import greenmirror.VisualComponent;
import greenmirror.server.ServerController;
import groovy.json.internal.LazyValueMap;

import java.util.Map;

import javafx.animation.Transition;

/**
 * The handler that sets the appearance of a node. This command is received from the client.
 */
public class SetNodeAppearanceCommandHandler extends CommandHandler {

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
        
        Node node;
        
        switch (format) {
        default: case JSON:
            Map<String, Object> map = CommandHandler.parseJson(data);
            if (!map.containsKey("id") || !map.containsKey("appearance")
                    || !(map.get("appearance") instanceof LazyValueMap)
                    /*|| !((LazyValueMap) map.get("appearance")).containsKey("type")*/) {
                throw new MissingDataException();
            }
            node = getController().getNode((int) map.get("id"));
            if (node == null) {
                throw new DataParseException("Unknown Node with id " + map.get("id"));
            }
            // New appearance: fade in.
            LazyValueMap appearance = (LazyValueMap) map.get("appearance");
            
            if (node.getAppearance() == null) {
                
                // Get new instance.
                VisualComponent vc = VisualComponent.instantiate((String) appearance.get("type"));
                if (vc == null) {
                    throw new DataParseException("An unknown appearance type was requested.");
                }
                
                // Link it to the Node.
                node.setOriginalAppearance(vc);
                node.setAppearance(vc);
                
                // Get the Transition from the visual component.
                Transition transition = vc.animateFromMap(appearance, 
                        VisualComponent.ChangeType.ADD_NODE, 
                        getController().getVisualizer().getCurrentAnimationDuration());
                
                // Add the visual component to the stage.
                getController().getVisualizer().executeOnCorrectThread(() -> {
                    getController().getVisualizer().getVisGroup()
                                   .getChildren().add((javafx.scene.Node) vc);
                });
                
                // Add a log entry.
                Log.add("Appearance of node " + node.getId() + " set.");
                
                
                // And put the visualization in the queue.
                getController().getVisualizer().addToVisualizationsQueue(transition);
                
            // The appearance was previously set, so we have to change its appearance.
            }  else {
                // Get VisualComponent instance.
                VisualComponent vc = node.getAppearance();
                
                // Get the Transition from the visual component.
                Transition transition = vc.animateFromMap(appearance, 
                        VisualComponent.ChangeType.NORMAL, 
                        getController().getVisualizer().getCurrentAnimationDuration());
                
                // Add a log entry.
                Log.add("Appearance of node " + node.getId() + " changed.");
                
                // And put the visualization in the queue.
                getController().getVisualizer().addToVisualizationsQueue(transition);
            }
        }
    }

}