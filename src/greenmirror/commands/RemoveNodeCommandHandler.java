package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.Node;
import greenmirror.Relation;
import greenmirror.server.ServerController;
import greenmirror.server.Visualizer;

import java.util.Map;

import javafx.util.Duration;

/**
 * The handler that removes a node. This command is received from the client.
 */
@CommandHandler.ServerSide
public class RemoveNodeCommandHandler extends CommandHandler {


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


    /* (non-Javadoc)
     * @see greenmirror.CommandHandler#handle(greenmirror.CommunicationFormat, java.lang.String)
     */
    @Override
    public void handle(CommunicationFormat format, String data) 
            throws MissingDataException, DataParseException {


        final Node node;
        
        switch (format) {
        default: case JSON:
            
            // Check existence of data.
            Map<String, Object> map = CommandHandler.parseJson(data);
            if (!map.containsKey("id")) {
                throw new MissingDataException();
            }

            // Parse data.
            try {
                // Node.
                if ((node = getController().getNode(
                        Integer.parseInt(String.valueOf(map.get("id"))))) == null) {
                    throw new DataParseException("The node was not found on the visualizer.");
                }
            } catch (NumberFormatException e) {
                throw new DataParseException("The id of the node is invalid.");
            }
        }
        

        final Visualizer visualizer = getController().getVisualizer();
        /**
         * A node will be removed, so this is what will happen:
         * - All nodes that have a connection with this node and have a temporary FX set, will be
         *   reverted to their original FX.
         * - All relations will be removed.
         * - This node will get a fade out.
         */
        for (Relation relation : node.getRelations(-1)) {
            // Revert the temporary FX of node A.
            if (relation.getTemporaryFxOfNodeA() != null) {
                final Node nodeA = relation.getNodeA();
                getController().getVisualizer().changeFx(nodeA, 
                        nodeA.getFxWrapper().getOriginalFx().toMapWithoutPositionData());
                nodeA.getFxWrapper().saveAsOriginal();
            }
        }
        node.getRelations().removeAll();
        visualizer.addToVisualizationsQueue(
                node.getFxWrapper().animateOpacity(0.0, 
                        Duration.millis(visualizer.getCurrentAnimationDuration())));
        
        
        //TODO: check if we should replace the node (in the controller) by a NullNode.
        
        
    }

}