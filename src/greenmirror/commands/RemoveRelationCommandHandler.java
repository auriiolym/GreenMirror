package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Node;
import greenmirror.Relation;
import greenmirror.server.ServerController;

import java.util.Map;

/**
 * The handler that removes a relation. This command is received from the client.
 */
@CommandHandler.ServerSide
public class RemoveRelationCommandHandler extends CommandHandler {


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


        final Relation relation;
        final Node nodeA;
        
        switch (format) {
        default: case JSON:
            
            // Check existence of data.
            Map<String, Object> map = CommandHandler.parseJson(data);
            if (!map.containsKey("id") || !map.containsKey("nodeA")) {
                throw new MissingDataException();
            }

            // Parse data.
            // Relation id.
            final String id = String.valueOf(map.get("id"));
            try {
                // node A
                if ((nodeA = getController().getNode(
                        Integer.parseInt(String.valueOf(map.get("nodeA"))))) == null) {
                    throw new DataParseException("Node A was not found on the visualizer.");
                }
            } catch (NumberFormatException e) {
                throw new DataParseException("The id of node A is invalid.");
            }
            
            // Create the Relation object.
            relation = nodeA.getRelations().withId(id).getFirst();
        }
        

        
        // Revert the temporary FX of node A.
        if (relation.getTemporaryFxOfNodeA() != null) {
            getController().getVisualizer().changeFx(nodeA, 
                    nodeA.getFxContainer().getOriginalFx().toMapWithoutPositionData());
            nodeA.getFxContainer().saveAsOriginal();
        }
        
        // Remove the relation.
        relation.removeFromNodes();
    }

}