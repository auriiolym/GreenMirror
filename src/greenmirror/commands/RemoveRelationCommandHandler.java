package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.Node;
import greenmirror.Relation;
import greenmirror.ServerSide;
import greenmirror.server.ServerController;

import org.eclipse.jdt.annotation.NonNull;

import java.util.Map;

/**
 * The handler that removes a relation. This command is received from the client.
 * 
 * @author  Karim El Assal
 * @see     RemoveRelationCommand
 */
@ServerSide
public class RemoveRelationCommandHandler extends CommandHandler {
    
    
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public void handle(@NonNull CommunicationFormat format, @NonNull String data) 
            throws MissingDataException, DataParseException {


        final Relation relation;
        final Node nodeA;
        
        switch (format) {
        default: case JSON:
            
            // Check data existence.
            final Map<String, Object> map = CommandHandler.parseJson(data);
            if (!map.containsKey("id") || !map.containsKey("nodeA")) {
                throw new MissingDataException();
            }

            // Parse data.
            // Relation id.
            final String id = String.valueOf(map.get("id"));
            if (id == null) {
                throw new DataParseException("relation id is invalid");
            }
            try {
                // Node A.
                nodeA = getController().getNode(Integer.parseInt(String.valueOf(map.get("nodeA"))));
            } catch (NumberFormatException e) {
                throw new DataParseException("the id of node A is invalid");
            } catch (IllegalArgumentException e) {
                throw new DataParseException("node A is not found on the visualizer");
            }
            
            // Get the Relation instance.
            relation = nodeA.getRelations().withId(id).getFirst();
        }
        
        // Add log entry.
        Log.add("Relation removed: " + relation.toString());
        

        // Revert the temporary FX of node A.
        if (relation.getTemporaryFxOfNodeA() != null) {
            ((ServerController) getController()).getVisualizer().changeFx(nodeA, 
                    nodeA.getFxWrapper().getOriginalFxWrapper().toMapWithoutPositionData());
            nodeA.getFxWrapper().saveAsOriginal();
        }
        
        // Remove the relation.
        relation.removeFromNodes();
    }

}