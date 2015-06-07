package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.Node;
import greenmirror.ServerSide;
import org.eclipse.jdt.annotation.NonNull;

import java.util.Map;


/**
 * The handler that adds a node. This command is received from the client.
 * <p>
 * Expected data:
 * id : int              The node id
 * identifier : String   The node identifier
 * 
 * @author Karim El Assal
 */
@ServerSide
public class AddNodeCommandHandler extends CommandHandler {


    // -- Commands ---------------------------------------------------------------------------

    @Override
    public void handle(@NonNull CommunicationFormat format, @NonNull String data) 
            throws MissingDataException, DataParseException {
        
        int id;
        String identifier = "";
        
        switch (format) {
        default: case JSON:
            final Map<String, Object> map = CommandHandler.parseJson(data);
            if (!map.containsKey("id") || !map.containsKey("identifier")) {
                throw new MissingDataException();
            }
            try {
                id = Integer.valueOf(String.valueOf(map.get("id")));
                if (!(id >= 0)) {
                    throw new NumberFormatException();
                }
            } catch (NumberFormatException e) {
                throw new DataParseException("the received node id was not valid");
            }
            identifier = String.valueOf(map.get("identifier"));
        }

        // Create node.
        Node node = new Node(identifier);
        node.setId(id);
        
        // Add to the controller.
        getController().getNodes().add(node);
        
        Log.add("Node " + Log.n(node) + " added.");
    }

}