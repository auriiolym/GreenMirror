package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.Node;
import greenmirror.server.ServerController;

import java.util.Map;

/**
 * The handler that adds a node. This command is received from the client.
 */
@CommandHandler.ServerSide
public class AddNodeCommandHandler extends CommandHandler {

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
        
        int id;
        String identifier = "";
        
        switch (format) {
        default: case JSON:
            Map<String, Object> map = CommandHandler.parseJson(data);
            if (!map.containsKey("id") || !map.containsKey("identifier")) {
                throw new MissingDataException();
            }
            try {
                id = Integer.valueOf(String.valueOf(map.get("id")));
                if (!(id >= 0)) {
                    throw new NumberFormatException();
                }
            } catch (NumberFormatException e) {
                throw new DataParseException("The passed node id was not valid.");
            }
            identifier = String.valueOf(map.get("identifier"));
        }

        Node node = new Node(identifier);
        node.setId(id);
        getController().getNodes().add(node);
        Log.add("Node (" + id + "," + identifier + ") added.");
    }

}