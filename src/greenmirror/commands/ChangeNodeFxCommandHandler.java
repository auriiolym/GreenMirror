package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Node;
import greenmirror.server.ServerController;
import groovy.json.internal.LazyValueMap;

import java.util.HashMap;
import java.util.Map;


/**
 * The handler that notifies the server that the FX of node should be changed. This command 
 * is received from the client.
 * 
 * @author Karim El Assal
 */
public class ChangeNodeFxCommandHandler extends CommandHandler {

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
        Map<String, Object> fxMap = new HashMap<>();
        
        switch (format) {
        default: case JSON:
            Map<String, Object> map = CommandHandler.parseJson(data);
            if (!map.containsKey("id") || !map.containsKey("fx")
                    || !(map.get("fx") instanceof LazyValueMap)) {
                throw new MissingDataException();
            }
            node = getController().getNode((int) map.get("id"));
            if (node == null) {
                throw new DataParseException("Unknown Node with id " + map.get("id"));
            }
            
            fxMap.putAll((LazyValueMap) map.get("fx"));
            break;
        }
        
        // We're assuming here that the FX of the Node has been set.
        
        getController().getVisualizer().changeFx(node, fxMap);
    }
}
