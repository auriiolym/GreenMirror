package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.Node;
import greenmirror.ServerSide;
import greenmirror.server.ServerController;
import groovy.json.internal.LazyValueMap;

import org.eclipse.jdt.annotation.NonNull;

import java.util.LinkedHashMap;
import java.util.Map;


/**
 * The handler that notifies the server that the FX of a node should be changed. This command 
 * is received from the client.
 * 
 * @author  Karim El Assal
 * @see     ChangeNodeFxCommand
 */
@ServerSide
public class ChangeNodeFxCommandHandler extends CommandHandler {
    
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public void handle(@NonNull CommunicationFormat format, @NonNull String data) 
            throws MissingDataException, DataParseException {
        
        final Node node;
        final Map<String, Object> fxMap = new LinkedHashMap<>();
        
        switch (format) {
        default: case JSON:
            final Map<String, Object> map = CommandHandler.parseJson(data);
            // Check data existence.
            if (!map.containsKey("id") || !map.containsKey("fx")
                    || !(map.get("fx") instanceof LazyValueMap)) {
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
            
            // FX.
            fxMap.putAll((LazyValueMap) map.get("fx"));
            break;
        }
        
        // We're assuming here that the FX of the node has previously been set (using 
        //  SetNodeFxCommand).
        ((ServerController) getController()).getVisualizer().changeFx(node, fxMap);
        
        // Add to log.
        Log.add("FX of node " + Log.n(node) + " changed to: " + fxMap.toString());
    }
}
