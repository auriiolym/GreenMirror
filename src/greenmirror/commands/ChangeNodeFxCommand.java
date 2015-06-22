package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.Node;
import groovy.json.JsonOutput;

import org.eclipse.jdt.annotation.NonNull;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * The command to change the FX of a node. This command is sent to the server.
 * Null values for the FxWrapper are not sent.
 * 
 * <table><caption>Values sent:</caption>
 * <tr><th>variable</th><th>type</th><th>description</th></tr>
 * <tr><td>id </td><td>int</td><td>the node id</td></tr>
 * <tr><td>fx </td><td>FxWrapper</td><td>the new FX</td></tr>
 * </table>
 * 
 * @author Karim El Assal
 * @see ChangeNodeFxCommandHandler
 */
public class ChangeNodeFxCommand extends Command {

    // -- Instance variables -----------------------------------------------------------------

    @NonNull private Node node;
    

    // -- Constructors -----------------------------------------------------------------------

    /**
     * Initializes this {@link greenmirror.Command}.
     * 
     * @param node the node that has been added
     */
    //@ ensures getNode() == node;
    public ChangeNodeFxCommand(@NonNull Node node) {
        this.node = node;
    }

    
    // -- Queries ----------------------------------------------------------------------------

    /** @return the node that has been added */
    /*@ pure */ @NonNull public Node getNode() {
        return node;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public String getFormattedString(@NonNull CommunicationFormat format) {
        Log.add("Node " + Log.n(getNode()) + " FX changed to: " 
                + getNode().getFxWrapper().toString());
        
        switch (format) {
        default: case JSON:
            final Map<String, Object> fxMap = new LinkedHashMap<String, Object>();
            for (Map.Entry<String, Object> entry : getNode().getFxWrapper().toMap().entrySet()) {
                if (entry.getValue() != null) {
                    fxMap.put(entry.getKey(), entry.getValue());
                }
            }
            
            return JsonOutput.toJson(new LinkedHashMap<String, Object>() {
                {
                    put("id", getNode().getId());
                    put("fx", fxMap);
                }
            });
        }
    }
}
