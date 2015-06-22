package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.Node;
import groovy.json.JsonOutput;

import org.eclipse.jdt.annotation.NonNull;

import java.util.LinkedHashMap;

/**
 * The command to remove a node. This command is sent to the server.
 * 
 * <table><caption>Values sent:</caption>
 * <tr><th>variable</th><th>type</th><th>description</th></tr>
 * <tr><td>id </td><td>int</td><td>      the node id</td></tr>
 * </table>
 * 
 * @author  Karim El Assal
 * @see     RemoveNodeCommandHandler
 */
public class RemoveNodeCommand extends Command {
    
    // -- Instance variables -----------------------------------------------------------------
    
    @NonNull private Node node;

    
    // --- Constructors ----------------------------------------------------------------------

    /**
     * Initializes this {@link greenmirror.Command}.
     * 
     * @param node the node that will be removed from the visualizer
     */
    public RemoveNodeCommand(@NonNull Node node) {
        this.node = node;
    }

    // --- Queries ---------------------------------------------------------------------------
    
    /** @return the node that will be removed from the visualizer */
    /*@ pure */ @NonNull private Node getNode() {
        return node;
    }


    // -- Commands ---------------------------------------------------------------------------
    
    @Override
    public String getFormattedString(@NonNull CommunicationFormat format) {
        Log.add("Node removed: " + getNode().toString());
        
        switch (format) {
        default: case JSON:
            return JsonOutput.toJson(new LinkedHashMap<String, Object>() {
                {
                    put("id", getNode().getId());
                }
            });
        }
    }
}