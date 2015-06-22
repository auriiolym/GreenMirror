package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.Node;
import groovy.json.JsonOutput;

import org.eclipse.jdt.annotation.NonNull;

import java.util.LinkedHashMap;


/**
 * The command to add a node. This command is sent to the server.
 * 
 * <table><caption>Values sent:</caption>
 * <tr><th>variable</th><th>type</th><th>description</th></tr>
 * <tr><td>id</td><td>int</td><td>the node id</td></tr>
 * <tr><td>identifier </td><td>String</td><td>the node identifier</td></tr>
 * </table>
 * 
 * @author Karim El Assal
 * @see    AddNodeCommandHandler
 */
public class AddNodeCommand extends Command {

    // -- Instance variables -----------------------------------------------------------------

    @NonNull private Node node;
    

    // -- Constructors -----------------------------------------------------------------------

    /**
     * Initializes this {@link greenmirror.Command}.
     * 
     * @param node The <code>Node</code> that has been added.
     */
    //@ ensures getNode() == node;
    public AddNodeCommand(@NonNull Node node) {
        this.node = node;
    }

    
    // -- Queries ----------------------------------------------------------------------------

    /** @return the <code>Node</code> that has been added */
    /*@ pure */ @NonNull public Node getNode() {
        return node;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public String getFormattedString(@NonNull CommunicationFormat format) {
        Log.add("Node added: " + getNode().toString());
        
        switch (format) {
        default: case JSON:
            return JsonOutput.toJson(new LinkedHashMap<String, Object>() {
                {
                    put("id", getNode().getId());
                    put("identifier", getNode().getIdentifier());
                }
            });
        }
    }
}