package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.Node;
import groovy.json.JsonOutput;

import org.eclipse.jdt.annotation.NonNull;

import java.util.LinkedHashMap;

/**
 * The command to set the FX of a node. This command is sent to the server.
 * 
 * <table><caption>Values sent:</caption>
 * <tr><th>variable</th><th>type</th><th>description</th></tr>
 * <tr><td>id </td><td>int</td><td>         the node id</td></tr>
 * <tr><td>fx </td><td>FxWrapper</td><td>   the values of the FX</td></tr>
 * </table>
 * 
 * @author  Karim El Assal
 * @see     SetNodeFxCommandHandler
 */
public class SetNodeFxCommand extends Command {

    // -- Instance variables -----------------------------------------------------------------

    @NonNull private Node node;
    

    // -- Constructors -----------------------------------------------------------------------

    /**
     * Initializes this {@link greenmirror.Command}.
     *
     * @param node the node of which its appearance will be set
     */
    //@ ensures getNode() == node;
    public SetNodeFxCommand(@NonNull Node node) {
        this.node = node;
    }

    
    // -- Queries ----------------------------------------------------------------------------

    /** @return the node of which its appearance will be set */
    /*@ pure */ @NonNull public Node getNode() {
        return node;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public String getFormattedString(@NonNull CommunicationFormat format) {
        Log.add("Node " + Log.n(getNode()) + " FX set: " + getNode().getFxWrapper().toString());
        
        switch (format) {
        default: case JSON:
            return JsonOutput.toJson(new LinkedHashMap<String, Object>() {
                {
                    put("id", getNode().getId());
                    put("fx", getNode().getFxWrapper() == null 
                                ? null : getNode().getFxWrapper().toMap());
                }
            });
        }
    }
}