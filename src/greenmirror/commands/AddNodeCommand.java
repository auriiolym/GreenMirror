package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import greenmirror.Node;
import groovy.json.JsonOutput;
import org.eclipse.jdt.annotation.NonNull;

import java.util.LinkedHashMap;


/**
 * The command to add a node. This command is sent to the server.
 * 
 * Values sent:
 * id : int              The node id
 * identifier : String   The node identifier
 */
public class AddNodeCommand extends Command {

    // -- Instance variables -----------------------------------------------------------------

    @NonNull private Node node;
    

    // -- Constructors -----------------------------------------------------------------------

    /**
     * Initializes the <code>Command</code>.
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

    /**
     * Fetch the raw data that will be sent.
     * 
     * @param format The format in which the data will be.
     */
    @Override
    public String getFormattedString(@NonNull CommunicationFormat format) {
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