package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import greenmirror.Node;
import groovy.json.JsonOutput;

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

    //@ private invariant node != null;
    private Node node;
    

    // -- Constructors -----------------------------------------------------------------------

    /**
     * Initialize the <code>Command</code>.
     * @param node The <code>Node</code> that has been added.
     */
    //@ requires node != null;
    //@ ensures getNode() == node;
    public AddNodeCommand(Node node) {
        this.node = node;
    }

    
    // -- Queries ----------------------------------------------------------------------------

    /**
     * @return The <code>Node</code> that has been added.
     */
    //@ ensures \result != null;
    /*@ pure */ public Node getNode() {
        return node;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    /**
     * Prepare the <code>Command</code>.
     */
    @Override
    public void prepare() {
        // Nothing to prepare.
    }

    /**
     * Fetch the raw data that will be sent.
     * @param format The format in which the data will be.
     */
    //@ requires format != null;
    @Override
    public String getFormattedString(CommunicationFormat format) {
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