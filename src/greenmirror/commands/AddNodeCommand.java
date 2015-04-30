package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import greenmirror.Node;
import groovy.json.JsonOutput;

import java.util.HashMap;

/**
 * The command to add a node. This command is sent to the server.
 * 
 * Values sent:
 * id : int        The node id
 */
public class AddNodeCommand extends Command {

    // -- Instance variables -----------------------------------------------------------------

    //@ private invariant node != null;
    private Node node;
    

    // -- Constructors -----------------------------------------------------------------------

    /**
     * Initialize the <tt>Command</tt>.
     * @param node The <tt>Node</tt> that has been added.
     */
    //@ requires node != null;
    //@ ensures getNode() == node;
    public AddNodeCommand(Node node) {
        this.node = node;
    }

    
    // -- Queries ----------------------------------------------------------------------------

    /**
     * @return The <tt>Node</tt> that has been added.
     */
    //@ ensures \result != null;
    /*@ pure */ public Node getNode() {
        return node;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    /**
     * Prepare the <tt>Command</tt>.
     */
    public void prepare() {
        // Nothing to prepare.
    }

    /**
     * Fetch the raw data that will be sent.
     * @param format The format in which the data will be.
     */
    //@ requires format != null;
    public String getFormattedString(CommunicationFormat format) {
        switch (format) {
        default: case JSON:
            return JsonOutput.toJson(new HashMap<String, Integer>() {
                {
                    put("id", getNode().getId());
                }
            });
        }
    }
}