package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.Node;
import groovy.json.JsonOutput;

import java.util.LinkedHashMap;

/**
 * The command to set the FX of a node. This command is sent to the server.
 * 
 * Values sent:
 * id : int             The node id
 * fx : FxWrapper     The values of the FX.
 */
public class SetNodeFxCommand extends Command {

    // -- Instance variables -----------------------------------------------------------------

    //@ private invariant node != null;
    private Node node;
    

    // -- Constructors -----------------------------------------------------------------------

    /**
     * Initialize the <code>Command</code>.
     * @param node The <code>Node</code> of which its appearance has been set.
     */
    //@ requires node != null;
    //@ ensures getNode() == node;
    public SetNodeFxCommand(Node node) {
        this.node = node;
    }

    
    // -- Queries ----------------------------------------------------------------------------

    /**
     * @return The <code>Node</code> of which its appearance has been set.
     */
    //@ ensures \result != null;
    /*@ pure */ public Node getNode() {
        return node;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    /**
     * Prepare the <code>Command</code>.
     */
    public void prepare() {
        // Nothing to prepare.
    }

    /**
     * Fetch the raw data that will be sent.
     * @param format The format in which the data will be.
     */
    public String getFormattedString(CommunicationFormat format) {
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