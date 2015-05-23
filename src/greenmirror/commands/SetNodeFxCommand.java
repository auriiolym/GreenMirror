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
 * fx : FxContainer     The values of the FX.
 */
public class SetNodeFxCommand extends Command {

    // -- Instance variables -----------------------------------------------------------------

    //@ private invariant node != null;
    private Node node;
    

    // -- Constructors -----------------------------------------------------------------------

    /**
     * Initialize the <tt>Command</tt>.
     * @param node The <tt>Node</tt> of which its appearance has been set.
     */
    //@ requires node != null;
    //@ ensures getNode() == node;
    public SetNodeFxCommand(Node node) {
        this.node = node;
    }

    
    // -- Queries ----------------------------------------------------------------------------

    /**
     * @return The <tt>Node</tt> of which its appearance has been set.
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
    public String getFormattedString(CommunicationFormat format) {
        Log.add("Node " + Log.n(getNode()) + " FX set: " + getNode().getFxContainer().toString());
        
        switch (format) {
        default: case JSON:
            return JsonOutput.toJson(new LinkedHashMap<String, Object>() {
                {
                    put("id", getNode().getId());
                    put("fx", getNode().getFxContainer() == null 
                                ? null : getNode().getFxContainer().toMap());
                }
            });
        }
    }
}