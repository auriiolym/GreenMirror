package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.Node;
import groovy.json.JsonOutput;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * The command to change the FX of a node. This command is sent to the server.
 * Empty values for the FxWrapper are not sent.
 * 
 * Values sent:
 * id : int          The node id
 * fx : FxWrapper  The new FX.
 * 
 * @author Karim El Assal
 */
public class ChangeNodeFxCommand extends Command {

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
    public ChangeNodeFxCommand(Node node) {
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
     * Fetch the raw data that will be sent.
     * @param format The format in which the data will be.
     */
    //@ requires format != null;
    public String getFormattedString(CommunicationFormat format) {
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
