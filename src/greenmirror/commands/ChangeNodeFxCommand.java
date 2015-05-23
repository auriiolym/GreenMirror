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
 * Empty values for the FxContainer are not sent.
 * 
 * Values sent:
 * id : int          The node id
 * fx : FxContainer  The new FX.
 * 
 * @author Karim El Assal
 */
public class ChangeNodeFxCommand extends Command {

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
    public ChangeNodeFxCommand(Node node) {
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
        Log.add("Node " + getNode().getId() + " FX changed to: " 
                + getNode().getFxContainer().toString());
        
        switch (format) {
        default: case JSON:
            Map<String, Object> fxMap = new LinkedHashMap<>();
            for (Map.Entry<String, Object> entry : getNode().getFxContainer().toMap().entrySet()) {
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
