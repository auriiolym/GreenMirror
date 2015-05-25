package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.Node;
import groovy.json.JsonOutput;

import java.util.LinkedHashMap;

/**
 * The command to remove a node. This command is sent to the server.
 * 
 * Values sent:
 * id : int        The node id
 */
public class RemoveNodeCommand extends Command {
    
    // -- Instance variables -----------------------------------------------------------------
    
    private Node node;

    
    // --- Constructors ----------------------------------------------------------------------

    /**
     * Create a new <tt>RemoveNodeCommand</tt>.
     * @param node The <tt>Node</tt> that will be removed from the visualizer.
     */
    //@ requires node != null;
    public RemoveNodeCommand(Node node) {
        this.node = node;
    }

    // --- Queries ---------------------------------------------------------------------------
    
    /**
     * @return The <tt>Node</tt> that will be removed from the visualizer.
     */
    //@ ensures \result != null;
    /*@ pure */ private Node getNode() {
        return node;
    }


    // -- Commands ---------------------------------------------------------------------------
    
    /* (non-Javadoc)
     * @see greenmirror.Command#prepare()
     */
    @Override
    public void prepare() {
        // Nothing to prepare.
    }
    
    /* (non-Javadoc)
     * @see greenmirror.Command#getFormattedString(greenmirror.CommunicationFormat)
     */
    @Override
    public String getFormattedString(CommunicationFormat format) {
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