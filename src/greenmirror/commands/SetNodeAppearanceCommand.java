package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import greenmirror.Node;
import groovy.json.JsonOutput;

import java.util.HashMap;
import java.util.Map;

/**
 * The command to set the appearance of a node. This command is sent to the server.
 * 
 * Values sent:
 * id : int        The node id
 * appearance : VisualComponent        The changed values of the appearance.
 */
public class SetNodeAppearanceCommand extends Command {

    // -- Instance variables -----------------------------------------------------------------

    //@ private invariant node != null;
    private Node node;
    
    //TODO: define a getter.
    private Map<String, Object> changedValues;
    

    // -- Constructors -----------------------------------------------------------------------

    /**
     * Initialize the <tt>Command</tt>.
     * @param node The <tt>Node</tt> of which its appearance has been set.
     */
    //@ requires node != null;
    //@ ensures getNode() == node;
    public SetNodeAppearanceCommand(Node node, Map<String, Object> changedValues) {
        this.node = node;
        this.changedValues = changedValues;
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
        switch (format) {
        default: case JSON:
            return JsonOutput.toJson(new HashMap<String, Object>() {
                {
                    put("id", getNode().getId());
                    if (getNode().getAppearance() == null) {
                        put("appearance", null);
                    } else {
                        //put("appearance", getNode().getAppearance().toMap());
                        put("appearance", changedValues);
                    }
                }
            });
        }
    }
}