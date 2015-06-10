package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.Relation;
import groovy.json.JsonOutput;

import java.util.LinkedHashMap;

/**
 * The command to remove a relation. This command is sent to the server.
 * 
 * Values sent:
 * id : String        The relation id.
 * nodeA : int        Node A id.
 */
public class RemoveRelationCommand extends Command {
    
    // --- Instance variables ----------------------------------------------------------------
    
    private Relation relation;
    

    // --- Constructors ----------------------------------------------------------------------

    /**
     * Create a new <code>RemoveRelationCommand</code>.
     * @param relation The <code>Relation</code> to be removed.
     */
    //@ requires relation != null;
    public RemoveRelationCommand(Relation relation) {
        this.relation = relation;
    }

    // --- Queries ---------------------------------------------------------------------------
    
    /*@ pure */ private Relation getRelation() {
        return relation;
    }
    
    // --- Setters ---------------------------------------------------------------------------

    /**
     * Fetch the raw data that will be sent.
     * @param format The format in which the data will be.
     */
    //@ requires format != null;
    public String getFormattedString(CommunicationFormat format) {
        Log.add("Relation removed: " + getRelation().toString());
        
        switch (format) {
        default: case JSON:
            return JsonOutput.toJson(new LinkedHashMap<String, Object>() {
                {
                    put("id", getRelation().getId());
                    put("nodeA", getRelation().getNodeA().getId());
                }
            });
        }
    }

}