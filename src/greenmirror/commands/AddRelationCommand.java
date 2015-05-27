package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.Relation;
import groovy.json.JsonOutput;

import java.util.LinkedHashMap;

/**
 * The command to add a relation. This command is sent to the server.
 * 
 * Values sent:
 * name : String      The name of the relation
 * nodeA : int        The id of the first node.
 * nodeB : int        The id of the second node.
 * placement : String The placement data of node A on node B.
 * rigid : boolean    Whether the relation is rigid or not. This value is optional and defaults to
 *                    false.
 * tempFx :   FxWrapper        The temporary appearance of node A.
 */
public class AddRelationCommand extends Command {
    
    // --- Instance variables ----------------------------------------------------------------
    
    private Relation relation;
    

    // --- Constructors ----------------------------------------------------------------------
    
    /**
     * Create a new <tt>AddRelationCommand</tt>.
     * @param relation The newly created <tt>Relation</tt>.
     */
    public AddRelationCommand(Relation relation) {
        this.relation = relation;
    }

    // --- Queries ---------------------------------------------------------------------------
    
    /*@ pure */ private Relation getRelation() {
        return relation;
    }
    
    // --- Setters ---------------------------------------------------------------------------

    public void prepare() {
        // Nothing to prepare.
    }

    /**
     * Fetch the raw data that will be sent.
     * @param format The format in which the data will be.
     */
    //@ requires format != null;
    public String getFormattedString(CommunicationFormat format) {
        Log.add("Relation added: " + getRelation().toString());
        
        switch (format) {
        default: case JSON:
            return JsonOutput.toJson(new LinkedHashMap<String, Object>() {
                {
                    put("name", getRelation().getName());
                    put("nodeA", getRelation().getNodeA().getId());
                    put("nodeB", getRelation().getNodeB().getId());
                    put("placement", getRelation().getPlacement().toData());
                    put("rigid", getRelation().isRigid());
                    put("tempFx", getRelation().getTemporaryFxOfNodeA() == null
                            ? null : getRelation().getTemporaryFxOfNodeA().toMap());
                }
            });
        }
    }
}