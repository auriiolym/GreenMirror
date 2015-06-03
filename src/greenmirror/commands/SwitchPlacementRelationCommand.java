package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.Relation;
import groovy.json.JsonOutput;

import java.util.LinkedHashMap;

/**
 * The command to switch a relation. This command is sent to the server.
 * 
 * Values sent:
 * oldId : String     The unique id of the old relation.
 * name : String      The name of the new relation
 * nodeA : int        The id of the first node.
 * nodeB : int        The id of the second node.
 * placement : String The placement data of node A on node B.
 * rigid : boolean    Whether the relation is rigid or not. This value is optional and 
 *                    defaults to false.
 * tempFx : FxWrapper        The temporary appearance of node A.
 */
public class SwitchPlacementRelationCommand extends Command {
    
    // --- Instance variables ----------------------------------------------------------------
    
    private Relation oldRelation;
    private Relation newRelation;
    

    // --- Constructors ----------------------------------------------------------------------
    
    /**
     * Create a new <code>AddRelationCommand</code>.
     * @param oldRelation The old <code>Relation</code>.
     * @param newRelation The new <code>Relation</code>.
     */
    //@ requires oldRelation != null && newRelation != null;
    public SwitchPlacementRelationCommand(Relation oldRelation, Relation newRelation) {
        this.oldRelation = oldRelation;
        this.newRelation = newRelation;
    }

    // --- Queries ---------------------------------------------------------------------------
    
    /*@ pure */ private Relation getOldRelation() {
        return this.oldRelation;
    }
    
    /*@ pure */ private Relation getNewRelation() {
        return this.newRelation;
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
        Log.add("Placement relation switched to: " + getNewRelation().toString());
        
        switch (format) {
        default: case JSON:
            return JsonOutput.toJson(new LinkedHashMap<String, Object>() {
                {
                    put("oldId", getOldRelation().getId());
                    put("name", getNewRelation().getName());
                    put("nodeA", getNewRelation().getNodeA().getId());
                    put("nodeB", getNewRelation().getNodeB().getId());
                    put("placement", getNewRelation().getPlacement().toData());
                    put("rigid", getNewRelation().isRigid());
                    put("tempFx", getNewRelation().getTemporaryFxOfNodeA() == null
                            ? null : getNewRelation().getTemporaryFxOfNodeA().toMap());
                }
            });
        }
    }
}