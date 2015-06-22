package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.Relation;
import groovy.json.JsonOutput;

import org.eclipse.jdt.annotation.NonNull;

import java.util.LinkedHashMap;

/**
 * The command to switch a relation. This command is sent to the server.
 * 
 * <table><caption>Values sent:</caption>
 * <tr><th>variable</th><th>type</th><th>description</th></tr>
 * <tr><td>oldId </td><td>String</td><td>           the unique id of the old relation</td></tr>
 * <tr><td>name </td><td>String</td><td>    the name of the new relation</td></tr>
 * <tr><td>nodeA </td><td>int</td><td>      the id of the first node</td></tr>
 * <tr><td>nodeB </td><td>int</td><td>      the id of the second node</td></tr>
 * <tr><td>placement </td><td>String</td><td>the placement data of node A on node B</td></tr>
 * <tr><td>rigid </td><td>boolean</td><td>          whether the new relation is rigid or not. 
 *                                          This value is optional and defaults to false</td></tr>
 * <tr><td>tempFx </td><td>FxWrapper</td><td>the temporary appearance of node A</td></tr>
 * </table>
 * 
 * @author  Karim El Assal
 * @see     SwitchPlacementRelationCommandHandler
 */
public class SwitchPlacementRelationCommand extends Command {
    
    // --- Instance variables ----------------------------------------------------------------
    
    @NonNull private Relation oldRelation;
    @NonNull private Relation newRelation;
    

    // --- Constructors ----------------------------------------------------------------------
    
    /**
     * Initializes this {@link greenmirror.Command}.
     * 
     * @param oldRelation the old relation
     * @param newRelation the new relation
     */
    public SwitchPlacementRelationCommand(@NonNull Relation oldRelation, 
                                          @NonNull Relation newRelation) {
        this.oldRelation = oldRelation;
        this.newRelation = newRelation;
    }

    // --- Queries ---------------------------------------------------------------------------
    
    /*@ pure */ @NonNull private Relation getOldRelation() {
        return this.oldRelation;
    }
    
    /*@ pure */ @NonNull private Relation getNewRelation() {
        return this.newRelation;
    }
    
    // --- Setters ---------------------------------------------------------------------------

    @Override
    public String getFormattedString(@NonNull CommunicationFormat format) {
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