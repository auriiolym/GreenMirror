package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.Relation;
import groovy.json.JsonOutput;

import org.eclipse.jdt.annotation.NonNull;

import java.util.LinkedHashMap;

/**
 * The command to add a relation. This command is sent to the server.
 * 
 * <table><caption>Values sent:</caption>
 * <tr><th>variable</th><th>type</th><th>description</th></tr>
 * <tr><td>name </td><td>String</td><td>      the name of the relation</td></tr>
 * <tr><td>nodeA </td><td>int</td><td>        the id of the first node</td></tr>
 * <tr><td>nodeB </td><td>int</td><td>        the id of the second node</td></tr>
 * <tr><td>placement </td><td>String</td><td> the placement data of node A on node B</td></tr>
 * <tr><td>rigid </td><td>boolean</td><td>    whether the relation is rigid or not. This value is 
 *                                            optional and defaults to false</td></tr>
 * <tr><td>tempFx </td><td>FxWrapper </td><td>the temporary appearance of node A; null if it is 
 *                                            not set</td></tr>
 * </table>
 * 
 * @author  Karim El Assal
 * @see     AddRelationCommandHandler
 */
public class AddRelationCommand extends Command {
    
    // --- Instance variables ----------------------------------------------------------------
    
    @NonNull private Relation relation;
    

    // --- Constructors ----------------------------------------------------------------------
    
    /**
     * Initializes this {@link greenmirror.Command}.
     * 
     * @param relation the newly created {@link Relation}
     */
    public AddRelationCommand(@NonNull Relation relation) {
        this.relation = relation;
    }

    // --- Queries ---------------------------------------------------------------------------
    
    /** @return the newly created relation */
    /*@ pure */ @NonNull private Relation getRelation() {
        return relation;
    }
    
    // --- Setters ---------------------------------------------------------------------------

    @Override 
    public String getFormattedString(@NonNull CommunicationFormat format) {
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