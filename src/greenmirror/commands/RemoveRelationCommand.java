package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.Relation;
import groovy.json.JsonOutput;

import org.eclipse.jdt.annotation.NonNull;

import java.util.LinkedHashMap;

/**
 * The command to remove a relation. This command is sent to the server.
 * 
 * <table><caption>Values sent:</caption>
 * <tr><th>variable</th><th>type</th><th>description</th></tr>
 * <tr><td>id </td><td>String</td><td>      the relation id
 * <tr><td>nodeA </td><td>int</td><td>      the id of node A
 * </table>
 * 
 * @author  Karim El Assal
 * @see     RemoveRelationCommandHandler
 */
public class RemoveRelationCommand extends Command {
    
    // --- Instance variables ----------------------------------------------------------------
    
    @NonNull private Relation relation;
    

    // --- Constructors ----------------------------------------------------------------------

    /**
     * Initializes this {@link greenmirror.Command}.
     * 
     * @param relation the relation to be removed
     */
    public RemoveRelationCommand(@NonNull Relation relation) {
        this.relation = relation;
    }

    // --- Queries ---------------------------------------------------------------------------
    
    /** @return the relation that will be removed */
    /*@ pure */ @NonNull private Relation getRelation() {
        return relation;
    }
    
    // --- Setters ---------------------------------------------------------------------------

    @Override
    public String getFormattedString(@NonNull CommunicationFormat format) {
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