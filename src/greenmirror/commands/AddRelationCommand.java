package greenmirror.commands;

import greenmirror.*;

/**
 * The command to add a relation. This command is sent to the server.
 * 
 * Values sent:
 * id : String        The id of the relation. This can be constructed from nodeAid-relationName-nodeBid. In any case, it must be a unique identifier.
 * nodeA : int        The id of the first node.
 * nodeB : int        The id of the second node.
 * rigid : boolean        Whether the relation is rigid or not. This value is optional and defaults to false.
 * temptAppearance : VisualComponent        The temporary appearance of node A.
 */
public class AddRelationCommand extends Command {

    /**
     * 
     * @param relation
     */
    public AddRelationCommand(Relation relation) {
        // TODO - implement AddRelationCommand.AddRelationCommand
        throw new UnsupportedOperationException();
    }

    public void prepare() {
        // TODO - implement AddRelationCommand.prepare
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param format
     */
    public String getFormattedString(CommunicationFormat format) {
        // TODO - implement AddRelationCommand.getFormattedString
        throw new UnsupportedOperationException();
    }

}