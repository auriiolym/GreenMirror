package greenmirror.commands;

import greenmirror.*;

/**
 * The command to set the appearance of a node. This command is sent to the server.
 * 
 * Values sent:
 * id : int        The node id
 * appearance : VisualComponent        The new appearance.
 */
public class SetNodeAppearanceCommand extends Command {

    /**
     * 
     * @param node
     */
    public SetNodeAppearanceCommand(Node node) {
        // TODO - implement SetNodeAppearanceCommand.SetNodeAppearanceCommand
        throw new UnsupportedOperationException();
    }

    public void prepare() {
        // TODO - implement SetNodeAppearanceCommand.prepare
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param format
     */
    public String getFormattedString(CommunicationFormat format) {
        // TODO - implement SetNodeAppearanceCommand.getFormattedString
        throw new UnsupportedOperationException();
    }

}