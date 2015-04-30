package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;

/**
 * The command to signal that the server has encountered an error. 
 * This command is sent to the client.
 * 
 * Values sent:
 * code : int        The error code
 * info : String        Extra error information.
 */
public class ServerErrorCommand extends Command {

    public void prepare() {
        // TODO - implement ServerErrorCommand.prepare
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param format
     */
    public String getFormattedString(CommunicationFormat format) {
        // TODO - implement ServerErrorCommand.getFormattedString
        throw new UnsupportedOperationException();
    }

}