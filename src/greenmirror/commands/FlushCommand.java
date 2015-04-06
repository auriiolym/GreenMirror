package greenmirror.commands;

import greenmirror.*;

/**
 * The command to create a new sub-queue of visualizations. This command is sent to the server.
 * 
 * Values sent:
 * duration : int        The duration of the previous sub-queue of visualizations.
 */
public class FlushCommand extends Command {

    /**
     * 
     * @param duration
     */
    public FlushCommand(Duration duration) {
        // TODO - implement FlushCommand.FlushCommand
        throw new UnsupportedOperationException();
    }

    public void prepare() {
        // TODO - implement FlushCommand.prepare
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param format
     */
    public String getFormattedString(CommunicationFormat format) {
        // TODO - implement FlushCommand.getFormattedString
        throw new UnsupportedOperationException();
    }

}