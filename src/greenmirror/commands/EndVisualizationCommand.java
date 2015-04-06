package greenmirror.commands;

import greenmirror.*;

/**
 * The command to signal that the complete visualization has ended. This command is sent to the server.
 * 
 * Values sent:
 * status : int        The status code that indicates the reason for the ending of the complete visualization.
 */
public class EndVisualizationCommand extends Command {

    /**
     * 
     * @param status
     */
    public EndVisualizationCommand(int status) {
        // TODO - implement EndVisualizationCommand.EndVisualizationCommand
        throw new UnsupportedOperationException();
    }

    public void prepare() {
        // TODO - implement EndVisualizationCommand.prepare
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param format
     */
    public String getFormattedString(CommunicationFormat format) {
        // TODO - implement EndVisualizationCommand.getFormattedString
        throw new UnsupportedOperationException();
    }

}