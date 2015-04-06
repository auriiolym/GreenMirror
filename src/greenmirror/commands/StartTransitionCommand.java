package greenmirror.commands;

import greenmirror.*;

/**
 * The command to start all visualizations that are in the queue. This command is sent to the server.
 * 
 * Values sent:
 * duration : int        The total duration of the transition. This value is optional and defaults to the sum of the durations of all sub-transitions.
 */
public class StartTransitionCommand extends Command {

    /**
     * 
     * @param duration
     */
    public StartTransitionCommand(Duration duration) {
        // TODO - implement StartTransitionCommand.StartTransitionCommand
        throw new UnsupportedOperationException();
    }

    public StartTransitionCommand() {
        // TODO - implement StartTransitionCommand.StartTransitionCommand
        throw new UnsupportedOperationException();
    }

    public void prepare() {
        // TODO - implement StartTransitionCommand.prepare
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param format
     */
    public String getFormattedString(CommunicationFormat format) {
        // TODO - implement StartTransitionCommand.getFormattedString
        throw new UnsupportedOperationException();
    }

}