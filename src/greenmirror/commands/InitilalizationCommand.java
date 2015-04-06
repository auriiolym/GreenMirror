package greenmirror.commands;

import greenmirror.*;

/**
 * The command to initialize the visualizer. This command is sent to the server.
 * 
 * Values sent:
 * width : int        The width of the window.
 * height : int        The height of the window.
 * defaultTransitionTime : int        The default time transitions will take. This value is optional and defaults to the sum of the included "sub-"transitions.
 */
public class InitilalizationCommand extends Command {

    /**
     * 
     * @param width
     * @param height
     */
    public void InitializeCommand(double width, double height) {
        // TODO - implement InitilalizationCommand.InitializeCommand
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param width
     * @param height
     * @param defaultTransitionTime
     */
    public void InitializeCommand(double width, double height, Duration defaultTransitionTime) {
        // TODO - implement InitilalizationCommand.InitializeCommand
        throw new UnsupportedOperationException();
    }

    public void prepare() {
        // TODO - implement InitilalizationCommand.prepare
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param format
     */
    public String getFormattedString(CommunicationFormat format) {
        // TODO - implement InitilalizationCommand.getFormattedString
        throw new UnsupportedOperationException();
    }

}