package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.ServerSide;
import greenmirror.server.ServerController;
import greenmirror.server.ToolbarButton;

import org.eclipse.jdt.annotation.NonNull;

/**
 * The handler that handles the signal that the visualization can start. This command is 
 * received from the client.
 * 
 * @author  Karim El Assal
 * @see     StartVisualizationCommand
 */
@ServerSide
public class StartVisualizationCommandHandler extends CommandHandler {

    
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public void handle(@NonNull CommunicationFormat format, @NonNull String data) 
            throws MissingDataException, DataParseException {
        
        Log.add("The visualization may start now.");
        ((ServerController) getController()).getVisualizer().updateMementoNumberInfo();
        ToolbarButton.STEP.action();
    }
}