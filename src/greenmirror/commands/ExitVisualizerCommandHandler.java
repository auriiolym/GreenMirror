package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.ServerSide;
import greenmirror.server.ServerController;
import greenmirror.server.Visualizer;

import org.eclipse.jdt.annotation.NonNull;

/**
 * The handler that handles the signal that the visualizer should terminate. 
 * This command is received from the client.
 * 
 * @author  Karim El Assal
 * @see     ExitVisualizerCommand
 */
@ServerSide
public class ExitVisualizerCommandHandler extends CommandHandler {

    
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public void handle(@NonNull CommunicationFormat format, @NonNull String data) 
            throws MissingDataException, DataParseException {
        
        final Visualizer visualizer = ((ServerController) getController()).getVisualizer(); 

        visualizer.executeOnCorrectThread(() -> {
            Log.add("Exit command reveived from the client.");
            if (visualizer.getStage() != null) {
                visualizer.getStage().close();
            }
        });
    }
}