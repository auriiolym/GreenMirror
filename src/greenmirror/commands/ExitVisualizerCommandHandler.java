package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.ServerSide;
import greenmirror.server.ServerController;

/**
 * The handler that handles the signal that we're at the end of a transition. 
 * This command is received from the client.
 * 
 * @author Karim El Assal
 */
@ServerSide
public class ExitVisualizerCommandHandler extends CommandHandler {

    
    // -- Commands ---------------------------------------------------------------------------

    /**
     * Handle the received command. 
     * @param format The format in which the data is received.
     * @param data   The (raw) received data.
     * @throws MissingDataException When the data is incomplete.
     * @throws DataParseException   When parsing the data went wrong.
     */
    //@ requires getController() != null && format != null && data != null;
    public void handle(CommunicationFormat format, String data) 
            throws MissingDataException, DataParseException {

        ((ServerController) getController()).getVisualizer().executeOnCorrectThread(() -> {
            Log.add("Exit command reveived from the client.");
            ((ServerController) getController()).getVisualizer().getStage().close();
        });
    }
}