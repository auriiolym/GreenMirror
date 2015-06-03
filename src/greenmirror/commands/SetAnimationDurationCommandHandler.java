package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.ServerSide;
import greenmirror.server.ServerController;

import java.util.Map;

/**
 * The handler that sets the duration for the following animations. This command is received from
 * the client.
 * 
 * @author Karim El Assal
 */
@ServerSide
public class SetAnimationDurationCommandHandler extends CommandHandler {

    // -- Queries ----------------------------------------------------------------------------
    
    /* (non-Javadoc)
     * @see greenmirror.CommandHandler#getController()
     */
    @Override
    //@ ensures \result != null;
    /*@ pure */ public ServerController getController() {
        return (ServerController) super.getController();
    }

    
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
        
        double duration;
        
        switch (format) {
        default: case JSON:
            Map<String, Object> map = CommandHandler.parseJson(data);
            if (!map.containsKey("duration")) {
                throw new MissingDataException();
            }
            try {
                duration = Double.valueOf(String.valueOf(map.get("duration")));
                if (!(duration >= -1.0)) {
                    throw new NumberFormatException();
                }
            } catch (NumberFormatException e) {
                throw new DataParseException("The passed duration was not valid.");
            }
        }

        getController().getVisualizer().setCurrentAnimationDuration(duration);
        Log.add("Current animation duration set to " + duration + "ms.");
    }
}
