package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.ServerSide;
import greenmirror.server.ServerController;
import org.eclipse.jdt.annotation.NonNull;

import java.util.Map;


/**
 * The handler that sets the duration for the upcoming animations. This command is received from
 * the client.
 * 
 * @author  Karim El Assal
 * @see     SetAnimationDurationCommand
 */
@ServerSide
public class SetAnimationDurationCommandHandler extends CommandHandler {
    
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public void handle(@NonNull CommunicationFormat format, @NonNull String data) 
            throws MissingDataException, DataParseException {
        
        final double duration;
        
        switch (format) {
        default: case JSON:
            final Map<String, Object> map = CommandHandler.parseJson(data);
            // Check data existence.
            if (!map.containsKey("duration")) {
                throw new MissingDataException();
            }
            
            // Parse data.
            try {
                duration = Double.valueOf(String.valueOf(map.get("duration")));
                if (!(duration >= -1.0)) {
                    throw new NumberFormatException();
                }
            } catch (NumberFormatException e) {
                throw new DataParseException("the duration is invalid: " + map.get("duration"));
            }
        }

        ((ServerController) getController()).getVisualizer().setCurrentAnimationDuration(duration);
        Log.add("Current animation duration set to " + duration + "ms.");
    }
}
