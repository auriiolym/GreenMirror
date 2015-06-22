package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.ServerSide;
import greenmirror.server.ServerController;

import org.eclipse.jdt.annotation.NonNull;

import java.util.Map;

import javafx.animation.ParallelTransition;
import javafx.animation.PauseTransition;
import javafx.animation.SequentialTransition;
import javafx.util.Duration;

/**
 * The handler that creates a new sub-queue of visualizations. This command is received 
 * from the client.
 * 
 * @author  Karim El Assal
 * @see     FlushCommand
 */
@ServerSide
public class FlushCommandHandler extends CommandHandler {
    
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public void handle(@NonNull CommunicationFormat format, @NonNull String data) 
            throws MissingDataException, DataParseException {
        
        final double delay;
        
        switch (format) {
        default: case JSON:
            final Map<String, Object> map = CommandHandler.parseJson(data);
            
            // Check data existence.
            if (!map.containsKey("delay")) {
                throw new MissingDataException();
            }
            
            // Parse data.
            try {
                // Delay.
                delay = Double.valueOf(String.valueOf(map.get("delay")));
                if (!(delay >= 0)) {
                    throw new NumberFormatException();
                }
            } catch (NumberFormatException e) {
                throw new DataParseException("the passed delay was invalid: " + map.get("delay"));
            }
        }

        // Add to log.
        Log.add("A new sub-queue was created with a delay of " + delay + "ms.");
        
        // Make a new sequential transition, but first add a pausing transition.
        final SequentialTransition queue = 
                ((ServerController) getController()).getVisualizer().getVisualizationsQueue();
        queue.getChildren().add(new PauseTransition(Duration.millis(delay)));
        queue.getChildren().add(new ParallelTransition());
    }
}