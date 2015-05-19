package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.server.ServerController;

import java.util.Map;

import javafx.animation.ParallelTransition;
import javafx.animation.PauseTransition;
import javafx.animation.SequentialTransition;
import javafx.util.Duration;

/**
 * The handler that creates a new sub-queue of visualizations. 
 * This command is received from the client.
 * 
 * @author Karim El Assal
 */
@CommandHandler.ServerSide
public class FlushCommandHandler extends CommandHandler {

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
        
        double delay;
        
        switch (format) {
        default: case JSON:
            Map<String, Object> map = CommandHandler.parseJson(data);
            if (!map.containsKey("delay")) {
                throw new MissingDataException();
            }
            try {
                delay = Double.valueOf(String.valueOf(map.get("delay")));
                if (!(delay >= 0)) {
                    throw new NumberFormatException();
                }
            } catch (NumberFormatException e) {
                throw new DataParseException("The passed delay was not valid.");
            }
        }

        Log.add("A new sub-queue was created with a delay of " + delay + "ms.");
        
        // Make a new sequential transition, but first add a pausing transition.
        SequentialTransition queue = getController().getVisualizer().getVisualizationsQueue();
        queue.getChildren().add(new PauseTransition(Duration.millis(delay)));
        queue.getChildren().add(new ParallelTransition());
    }
}