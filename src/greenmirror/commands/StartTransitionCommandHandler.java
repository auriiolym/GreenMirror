package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.server.ServerController;
import greenmirror.server.Visualizer;
import groovy.json.JsonOutput;

import java.util.Map;

import javafx.util.Duration;

/**
 * The handler that starts the visualizations stored in the queue. 
 * This command is received from the client.
 * 
 * @author Karim El Assal
 */
public class StartTransitionCommandHandler extends CommandHandler {

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
            delay = Double.valueOf(String.valueOf(map.get("delay")));
            if (!(delay >= 0)) {
                throw new DataParseException("The passed delay is invalid.");
            }
        }

        Log.add("Transition with delay " + delay + "ms started.");

        Visualizer visualizer = getController().getVisualizer();
        // Set the delay of the visualizations queue.
        visualizer.getVisualizationsQueue().setDelay(Duration.millis(delay));
        Log.addVerbose("The following transitions are executed: " 
            + JsonOutput.prettyPrint(JsonOutput.toJson(
                    Visualizer.listTransitions(visualizer.getVisualizationsQueue())
              ))
        );
        // Execute the transitions in the queue.
        visualizer.toNextState(visualizer.getVisualizationsQueue());
        // And reset the queue;
        visualizer.resetVisualizationQueue();
    }
}