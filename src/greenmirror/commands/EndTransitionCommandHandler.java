package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.ServerSide;
import greenmirror.server.ServerController;
import greenmirror.server.Visualizer;
import groovy.json.JsonOutput;

/**
 * The handler that handles the signal that we're at the end of a transition. 
 * This command is received from the client.
 * 
 * @author Karim El Assal
 */
@ServerSide
public class EndTransitionCommandHandler extends CommandHandler {

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
        
        

        Visualizer visualizer = getController().getVisualizer();

        Log.addVerbose("The following animations are saved to transition to state " 
            + (visualizer.getMementoCount() + 1) + ": " 
            + JsonOutput.prettyPrint(JsonOutput.toJson(
                    Visualizer.listTransitions(visualizer.getVisualizationsQueue())
              ))
        );
        // Save the state with the visualizations as the transition to the next one.
        visualizer.addMemento(
                visualizer.saveToMemento(visualizer.getVisualizationsQueue()));
        // And reset the queue;
        visualizer.resetVisualizationQueue();
    }
}