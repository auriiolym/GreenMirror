package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.ServerSide;
import greenmirror.server.ServerController;
import greenmirror.server.Visualizer;
import groovy.json.JsonOutput;

import org.eclipse.jdt.annotation.NonNull;

/**
 * The handler that handles the signal that we're at the end of a state-transition. 
 * This command is received from the client.
 * 
 * @author  Karim El Assal
 * @see     EndTransitionCommand
 */
@ServerSide
public class EndTransitionCommandHandler extends CommandHandler {
    
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public void handle(@NonNull CommunicationFormat format, @NonNull String data) 
            throws MissingDataException, DataParseException {
        

        final Visualizer visualizer = ((ServerController) getController()).getVisualizer();

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