package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.server.ServerController;
import greenmirror.server.ToolbarButton;

/**
 * The handler that handles the signal that we're at the end of a transition. 
 * This command is received from the client.
 * 
 * @author Karim El Assal
 */
@CommandHandler.ServerSide
public class StartVisualizationCommandHandler extends CommandHandler {

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
        
        
        /*
        switch (format) {
        default: case JSON:
            Map<String, Object> map = CommandHandler.parseJson(data);
        }
        */


        //Visualizer visualizer = getController().getVisualizer();
        
        Log.add("The visualization may start now.");
        getController().getVisualizer().updateStateNumberInfo();
        ToolbarButton.STEP.action();
    }
}