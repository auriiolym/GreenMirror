package greenmirror;

import java.io.IOException;

/*
 * Implements java.util.Runnable / extends java.util.Thread.
 */
/**
 * A general class for listening to incoming data from the connected peer.
 * 
 * @author Karim El Assal
 */
public class PeerListener extends Thread {

    // -- Instance variables -----------------------------------------------------------------
    
    /**
     * The controller used for the connections and handling of incoming data.
     */
    //@ private invariant controller != null;
    private GreenMirrorController controller;


    // -- Constructors -----------------------------------------------------------------------

    /**
     * Prepare the new listening <tt>Thread</tt>.
     * @param controller The controller used for the connections and handling of incoming data.
     */
    //@ requires controller != null;
    //@ ensures getController() == controller;
    public PeerListener(GreenMirrorController controller) {
        this.controller = controller;
    }

    
    // -- Queries ----------------------------------------------------------------------------

    /**
     * @return The controller used for the connections and handling of incoming data.
     */
    //@ ensures \result != null;
    public GreenMirrorController getController() {
        return controller;
    }
    
    /**
     * @param rawData Raw data with the format (without quotes): "command:data"
     * @return        The command part of the raw data.
     */
    //@ requires rawData != null;
    //@ ensures \result != null;
    /*@ pure */ private String extractCommand(String rawData) {
        String[] dataParts = rawData.split(":", 2);
        return dataParts[0];
    }
    
    /**
     * @param rawData Raw data with the format (without quotes): "command:data"
     * @return        The data part of the raw data; <tt>null</tt> if no data was found.
     */
    //@ requires rawData != null;
    /*@ pure */ private String extractData(String rawData) {
        String[] dataParts = rawData.split(":", 2);
        return dataParts.length <= 1 ? null : dataParts[1];
    }
    
    // -- Commands ---------------------------------------------------------------------------

    /**
     * Start listening for incoming data. If a <tt>CommandHandler</tt> is found that can handle
     * specific incoming data, the data and the <tt>CommandHandler</tt> are sent to the 
     * controller's handlePeerData(String, CommandHandler) method.
     */
    public void run() {
        if (getController().getStreamIn() == null) {
            throw new IllegalStateException("No incoming connection could be found.");
        }
        
        try {
            // Keep on listening for raw data.
            while (true) {
                
                // Read raw data.
                boolean dataIsHandled = false;
                String in = getController().getStreamIn().readLine();
                if (in == null || in.equals("")) {
                    throw new IOException();
                }
                
                Log.addVerbose("Data received from peer: " + in);
                
                // Extract data.
                String command = extractCommand(in);
                String data = extractData(in);
                
                // Find correct CommandHandlers.
                for (CommandHandler handler : getController().getCommandHandlers()) {
                    if (command.equals(handler.getCommand())) {
                        
                        // Use controller to let the handler handle the data.
                        getController().handlePeerData(data, handler);
                        
                        /* We don't break from the for loop, so raw data can be handled by
                         * multiple CommandHandlers. */
                        dataIsHandled = true;
                    }
                }
                if (!dataIsHandled) {
                    Log.add("An unkonwn command was received from the peer (" + command
                          + "). It was ignored.");
                }
            }
        } catch (IOException e) {
            getController().closeStreams();
        }
    }
}