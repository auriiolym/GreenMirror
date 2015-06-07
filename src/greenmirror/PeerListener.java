package greenmirror;

import org.eclipse.jdt.annotation.NonNull;

import java.io.IOException;

/**
 * A general class for listening to incoming data from a connected peer.
 * 
 * @author Karim El Assal
 */
public class PeerListener extends Thread {

    // -- Instance variables -----------------------------------------------------------------
    
    /** the controller used for the connections and handling of incoming data */
    @NonNull private final GreenMirrorController controller;


    // -- Constructors -----------------------------------------------------------------------

    /**
     * Prepares the new listening <code>Thread</code>.
     * 
     * @param controller the controller used for the connections and handling of incoming data
     */
    //@ ensures getController() == controller;
    public PeerListener(@NonNull GreenMirrorController controller) {
        this.controller = controller;
    }

    
    // -- Queries ----------------------------------------------------------------------------

    /** @return the controller used for the connections and handling of incoming data */
    @NonNull public GreenMirrorController getController() {
        return this.controller;
    }
    
    /**
     * @param rawData raw data in the format (without quotes): "command:data"
     * @return        the command part of the raw data
     */
    /*@ pure */ @NonNull private String extractCommand(@NonNull String rawData) {
        final String cmd = rawData.split(":", 2)[0];
        return cmd == null ? "" : cmd;
    }
    
    /**
     * @param rawData raw data with the format (without quotes): "command:data"
     * @return        the data part of the raw data; an empty string if no data was found.
     */
    /*@ pure */ @NonNull private String extractData(@NonNull String rawData) {
        final String[] dataParts = rawData.split(":", 2);
        return dataParts.length <= 1 ? "" : (dataParts[1] == null ? "" : dataParts[1]);
    }
    
    // -- Commands ---------------------------------------------------------------------------

    /**
     * Start listening for incoming data. If a {@link CommandHandler} is found that can handle
     * specific incoming data, the data and the <code>CommandHandler</code> are sent to the 
     * controller's {@link GreenMirrorController#handlePeerData(String, CommandHandler)} method.
     * 
     * @throws IllegalStateException if there was no incoming connection found
     */
    @Override
    public void run() {
        if (getController().getStreamIn() == null) {
            throw new IllegalStateException("no incoming connection could be found");
        }
        
        try {
            // Keep on listening for raw data.
            while (true) {
                
                // Read raw data.
                boolean dataIsHandled = false;
                final String in = getController().getStreamIn().readLine();
                if (in == null || in.equals("")) {
                    throw new IOException();
                }
                
                final String inFormatted = in.replaceAll("(?s)\"image\":\"(.+?)\"", 
                                "\"image\":--removed for convenience--");
                Log.addVerbose("Data received from peer: " + inFormatted);
                
                // Extract data.
                final String command = extractCommand(in);
                final String data = extractData(in);
                
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