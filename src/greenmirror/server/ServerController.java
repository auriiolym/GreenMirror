package greenmirror.server;

import greenmirror.CommandHandler;
import greenmirror.CommandHandler.DataParseException;
import greenmirror.CommandHandler.MissingDataException;
import greenmirror.GreenMirrorController;
import greenmirror.Log;
import greenmirror.PeerListener;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.InputStreamReader;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.UnknownHostException;
import java.util.Arrays;
import java.util.ServiceLoader;

/**
 * The main server class.
 * 
 * @author Karim El Assal
 */
public class ServerController extends GreenMirrorController {
    
    // -- Constants --------------------------------------------------------------------------
    
    // -- Class variables --------------------------------------------------------------------

    // -- Instance variables -----------------------------------------------------------------
    
    /**
     * The visualizer controller.
     */
    private Visualizer visualizer;

    /**
     * The port the server will be listening on.
     */
    private Integer port;
    

    // -- Constructors -----------------------------------------------------------------------
    
    /**
     * Create a new <tt>ServerController</tt> instance. It registers all available 
     * <tt>CommandHandler</tt>s that are meant for the server.
     * @param visualizer The main application.
     */
    //@ requires visualizer != null;
    //@ ensures getVisualizer() == visualizer;
    public ServerController(Visualizer visualizer) {
        for (CommandHandler ch : ServiceLoader.load(CommandHandler.class)) {
            if (ch.getClass().isAnnotationPresent(CommandHandler.ServerSide.class)) {
                ch.setController(this);
                getCommandHandlers().add(ch);
            }
        }
        
        this.visualizer = visualizer;
    }

    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @return The port the server will listen on.
     */
    /*@ pure */ public Integer getPort() {
        return port;
    }

    /** 
     * @return The ip address of this computer or "?unknown?" if it couldn't be found. 
     */
    //@ ensures \result != null;
    private String getHostAddress() {
        try {
            InetAddress iaddr = InetAddress.getLocalHost();
            return iaddr.getHostAddress();
        } catch (UnknownHostException e) {
            return "?unknown?";
        }
    }
    
    
    // -- Setters ----------------------------------------------------------------------------

    /**
     * @param port The port the server will listen on.
     */
    //@ requires port != null;
    //@ ensures getPort() == port;
    public void setPort(Integer port) {
        this.port = port;
    }
    

    // -- Commands ---------------------------------------------------------------------------

    /**
     * Create a new <tt>Thread</tt> on which the server will listen for connections.
     */
    //@ requires getPort() != null;
    public void listenForConnections() {
        new Thread(() -> {
            try {
                ServerSocket serverSock = new ServerSocket(getPort());
                Log.add("Server is running on " + getHostAddress() + ":" + getPort() + ".");
                Log.add("Waiting for incoming connections...");
                
                // Waiting for a connection...
                setSocket(serverSock.accept());
        
                // Open the input and output streams from and to the server.
                setStreamIn(new BufferedReader(
                                new InputStreamReader(getSocket().getInputStream())));
                setStreamOut(new BufferedWriter(
                                new OutputStreamWriter(getSocket().getOutputStream())));
                
                
                Log.add("Client connected.");
                
                // Start listening for incoming data from the peer.
                startPeerListener(new PeerListener(this));
                
                serverSock.close();
            } catch (IOException e) {
                Log.add("Unable to start server on port " + getPort() + ". The following "
                        + "exception was thrown: " + e.getMessage());
            }
        }).start();
    }
    
    /**
     * Start listening for connections again if the visualizer and the connections have 
     * been closed.
     */
    public void relistenForConnections() {
        if (getVisualizer().getStage() != null || getStreamIn()  != null
                                               || getStreamOut() != null
                                               || getSocket()    != null) {
            return;
        }
        listenForConnections();
    }

    /**
     * @return The visualizer instance.
     */
    /*@ pure */ public Visualizer getVisualizer() {
        return visualizer;
    }

    /* (non-Javadoc)
     * @see greenmirror.GreenMirrorController#handlePeerData(java.lang.String,
                                                   greenmirror.CommandHandler)
     */
    @Override
    public void handlePeerData(String data, CommandHandler handler) {
        
        try {
            handler.handle(getCommunicationFormat(), data);
        } catch (DataParseException e) {
            Log.add(e.getMessage());
            //TODO: do something with this.
        } catch (MissingDataException e) {
            Log.add("Data was missing in the following received command: " + data);
            //TODO: do something with this.
        }
    }
    
    /**
     * Close the streams and start listening for connections again if wanted.
     */
    @Override
    public void closeStreams() {
        super.closeStreams();
        relistenForConnections();
    }

}