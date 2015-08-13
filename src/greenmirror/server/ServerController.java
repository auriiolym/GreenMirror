package greenmirror.server;

import greenmirror.CommandHandler; 
import greenmirror.CommandHandler.DataParseException;
import greenmirror.CommandHandler.MissingDataException;
import greenmirror.CommandLineOptionHandler;
import greenmirror.GreenMirrorController;
import greenmirror.Log;
import greenmirror.PeerListener;
import greenmirror.ServerSide;

import org.eclipse.jdt.annotation.NonNull;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.InputStreamReader;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.UnknownHostException;
import java.util.ServiceLoader;

/**
 * The main server class.
 * 
 * @author Karim El Assal
 */
public class ServerController extends GreenMirrorController {
    
    // -- Constants --------------------------------------------------------------------------

    /**
     * The current GreenMirror server application version.
     */
    private static final double VERSION = 1.0;
    
    /**
     * The help message, shown in the log when --help is used as an option.
     */
    @NonNull private static final String HELP_MSG = 
          "\nGreenMirror State-Transition Visualization server v" + VERSION + "."
        + "\n"
        + "\nThe following options are available:\n%s";
    
    // -- Class variables --------------------------------------------------------------------

    // -- Instance variables -----------------------------------------------------------------
    
    /** the visualizer controller */
    private Visualizer visualizer;

    /** the port the server will be listening on */
    private Integer port;
    
    
    private ServerSocket serverSocket;
    

    // -- Constructors -----------------------------------------------------------------------
    
    /**
     * Creates a new <code>ServerController</code> instance. It registers all available 
     * {@link CommandHandler}s and {@link CommandLineOptionHandler}s that are meant for the 
     * server.
     * 
     * @param visualizer the main application instance
     */
    //@ ensures getVisualizer() == visualizer;
    public ServerController(@NonNull Visualizer visualizer) {
        
        // Register CommandHandlers.
        for (CommandHandler ch : ServiceLoader.load(CommandHandler.class)) {
            if (ch.getClass().isAnnotationPresent(ServerSide.class)) {
                ch.setController(this);
                getCommandHandlers().add(ch);
            }
        }

        // Register CommandLineOptionHandlers.
        ServiceLoader.load(CommandLineOptionHandler.class).forEach(cloh -> {
            if (cloh.getClass().isAnnotationPresent(ServerSide.class)) {
                getCommandLineOptionHandlers().add(cloh);
            }
        });
        
        this.visualizer = visualizer;
    }

    // -- Queries ----------------------------------------------------------------------------
    
    @Override @NonNull 
    public String getHelpMessage() {
        return HELP_MSG;
    }

    /** @return the port the server will listen on */
    /*@ pure */ public Integer getPort() {
        return port;
    }

    /** @return The ip address of this computer or "?unknown?" if it couldn't be found */
    @NonNull private String getHostAddress() {
        try {
            final String iaddr = InetAddress.getLocalHost().getHostAddress();
            if (iaddr == null) {
                throw new UnknownHostException();
            }
            return iaddr;
        } catch (UnknownHostException e) {
            return "?unknown?";
        }
    }
    
    /** @return the server socket; <code>null</code> if not set */
    public ServerSocket getServerSocket() {
        return this.serverSocket;
    }
    
    
    // -- Setters ----------------------------------------------------------------------------

    /** @param port the port the server will listen on */
    //@ ensures getPort() == port;
    public void setPort(@NonNull Integer port) {
        this.port = port;
    }
    

    // -- Commands ---------------------------------------------------------------------------

    /** Creates a new {@link Thread} on which the server will listen for connections */
    //@ requires getPort() != null;
    public void listenForConnections() {
        new Thread(() -> {
            try {
                serverSocket = new ServerSocket(getPort());
                Log.add("Server is running on " + getHostAddress() + ":" + getPort() + ".");
                Log.add("Waiting for incoming connections...");
                
                // Waiting for a connection...
                setSocket(getServerSocket().accept());
        
                // Open the input and output streams from and to the server.
                setStreamIn(new BufferedReader(
                                new InputStreamReader(getSocket().getInputStream())));
                setStreamOut(new BufferedWriter(
                                new OutputStreamWriter(getSocket().getOutputStream())));
                
                
                Log.add("Client connected.");
                
                // Start listening for incoming data from the peer.
                startPeerListener(new PeerListener(this));
                
                getServerSocket().close();
            } catch (IOException e) {
                Log.add("Unable to (re)start server on port " + getPort() + ". The following "
                        + "exception was thrown: " + e.getMessage());
            }
        }).start();
    }
    
    /**
     * Starts listening for connections again if the visualizer and the connections have 
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

    /** @return the visualizer instance */
    /*@ pure */ public Visualizer getVisualizer() {
        return visualizer;
    }

    @Override
    public void handlePeerData(@NonNull String data, CommandHandler handler) {
        
        try {
            handler.handle(getCommunicationFormat(), data);
        } catch (DataParseException e) {
            Log.add(e.getMessage());
        } catch (MissingDataException e) {
            Log.add("Data was missing in the following received command: " + data);
        }
    }

    @Override
    public void closeStreams() {
        if (getServerSocket() != null) {
            try {
                getServerSocket().close();
            } catch (IOException e) {
                Log.add("An IOException occured while closing server socket: ", e);
            }
        }
        super.closeStreams();
    }
    
    /**
     * Exit the server application.
     */
    public void exit() {
        // Close the visualizer.
        if (getVisualizer().getStage() != null) {
            getVisualizer().getStage().setOnHidden(null);
            getVisualizer().getStage().close();
            getVisualizer().setStage(null);
        }
        // Close connections. This results in termination of the server.
        closeStreams();
    }

}