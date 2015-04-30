package greenmirror;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.net.Socket;
import java.util.LinkedList;
import java.util.List;

/**
 * The base controller. It contains shared functionality for the client and server 
 * implementations.
 * 
 * @author Karim El Assal
 */
public abstract class GreenMirrorController {

    // -- Instance variables -----------------------------------------------------------------
    
    /**
     * All <tt>Node</tt>s.
     */
    //@ private invariant nodes != null && nodes == getNodes();
    private NodeList nodes = new NodeList();
    
    /**
     * The socket and input and output streams from and to the peer.
     */
    //@ private invariant getStreamIn() == streamIn;
    private BufferedReader streamIn;
    //@ private invariant getStreamOut() == streamOut;
    private BufferedWriter streamOut;
    //@ private invariant getSocket() == socket;
    private Socket socket;

    /**
     * All registered <tt>CommandHandler</tt>s.
     */
    //@ private invariant commandHandlers != null;
    private List<CommandHandler> commandHandlers = new LinkedList<CommandHandler>();
    
    /**
     * The communication format used for network communication.
     */
    //@ private invariant communicationFormat != null;
    private CommunicationFormat communicationFormat = CommunicationFormat.JSON;
    
    /**
     * The instance that listens to data from the peer.
     */
    private PeerListener peerListener;

    
    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @return The reference to the list of <tt>Node</tt>s.
     */
    //@ ensures \result != null;
    /*@ pure */ public NodeList getNodes() {
        return nodes;
    }
    
    /**
     * Get a <tt>NodeList</tt> which only contains the name and/or type specified in 
     * <tt>identifierArg</tt>.
     * @param identifier The name/type identifier. {@link greenmirror.Node.Identifier}
     * @return           The list.
     */
    //@ requires identifierArg != null;
    //@ ensures \result != null;
    /*@ pure */ public NodeList getNodes(String identifier) {
        return getNodes().withIdentifier(identifier);
    }

    /**
     * Get a <tt>Node</tt> by its id.
     * @param id The <tt>Node</tt>'s id.
     * @return   The <tt>Node</tt> with id <tt>id</tt>.
     */
    //@ requires id != null;
    //TODO: do something with invalid ids.
    /*@ pure */ public Node getNode(Integer id) {
        for (Node node : getNodes()) {
            if (id.equals(node.getId())) {
                return node;
            }
        }
        return null;
    }

    /**
     * @return The incoming stream.
     */
    /*@ pure */ public BufferedReader getStreamIn() {
        return streamIn;
    }

    /**
     * @return The outgoing stream.
     */
    /*@ pure */ public BufferedWriter getStreamOut() {
        return streamOut;
    }

    /**
     * @return The socket.
     */
    /*@ pure */ public Socket getSocket() {
        return socket;
    }

    /**
     * @return All registered <tt>CommandHandler</tt>s.
     */
    //@ ensures \result != null;
    /*@ pure */ public List<CommandHandler> getCommandHandlers() {
        return commandHandlers;
    }

    /**
     * @return The communication format used for network communication.
     */
    //@ ensures \result != null;
    /*@ pure */ public CommunicationFormat getCommunicationFormat() {
        return communicationFormat;
    }

    
    // -- Setters ----------------------------------------------------------------------------

    /**
     * @param in The incoming stream to set.
     */
    //@ ensures getStreamIn() == in;
    public void setStreamIn(BufferedReader in) {
        streamIn = in;
    }

    /**
     * @param out The outgoing stream to set.
     */
    //@ ensures getStreamOut() == out;
    public void setStreamOut(BufferedWriter out) {
        streamOut = out;
    }

    /**
     * @param socket The socket to set.
     */
    //@ ensures getSocket() == socket;
    public void setSocket(Socket socket) {
        this.socket = socket;
    }

    /**
     * @param handler The command handler to register.
     */
    //@ requires handler != null;
    //@ ensures getCommandHandlers().contains(handler);
    //@ ensures this.equals(handler.getController());
    public void register(CommandHandler handler) {
        getCommandHandlers().add(handler);
        handler.setController(this);
    }

    /**
     * @param format The communication format to set.
     */
    //@ ensures getCommunicationFormat() == format;
    public void setCommunicationFormat(CommunicationFormat format) {
        communicationFormat = format;
    }


    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * @param data Raw data to send to the peer.
     */
    //@ requires data != null;
    public void send(String data) {
        try {
            getStreamOut().write(data);
            getStreamOut().newLine();
            getStreamOut().flush();
        } catch (IOException e) {
            closeStreams();
        } catch (NullPointerException e) {
            Log.add("No connection available for sending data. ", e);
            closeStreams();
            return;
        }
        Log.addVerbose("Data sent to peer: " + data);
    }
    
    /**
     * @param cmd <tt>Command</tt> to send to the peer.
     */
    //@ requires cmd != null;
    public void send(Command cmd) {
        if (cmd.getController() == null) {
            cmd.setController(this);
        }
        cmd.prepare();
        send(cmd.getCommand() + ":" + cmd.getFormattedString(getCommunicationFormat()));
    }

    /**
     * @param listener The <tt>PeerListener</tt> we're starting to listen.
     */
    //@ requires listener != null && this.equals(listener.getController());
    public void startPeerListener(PeerListener listener) {
        assert listener != null && this.equals(listener.getController());
        
        listener.start();
    }

    /**
     * Close the streams.
     */
    //@ ensures getSocket() == null && getStreamIn() == null && getStreamOut() == null;
    public synchronized void closeStreams() {
        try {
            getSocket().close();
            getStreamIn().close();
            getStreamOut().close();
            setSocket(null);
            setStreamIn(null);
            setStreamOut(null);
            
            Log.add("The connection with the peer has been closed.\n");
        } catch (IOException e) {
            Log.add("An IOException occured while closing the connection with the peer: ", e);
            // Don't do anything further with this.
        } catch (NullPointerException e) {
            // Streams have already been closed, don't do anything.
        }
    }

    /**
     * 
     * @param data
     */
    public abstract void handlePeerData(String data, CommandHandler handler);

}