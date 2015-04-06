package greenmirror;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.util.LinkedList;
import java.util.List;

public abstract class GreenMirrorController {

    // -- Instance variables -----------------------------------------------------------------
    
    /**
     * All <tt>Node</tt>s.
     */
    //@ private invariant nodes != null && nodes == getNodes();
    private NodeList nodes = new NodeList();
    
    /**
     * The input and output streams from and to the peer.
     */
    //@ private invariant getStreamIn() == streamIn;
    private BufferedReader streamIn;
    //@ private invariant getStreamOut() == streamOut;
    private BufferedWriter streamOut;

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
     * <tt>identifierArg</tt>. <tt>identifierArg</tt> can have one of these formats (without
     * quotes): "type:name", "type:" or "name". 
     * @param identifierArg The name/type identifier.
     * @return The new list.
     */
    //@ requires identifierArg != null;
    /*@ pure */ public NodeList getNodes(String identifierArg) {
        NodeList result = new NodeList();
        
        Node.Identifier identifier = new Node.Identifier(identifierArg);
        
        for (Node node : getNodes()) {
            if ((identifier.hasType() && !identifier.getType().equals(node.getType()))
             || (identifier.hasName() && !identifier.getName().equals(node.getName()))) {
                continue;
            }
            result.add(node);
        }
        
        return result;
    }

    /**
     * Get a <tt>Node</tt> by its id.
     * @param id The <tt>Node</tt>'s id.
     * @result   The <tt>Node</tt> with id <tt>id</tt>.
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
     * @param handler The command handler to register.
     */
    //@ ensures getCommandHandlers().contains(handler);
    public void registerCommandHandler(CommandHandler handler) {
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
     * 
     * @param data
     */
    public void send(String data) {
        // TODO - implement GreenMirrorController.send
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param listener
     */
    public void startPeerListener(PeerListener listener) {
        
        // TODO - implement GreenMirrorController.startPeerListener
        throw new UnsupportedOperationException();
    }

    public void closeStreams() {
        // TODO - implement GreenMirrorController.closeStreams
        throw new UnsupportedOperationException();
    }

    /**
     * 
     * @param data
     */
    public abstract void handlePeerData(String data);

}