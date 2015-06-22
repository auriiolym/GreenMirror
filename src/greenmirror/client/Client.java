package greenmirror.client;

import greenmirror.ClientSide;
import greenmirror.Command;
import greenmirror.CommandHandler;
import greenmirror.CommandLineOptionHandler;
import greenmirror.GreenMirrorController;
import greenmirror.Log;
import greenmirror.Node;
import greenmirror.NodeList;
import greenmirror.NullNode;
import greenmirror.PeerListener;
import greenmirror.Relation;
import greenmirror.commands.AddNodeCommand;
import greenmirror.commands.AddRelationCommand;
import greenmirror.commands.EndTransitionCommand;
import greenmirror.commands.ExitVisualizerCommand;
import greenmirror.commands.InitializationCommand;
import greenmirror.commands.RemoveNodeCommand;
import greenmirror.commands.RemoveRelationCommand;
import greenmirror.commands.SetAnimationDurationCommand;
import greenmirror.commands.SetNodeFxCommand;
import greenmirror.commands.StartVisualizationCommand;

import org.eclipse.jdt.annotation.NonNull;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.InputStreamReader;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.InetSocketAddress;
import java.net.Socket;
import java.net.SocketTimeoutException;
import java.util.LinkedList;
import java.util.List;
import java.util.Observable;
import java.util.Observer;
import java.util.ServiceLoader;

/**
 * The controller on the client side. It handles nearly everything, from the connection with the
 * server to the tracking of the model.
 * 
 * @author Karim El Assal
 */
public class Client extends GreenMirrorController implements Observer {

    // -- Constants --------------------------------------------------------------------------
    
    /** the current GreenMirror client application version */
    private static final double VERSION = 1.0;
    
    /** the connection timeout in seconds */
    private static final int CONNECTION_TIMEOUT = 30;

    
    // -- Instance variables -----------------------------------------------------------------
    
    /** the available transitions as loaded by the model initializer */
    @NonNull private List<ModelTransition> availableTransitions 
                                            = new LinkedList<ModelTransition>();
    
    /** all registered <code>ModelInitializer</code>s */
    @NonNull private List<ModelInitializer> registeredModelInitializers 
                                            = new LinkedList<ModelInitializer>();
    
    /** all registered <code>TraceSelector</code>s */
    @NonNull private List<TraceSelector> registeredTraceSelectors 
                                            = new LinkedList<TraceSelector>();

    
    // -- Constructors -----------------------------------------------------------------------
    
    /**
     * Creates a new <code>Client</code> controller. It registers any available 
     * {@link ModelInitializer}s, {@link TraceSelector}s and {@link CommandHandler}s.
     */
    public Client() {
        
        // Register CommandHandlers
        ServiceLoader.load(CommandHandler.class).forEach(ch -> {
            if (ch.getClass().isAnnotationPresent(ClientSide.class)) {
                ch.setController(this);
                getCommandHandlers().add(ch);
            }
        });
        
        // Register ModelInitializers.
        ServiceLoader.load(ModelInitializer.class).forEach(mi -> {
            mi.setController(this);
            getModelInitializers().add(mi);
        });
        
        // Register TraceSelectors.
        ServiceLoader.load(TraceSelector.class).forEach(ts -> {
            getTraceSelectors().add(ts);
        });

        // Register CommandLineOptionHandlers.
        ServiceLoader.load(CommandLineOptionHandler.class).forEach(cloh -> {
            if (cloh.getClass().isAnnotationPresent(ClientSide.class)) {
                getCommandLineOptionHandlers().add(cloh);
            }
        });
    }

    
    // -- Queries ----------------------------------------------------------------------------
    
    @Override @NonNull
    public String getHelpMessage() {
        String help = 
            "\nGreenMirror State-Transition Visualization client v" + VERSION + "."
          + "\n"
          + "\nThe following options are available:"
          + "\n%s"
          + "\n "
          + "\nThe parameter of the model initializers and trace selectors described below "
          + "differs per implementation.If you need to use spaces in your parameters, surround "
          + "them by quotes (\")."
          + "\n "
          + "\nThe following model initializers are currently supported:";
        int counter = 1;
        for (ModelInitializer mi : getModelInitializers()) {
            help += "\n" + counter;
            help += ". initializer: " + mi.getIdentifier();
            help += "\n     parameter: " + mi.getParameterSpecification();
            counter++;
        }
        help += "\n\nAnd the following trace selectors are currently supported:";
        counter = 1;
        for (TraceSelector ts : getTraceSelectors()) {
            help += "\n" + counter + ".    selector: " + ts.getIdentifier();
            help += "\n     parameter: " + ts.getParameterSpecification();
            counter++;
        }
        return help;
    }

    /** @return the available transitions as defined by the model initializer */
    /*@ pure */ @NonNull public List<ModelTransition> getTransitions() {
        return availableTransitions;
    }
    
    /**
     * @param traceTransition a transition from a trace
     * @return                all {@link ModelInitializer}s that would execute from
     *                        <code>traceTransition</code>
     */
    /*@ pure */ @NonNull public List<ModelTransition> getTransitions(
                                                            @NonNull String traceTransition) {
        final List<ModelTransition> matchedTransitions = new LinkedList<ModelTransition>();
        for (ModelTransition transition : getTransitions()) {
            if (transition.executableBy(traceTransition)) {
                matchedTransitions.add(transition);
            }
        }
        return matchedTransitions;
    }

    /**
     * @return all registered {@link ModelInitializer}s
     */
    /*@ pure */ @NonNull public List<ModelInitializer> getModelInitializers() {
        return registeredModelInitializers;
    }

    /**
     * @return all registered {@link TraceSelector}s
     */
    /*@ pure */ @NonNull public List<TraceSelector> getTraceSelectors() {
        return registeredTraceSelectors;
    }
    
    
    // -- Setters ----------------------------------------------------------------------------
    
    /**
     * Adds a {@link Node} to the visualizer and sets the unique id of the node accordingly.
     * It also starts observing the node for changes. If the node is already added, nothing 
     * happens.
     * 
     * @param node the new <code>Node</code>
     */
    //@ ensures getNodes().contains(node);
    public void addNode(@NonNull Node node) {
        if (getNodes().contains(node)) {
            return;
        }
        
        getNodes().add(node);
        node.setId(getNodes().indexOf(node));
        
        // Add this controller to the list of Observers.
        node.addObserver(this);
        
        // Notify the server.
        send(new AddNodeCommand(node));
        
        // If the appearance has already been set, also notify the server.
        if (node.getFxWrapper() != null) {
            send(new SetNodeFxCommand(node));
        }
        
        // If any relations have already been set, also notify the server.
        for (Relation relation : node.getRelations()) {
            if (relation != null) {
                send(new AddRelationCommand(relation));
            }
        }
    }
    
    /**
     * Adds a {@link Relation} to the visualizer and to the model. After some validity checks,
     * it adds the relation via {@link Node#addRelation(Relation)}. This means that if
     * <code>relation</code> is a placement relation, it replaces the previous placement
     * relation.
     * 
     * @param relation the new relation with both nodes set and both nodes should be known to 
     *                 the controller (this <code>Client</code> instance)
     * @throws IllegalArgumentException if one of the two nodes of the relation is 
     *                                  <code>null</code> or one of the two nodes isn't known
     *                                  to the controller
     */
    //@ requires relation.getNodeA() != null;
    //@ requires relation.getNodeB() != null;
    //@ ensures relation.getNodeA().hasRelation(relation);
    //@ ensures relation.getNodeB().hasRelation(relation); 
    public void addRelation(@NonNull Relation relation) {
        if (relation.getNodeA() == null || relation.getNodeB() == null) {
            throw new IllegalArgumentException("relation should have both nodes set");
        }
        if (!getNodes().contains(relation.getNodeA()) 
                || !getNodes().contains(relation.getNodeB())) {
            throw new IllegalArgumentException("related nodes should both be known with the "
                    + "controller");
        }
        
        // Add the relation to the node. This uses all the checks concerning placement relations.
        final Node nodeA = relation.getNodeA();
        relation.removeNodeA();
        nodeA.addRelation(relation);
    }
    
    /**
     * Removes a {@link Node} from the visualizer. It is actually replaced by a {@link NullNode}
     * so no issues occur with the indices of {@link NodeList} and <code>id</code>s of nodes.
     * The server will be notified and will handle the removal of relations in its own way.
     * 
     * @param node the node to remove
     */
    //@ ensures !getNodes().contains(node);
    public void removeNode(@NonNull Node node) {
        final Integer id = node.getId();
        // No id means the node isn't part of GreenMirror.
        if (id == null) {
            return;
        }
        final NullNode removedNode = new NullNode(node.getType(), node.getName());
        removedNode.setId(id);
        getNodes().set(id, removedNode);
        
        // Remove the current controller instance as an observer and remove relations.
        node.deleteObserver(this);
        node.getRelations().removeAll();
        
        // Notify the server.
        send(new RemoveNodeCommand(node));
        // Add to log.
        Log.add("Node removed: " + node.toString());
    }
    
    /**
     * Removes a {@link Relation} and notifies the server. If <code>relation</code> is 
     * <code>null</code>, nothing happens.
     * 
     * @param relation the relation to remove
     */
    //@ ensures relation != null ? !relation.getNodeA().hasRelation(relation) : true;
    //@ ensures relation != null ? !relation.getNodeB().hasRelation(relation) : true; 
    public void removeRelation(Relation relation) {
        if (relation == null) {
            return;
        }
        relation.removeFromNodes();
        send(new RemoveRelationCommand(relation));
    }
    

    // -- Commands ---------------------------------------------------------------------------

    /**
     * Connects to the server. If <code>port</code> is not between 0 and 65535, we just return. 
     * This can be used for debug purposes. If the connection was established succesfully,
     * a new {@link PeerListener} thread is started to listen for incoming data.
     * 
     * @param host the address of the server
     * @param port the port on which the server should be listening (between 0 and 65535)
     * @throws SocketTimeoutException if the connection to the server timed out
     * @throws IOException            if something went wrong with creating the streams
     */
    //@ requires port >= -1 && port < 65535;
    public void connect(InetAddress host, int port) 
            throws SocketTimeoutException, IOException {
    
        if (port < 0 || port > 65535) {
            return;
        }
        
        // Open a socket to the server.
        setSocket(new Socket());
        getSocket().connect(new InetSocketAddress(host, port), CONNECTION_TIMEOUT * 1000);
            
        
        // Open the input and output streams from and to the server.
        setStreamIn(new BufferedReader(new InputStreamReader(getSocket().getInputStream())));
        setStreamOut(new BufferedWriter(new OutputStreamWriter(getSocket().getOutputStream())));
        
        // Add to log.
        Log.add("Connection established with server " + host.getHostAddress() + ":" + port + ".");
        
        // Start listening for incoming data.
        startPeerListener(new PeerListener(this));
    }

    /**
     * Initializes the model using all passed {@link ModelInitializer}s.
     * 
     * @param initializers the <code>ModelInitializer</code> instances
     */
    public void initializeModel(@NonNull List<ModelInitializer> initializers) {
        for (ModelInitializer initializer : initializers) {
            initializer.executeInitializer();
        }
        Log.add("Model(s) initialized.");
    }
    
    /**
     * Validates the transitions on the trace given by <code>selector</code> by checking if there is
     * registered {@link ModelTransition} available.
     * 
     * @param selector the trace supplier
     * @return         a list of invalid transitions; <code>null</code> if all transitions on the 
     *                 trace are valid
     */
    /*@ pure */ public List<String> validateTrace(@NonNull TraceSelector selector) {
        final List<String> invalidTransitions = new LinkedList<String>();
        for (String traceTransition : selector.getTrace()) {
            if (traceTransition != null && getTransitions(traceTransition).isEmpty()) {
                invalidTransitions.add(traceTransition);
            }
        }
        
        if (invalidTransitions.isEmpty()) {
            Log.add("Trace validated.");
            return null;
        } else {
            return invalidTransitions;
        }
    }

    /**
     * Executes the trace.
     * 
     * @param traceSelector the {@link TraceSelector} that selects the trace
     */
    public void executeTrace(@NonNull TraceSelector traceSelector) {
        // Loop through every trace transition.
        for (String traceTransition : traceSelector.getTrace()) {
            if (traceTransition == null) { // @NonNull formality
                continue;
            }
            // And execute the transition.
            for (ModelTransition transition : getTransitions(traceTransition)) {
                send(new SetAnimationDurationCommand(transition.getDuration()));
                transition.execute(traceTransition);
                if (!transition.isSupplemental()) {
                    send(new EndTransitionCommand());
                    Log.add("Transition " + traceTransition + " executed.");
                }
            }
        }
        send(new StartVisualizationCommand());
        Log.add("Trace executed.");
    }

    /**
     * Receives updates from the objects it's observing. In practice, these only are the
     * GreenMirror {@link Node}s. If they have sent an update to this method, it means
     * they want the server to know about a change in the model. In that case, this method
     * forwards the received {@link Command}.
     * 
     * @param observable the object it's observing
     * @param cmd        the object the observable passed
     */
    @Override
    public void update(Observable observable, Object cmd) {
        if (cmd instanceof Command) {
            send((Command) cmd);
            return;
        }
    }
    
    /**
     * Lets the server know with what parameters to initialize the visualizer. This has to be 
     * done as the first command and is the responsibility of the {@link ModelInitializer}
     * implementations.
     * 
     * @param width    the width of the canvas
     * @param height   the height of the canvas
     * @param duration the default duration of transitions; -1 for unspecified duration.
     * @param rotateRigidlyRelatedNodesRigidly see
     *                 {@link greenmirror.server.Visualizer#isRotateRigidlyRelatedNodesRigidly()}
     */
    //@ requires width > 0 && height > 0 && duration >= -1.0;
    public void initializeVisualizer(double width, double height, double duration,
            boolean rotateRigidlyRelatedNodesRigidly) {
        send(new InitializationCommand(width, height, duration, rotateRigidlyRelatedNodesRigidly));
    }

    /**
     * Handles data received from the peer. In the current version of GreenMirror, no
     * data is received from the peer, but this could be possible in future versions.
     * 
     * @param data    the received data
     * @param handler the command handler that has been matched with the data
     */
    @Override
    public void handlePeerData(@NonNull String data, CommandHandler handler) {
        throw new UnsupportedOperationException();
    }
    
    
    
    
    /**
     * The main entry point for the GreenMirror client. All available options are explained if
     * --help or -? is passed.
     * 
     * @param args the passed command line options
     */
    public static void main(@NonNull String[] args) {
        
        Log.addOutput(Log.DEFAULT);
        final Client greenmirror = new Client();


        // Process the command line startup.
        final boolean successfulStartup = greenmirror.processCommandLine(args);
        
        if (successfulStartup) {
            Log.add("We seem to be done. I'm closing down now.");
        } else if (greenmirror.getStreamOut() != null) {
            greenmirror.send(new ExitVisualizerCommand());
        }
        
        // And exit.
        greenmirror.closeStreams();
    }

}