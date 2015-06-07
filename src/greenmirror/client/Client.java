package greenmirror.client;

import greenmirror.ClientSide;
import greenmirror.Command;
import greenmirror.CommandHandler;
import greenmirror.CommandLineOptionHandler;
import greenmirror.GreenMirrorController;
import greenmirror.Log;
import greenmirror.Node;
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

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
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

import org.eclipse.jdt.annotation.NonNull;

/**
 * Implements java.util.Observer.
 */
public class Client extends GreenMirrorController implements Observer {

    // -- Constants --------------------------------------------------------------------------
    
    /**
     * The current GreenMirror client application version.
     */
    private static final double VERSION = 1.0;
    
    /**
     * The connection timeout in seconds.
     */
    private static final int CONNECTION_TIMEOUT = 30;

    
    // -- Instance variables -----------------------------------------------------------------
    
    /**
     * The available transitions as defined by the model initializer.
     */
    //@ private invariant availableTransitions != null;
    private List<ModelTransition> availableTransitions = new LinkedList<ModelTransition>();
    
    /**
     * All registered <code>ModelInitializer</code>s.
     */
    //@ private invariant registeredModelInitializers != null;
    private List<ModelInitializer> registeredModelInitializers = new LinkedList<ModelInitializer>();
    
    /**
     * All registered <code>TraceSelector</code>s.
     */
    //@ private invariant registeredTraceSelectors != null;
    private List<TraceSelector> registeredTraceSelectors = new LinkedList<TraceSelector>();

    
    // -- Constructors -----------------------------------------------------------------------
    
    /**
     * Create a new Client controller. It registers any available <code>ModelInitializer</code>s,
     * <code>TraceSelector</code>s and <code>CommandHandler</code>s.
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

    /**
     * @return The available transitions as defined by the model initializer.
     */
    //@ ensures \result != null;
    /*@ pure */ public List<ModelTransition> getTransitions() {
        return availableTransitions;
    }
    
    /**
     * @param traceTransition A transition from a trace.
     * @return                All <code>ModelTransition</code>s that would execute from
     *                        <code>traceTransition</code>.
     */
    //@ requires traceTransition != null;
    //@ ensures !\result.isEmpty();
    /*@ pure */ public List<ModelTransition> getTransitions(String traceTransition) {
        List<ModelTransition> matchedTransitions = new LinkedList<ModelTransition>();
        for (ModelTransition transition : getTransitions()) {
            if (transition.executableBy(traceTransition)) {
                matchedTransitions.add(transition);
            }
        }
        //TODO - use lambda function here.
        return matchedTransitions;
    }

    /**
     * @return All registered <code>ModelInitializer</code>s.
     */
    //@ ensures \result != null;
    /*@ pure */ public List<ModelInitializer> getModelInitializers() {
        return registeredModelInitializers;
    }

    /**
     * @return All registered <code>TraceSelector</code>s.
     */
    //@ ensures \result != null;
    /*@ pure */ public List<TraceSelector> getTraceSelectors() {
        return registeredTraceSelectors;
    }
    
    
    // -- Setters ----------------------------------------------------------------------------
    
    /**
     * Adds a <code>Node</code> to the visualizer and set the unique id of the <code>Node</code>
     * accordingly.
     * @param node The new <code>Node</code>.
     */
    //@ requires node != null && !getNodes().contains(node);
    //@ ensures getNodes().contains(node);
    public void addNode(Node node) {
        getNodes().add(node);
        node.setId(getNodes().indexOf(node));
        
        // Add this controller to the list of Observers.
        node.addObserver(this);
        
        // Add to log.
        Log.add("Node added: " + node.toString());
        
        // Notify the server.
        send(new AddNodeCommand(node));
        
        // If the appearance has already been set, also notify the server.
        if (node.getFxWrapper() != null) {
            send(new SetNodeFxCommand(node));
        }
        
        // If any relations have already been set, also notify the server.
        for (Relation relation : node.getRelations()) {
            send(new AddRelationCommand(relation));
        }
    }
    
    /**
     * Adds a <code>Relation</code> to the visualizer and to the model.
     * @param relation The new <code>Relation</code>.
     */
    //@ requires relation != null;
    //@ ensures relation.getNodeA().hasRelation(relation);
    //@ ensures relation.getNodeB().hasRelation(relation); 
    public void addRelation(Relation relation) {
        relation.addToNodes();
        send(new AddRelationCommand(relation));
    }
    
    /**
     * Remove a <code>Node</code> from the visualizer. It is actually replaced by a <code>NullNode</code>
     * so no issues occur with the indices of <code>NodeList</code> and <code>id</code>s of <code>Node</code>s.
     * The server will be notified and will handle the removal of relations in its own way.
     * @param node The <code>Node</code> to remove.
     */
    //@ requires node != null;
    public void removeNode(Node node) {
        Integer id = node.getId();
        // No id means the node isn't part of GreenMirror.
        if (id == null) {
            return;
        }
        NullNode removedNode = new NullNode(node.getType(), node.getName());
        removedNode.setId(id);
        getNodes().set(id, removedNode);
        
        // Remove relations.
        //node.getRelations().forEach(relation -> removeRelation(relation));
        //TODO: fix this (serverside). Remove from observing list and remove relations.
        
        // Notify the server.
        send(new RemoveNodeCommand(node));
        // Add to log.
        Log.add("Node removed: " + node.toString());
    }
    
    /**
     * Removes a <code>Relation</code> and notifies the visualizer.
     * @param relation The <code>Relation</code> to remove.
     */
    //@ requires relation != null;
    //@ ensures !relation.getNodeA().hasRelation(relation);
    //@ ensures !relation.getNodeB().hasRelation(relation); 
    public void removeRelation(Relation relation) {
        relation.removeFromNodes();
        send(new RemoveRelationCommand(relation));
    }
    

    // -- Commands ---------------------------------------------------------------------------

    /**
     * Connect to the server. If <code>port</code> is -1, we just return. This can be used for debug
     * purposes.
     * @param host The address of the server.
     * @param port The port on which the server is listening.
     */
    //@ requires host != null && port >= -1 && port < 65535;
    public void connect(InetAddress host, int port) throws SocketTimeoutException, IOException {
    
        if (port == -1) {
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
     * Initialize the model.
     * @param initializers The instantiated <code>ModelInitializer</code>s.
     */
    public void initializeModel(@NonNull List<ModelInitializer> initializers) {
        for (ModelInitializer initializer : initializers) {
            initializer.executeInitializer();
        }
        Log.add("Model(s) initialized.");
    }
    
    /**
     * Validate the transitions on the trace given by <code>selector</code> by checking if there is
     * registered transition code available.
     * @param selector The trace supplier.
     * @return         A list of invalid transitions; <code>null</code> if all transitions on the 
     *                 trace are valid.
     */
    //@ requires selector != null;
    /*@ pure */ public List<String> validateTrace(TraceSelector selector) {
        List<String> invalidTransitions = new LinkedList<String>();
        for (String traceTransition : selector.getTrace()) {
            if (getTransitions(traceTransition).isEmpty()) {
                invalidTransitions.add(traceTransition);
            }
        }
        //TODO - use lambda function here.
        if (invalidTransitions.isEmpty()) {
            Log.add("Trace validated.");
            return null;
        } else {
            return invalidTransitions;
        }
    }

    /**
     * Execute the trace.
     * @param traceSelector The <code>TraceSelector</code> that selects the trace.
     */
    //@ requires traceSelector != null;
    public void executeTrace(TraceSelector traceSelector) {
        // Loop through every trace transition.
        for (String traceTransition : traceSelector.getTrace()) {
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
     * 
     * @param o
     * @param cmd
     */
    @Override
    public void update(Observable observable, Object cmd) {
        if (cmd instanceof Command) {
            send((Command) cmd);
            return;
        }
        if (cmd instanceof String && "request_addition".equals(cmd)) {
            addNode((Node) observable);
        }
    }
    
    /**
     * Let the server know how to initialize the visualizer. This has to be done as the first
     * command.
     * @param width    The width of the canvas.
     * @param height   The height of the canvas.
     * @param duration The default duration of transitions; -1 for unspecified duration.
     * @param rotateRigidlyRelatedNodesRigidly
     *                 {@see greenmirror.server.Visualizer#getRotateRigidlyRelatedNodesRigidly()}
     */
    //@ requires width > 0 && height > 0 && duration >= -1.0;
    public void initializeVisualizer(double width, double height, double duration,
            boolean rotateRigidlyRelatedNodesRigidly) {
        send(new InitializationCommand(width, height, duration, rotateRigidlyRelatedNodesRigidly));
    }

    /**
     * 
     * @param data
     */
    @Override
    public void handlePeerData(@NonNull String data, CommandHandler handler) {
        // TODO - implement GMClient.handlePeerData
        throw new UnsupportedOperationException();
    }
    
    
    
    
    
    public static void main(@NonNull String[] args) {
        
        Log.addOutput(Log.DEFAULT);
        final Client greenmirror = new Client();


        // Process the command line startup.
        boolean successfulStartup = greenmirror.processCommandLine(args);
        
        if (successfulStartup) {
            Log.add("We seem to be done. I'm closing down now.");
        } else if (greenmirror.getStreamOut() != null) {
            greenmirror.send(new ExitVisualizerCommand());
        }
        
        // And exit.
        greenmirror.closeStreams();
        
        
    }

}