package greenmirror.client;

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
import greenmirror.commands.InitializationCommand;
import greenmirror.commands.RemoveNodeCommand;
import greenmirror.commands.RemoveRelationCommand;
import greenmirror.commands.SetAnimationDurationCommand;
import greenmirror.commands.SetNodeFxCommand;
import greenmirror.commands.StartVisualizationCommand;
import groovy.lang.GroovyRuntimeException;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.InetSocketAddress;
import java.net.Socket;
import java.net.SocketTimeoutException;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.Observable;
import java.util.Observer;
import java.util.ServiceLoader;

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
    //@ privaten invariant availableTransitions != null;
    private List<ModelTransition> availableTransitions = new LinkedList<ModelTransition>();
    
    /**
     * All registered <tt>ModelInitializer</tt>s.
     */
    //@ private invariant registeredModelInitializers != null;
    private List<ModelInitializer> registeredModelInitializers = new LinkedList<ModelInitializer>();
    
    /**
     * All registered <tt>TraceSelector</tt>s.
     */
    //@ private invariant registeredTraceSelectors != null;
    private List<TraceSelector> registeredTraceSelectors = new LinkedList<TraceSelector>();

    
    // -- Constructors -----------------------------------------------------------------------
    
    /**
     * Create a new Client controller. It registers any available <tt>ModelInitializer</tt>s,
     * <tt>TraceSelector</tt>s and <tt>CommandHandler</tt>s.
     */
    public Client() {
        
        // Register CommandHandlers
        ServiceLoader.load(CommandHandler.class).forEach(ch -> {
            if (ch.getClass().isAnnotationPresent(CommandHandler.ClientSide.class)) {
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
            if (cloh.getClass().isAnnotationPresent(CommandLineOptionHandler.ClientSide.class)) {
                getCommandLineOptionHandlers().add(cloh);
            }
        });
    }

    // -- Queries ----------------------------------------------------------------------------
    
    /* (non-Javadoc)
     * @see greenmirror.GreenMirrorController#getHelpMessage()
     */
    @Override
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
     * @return                All <tt>ModelTransition</tt>s that would execute from
     *                        <tt>traceTransition</tt>.
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
     * @return All registered <tt>ModelInitializer</tt>s.
     */
    //@ ensures \result != null;
    /*@ pure */ public List<ModelInitializer> getModelInitializers() {
        return registeredModelInitializers;
    }

    /**
     * @return All registered <tt>TraceSelector</tt>s.
     */
    //@ ensures \result != null;
    /*@ pure */ public List<TraceSelector> getTraceSelectors() {
        return registeredTraceSelectors;
    }
    
    
    // -- Setters ----------------------------------------------------------------------------
    
    /**
     * Adds a <tt>Node</tt> to the visualizer and set the unique id of the <tt>Node</tt>
     * accordingly.
     * @param node The new <tt>Node</tt>.
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
     * Adds a <tt>Relation</tt> to the visualizer and to the model.
     * @param relation The new <tt>Relation</tt>.
     */
    //@ requires relation != null;
    //@ ensures relation.getNodeA().hasRelation(relation);
    //@ ensures relation.getNodeB().hasRelation(relation); 
    public void addRelation(Relation relation) {
        relation.addToNodes();
        send(new AddRelationCommand(relation));
    }
    
    /**
     * Remove a <tt>Node</tt> from the visualizer. It is actually replaced by a <tt>NullNode</tt>
     * so no issues occur with the indices of <tt>NodeList</tt> and <tt>id</tt>s of <tt>Node</tt>s.
     * The server will be notified and will handle the removal of relations in its own way.
     * @param node The <tt>Node</tt> to remove.
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
     * Removes a <tt>Relation</tt> and notifies the visualizer.
     * @param relation The <tt>Relation</tt> to remove.
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
     * Connect to the server. If <tt>port</tt> is -1, we just return. This can be used for debug
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
     * @param initializers The instantiated <tt>ModelInitializer</tt>s.
     */
    public void initializeModel(List<ModelInitializer> initializers) {
        for (ModelInitializer initializer : initializers) {
            initializer.executeInitializer();
        }
        Log.add("Model(s) initialized.");
    }
    
    /**
     * Validate the transitions on the trace given by <tt>selector</tt> by checking if there is
     * registered transition code available.
     * @param selector The trace supplier.
     * @return         A list of invalid transitions; <tt>null</tt> if all transitions on the 
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
     * @param traceSelector The <tt>TraceSelector</tt> that selects the trace.
     */
    //@ requires traceSelector != null;
    public void executeTrace(TraceSelector traceSelector) {
        // Loop through every trace transition.
        for (String traceTransition : traceSelector.getTrace()) {
            // And execute the transition.
            for (ModelTransition transition : getTransitions(traceTransition)) {
                send(new SetAnimationDurationCommand(transition.getDuration()));
                transition.execute(traceTransition);
                send(new EndTransitionCommand());
                Log.add("Transition " + traceTransition + " executed.");
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
    public void handlePeerData(String data, CommandHandler handler) {
        // TODO - implement GMClient.handlePeerData
        throw new UnsupportedOperationException();
    }
    
    
    
    
    
    public static void main(String[] args) {
        
        Log.addOutput(Log.DEFAULT);
        final Client greenmirror = new Client();


        // Process the command line startup.
        boolean successfulStartup = greenmirror.processCommandLine(args);
        
        if (successfulStartup) {
            Log.add("We seem to be done. I'm closing down now.");
        }
        
        // And exit.
        greenmirror.closeStreams();
        
        
    }
    
    
    
    
    // FileTraceSelector test
    public static void main2(String[] args) {
        try {
            TraceSelector ts = new FileTraceSelector();
            ts.setParameter("trace");
            ts.prepare();
            System.out.println(ts.getTrace());
        } catch (Exception e) {
            System.out.println(e.getMessage());
        }
    }
    
    // GroovyScriptModelInitializer test
    public static void main1(String[] args) {
        GroovyScriptModelInitializer gsmi = new GroovyScriptModelInitializer();
        try {
            gsmi.setController(new Client());
            gsmi.setParameter("initialize_script.groovy");
            gsmi.prepare();
        } catch (Exception e) {
            System.out.println(e.getMessage());
        }
        
        try {
            gsmi.executeInitializer();
        } catch (GroovyRuntimeException e) {
            // Script1.run(Script1.groovy:1)
            System.out.println(Arrays.toString(e.getStackTrace()));
            //e.printStackTrace();
        }
    }
    
}