package greenmirror.client;

import greenmirror.Command;
import greenmirror.CommandHandler;
import greenmirror.GreenMirrorController;
import greenmirror.Log;
import greenmirror.Node;
import greenmirror.NullNode;
import greenmirror.PeerListener;
import greenmirror.commands.AddNodeCommand;
import greenmirror.commands.InitializationCommand;
import greenmirror.commands.RemoveNodeCommand;
import greenmirror.commands.SetCurrentAnimationDurationCommand;
import greenmirror.commands.SetNodeAppearanceCommand;
import greenmirror.commands.StartTransitionCommand;
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
import java.net.UnknownHostException;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Observable;
import java.util.Observer;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

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
     * The help message, shown in the log when -help is used as an argument. The first %s will
     * be replaced by a list of the registered model initializers, the second by a list of
     * registered trace selectors.
     */
    private static final String HELP_MSG = 
          "\nGreenMirror State-Transition Visualization client v" + VERSION + "."
        + "\n"
        + "\nThe following arguments are available:"
        + "\n  -host:<host>        Specifies the host of the server. <host> can be anything"
        + "\n                      that resolves to a server address."
        + "\n  -port:<port>        Specifies the port of the server. <port> should be a number."
        + "\n  -model:<initializer>:<parameters>"
        + "\n                      Specifies the model initializer which lets the application"
        + "\n                      know about your model. This argument can be used as often as"
        + "\n                      you want."
        + "\n  -trace:<selector>:<parameters>"
        + "\n                      Specifies the trace selector which lets the application"
        + "\n                      know about which trace to follow."
        + "\n  [-verbose]          Outputs verbose data to the logs. Optional."
        + "\n  [-help]             Display this help message."
        + "\n "
        + "\nIf <parameters> consists of multiple parameters (see the descriptions below),"
        + "\nthey can be passed by using a colon (:) as a delimeter. If you need to use "
        + "\nspaces in your parameters, surround them by quotes (\")."
        + "\n "
        + "\nThe following model initializers are currently supported:%s"
        + "\n "
        + "\nAnd the following trace selectors are currently supported:%s";
    
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

    // -- Queries ----------------------------------------------------------------------------
    
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
     * @param initializer The model initializer to register.
     */
    //@ ensures getModelInitializers().contains(initializer);
    //@ ensures this.equals(initializer.getController());
    public void register(ModelInitializer initializer) {
        getModelInitializers().add(initializer);
        initializer.setController(this);
    }
    
    /**
     * @param initializer The model initializer to register.
     */
    //@ ensures getTraceSelectors().contains(selector);
    public void register(TraceSelector selector) {
        getTraceSelectors().add(selector);
    }
    
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
        if (node.getAppearance() != null) {
            node.appearanceUpdated(null);
            //send(new SetNodeAppearanceCommand(node, node.getAppearance().toMap()));
            //TODO: check if this is right.
        }
    }
    
    /**
     * Remove a <tt>Node</tt> from the visualizer. It is actually replaced by a <tt>NullNode</tt>
     * so no issues occur with the indices of <tt>NodeList</tt> and <tt>id</tt>s of <tt>Node</tt>s.
     * The server will be notified.
     * @param node The <tt>Node</tt> to remove.
     */
    public void removeNode(Node node) {
        Integer id = node.getId();
        NullNode removedNode = new NullNode(node.getType(), node.getName());
        removedNode.setId(id);
        getNodes().set(id, removedNode);
        
        // Add to log.
        Log.add("Node removed: " + node.toString());
        //TODO: remove Relations
        
        // Notify the server.
        send(new RemoveNodeCommand(node));
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
                send(new SetCurrentAnimationDurationCommand(transition.getDuration()));
                transition.execute(traceTransition);
                send(new StartTransitionCommand(transition.getDelay()));
            }
        }
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
        }
    }
    
    /**
     * Let the server know how to initialize the visualizer. This has to be done as the first
     * command.
     * @param width    The width of the canvas.
     * @param height   The height of the canvas.
     * @param duration The default duration of transitions; -1 for unspecified duration.
     */
    //@ requires width > 0 && height > 0 && duration >= -1.0;
    public void initializeVisualizer(double width, double height, double duration) {
        send(new InitializationCommand(width, height, duration));
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
        
        final Map<String, Pattern> possibleArguments = new HashMap<String, Pattern>() {
            {
                put("help",    Pattern.compile("(?i)^-help$"));
                put("verbose", Pattern.compile("(?i)^-verbose$"));
                put("host",    Pattern.compile("(?i)^-host:(?<host>.*)$"));
                put("port",    Pattern.compile("(?i)^-port:(?<port>.*)$"));
                put("model",   Pattern.compile("(?i)^-model:(?<initializer>.*?)"
                                                + "(:(?<parameters>.*))?$"));
                put("trace",   Pattern.compile("(?i)^-trace:(?<selector>.*?)"
                                                + "(:(?<parameters>.*))?$"));
            }
        };
        Log.addOutput(Log.Output.DEFAULT);
        
        Client greenmirror = new Client();
        greenmirror.register(new GroovyScriptModelInitializer());
        greenmirror.register(new FileTraceSelector());
        //TODO: register CommandHandlers.
        
        
        
        
        
        
        
        Log.add("received arguments: " + Arrays.toString(args));
        
        
        boolean exit = false;
        boolean helpAsked = false;
        int counter;
        Matcher matcher = null;
        InetAddress host = null;
        Integer port = null;
        List<ModelInitializer> initializers = new LinkedList<ModelInitializer>();
        TraceSelector traceSelector = null;
        
        // Loop through arguments.
        for (String argument : args) {
            argument = argument.trim();
            // Match the argument to a possible argument.
            
            // -help
            matcher = possibleArguments.get("help").matcher(argument);
            if (matcher.find()) {
                String modelInitializersHelp = "";
                counter = 1;
                for (ModelInitializer mi : greenmirror.getModelInitializers()) {
                    modelInitializersHelp += "\n" + counter;
                    modelInitializersHelp += ". initializer: " + mi.getIdentifier();
                    modelInitializersHelp += "\n    parameters: " + mi.getParameterSpecification();
                    counter++;
                }
                String traceSelectorsHelp = "";
                counter = 1;
                for (TraceSelector ts : greenmirror.getTraceSelectors()) {
                    traceSelectorsHelp +=    "\n" + counter;
                    traceSelectorsHelp +=    ".    selector: " + ts.getIdentifier();
                    traceSelectorsHelp +=    "\n    parameters: " + ts.getParameterSpecification();
                    counter++;
                }
                Log.add(String.format(HELP_MSG, modelInitializersHelp, traceSelectorsHelp));
                //helpAsked = true;
                //TODO: test if the above line is still necessary.
                continue;
            }
            
            // -verbose
            matcher = possibleArguments.get("verbose").matcher(argument);
            if (matcher.find()) {
                Log.setVerbose(true);
                continue;
            }
            
            // -host
            matcher = possibleArguments.get("host").matcher(argument);
            if (matcher.find()) {
                try {
                    host = InetAddress.getByName(matcher.group("host"));
                } catch (UnknownHostException e) {
                    Log.add("The host is unknown.");
                    exit = true;
                }
                continue;
            }
            
            // -port
            matcher = possibleArguments.get("port").matcher(argument);
            if (matcher.find()) {
                try {
                    port = Integer.valueOf(matcher.group("port"));
                } catch (NumberFormatException e) {
                    Log.add("The port number is invalid.");
                    exit = true;
                }
                continue;
            }
            
            // -model
            matcher = possibleArguments.get("model").matcher(argument);
            if (matcher.find()) {
                try {
                    // Loop through all registered ModelInitializers.
                    for (ModelInitializer initializer : greenmirror.getModelInitializers()) {
                        // Check if we're encountering one requested by the user.
                        if (initializer.getIdentifier().equals(matcher.group("initializer"))) {
                            // Remember it.
                            initializers.add(initializer);
                            // Pass the parameters.
                            initializer.setParameters(getParameters(matcher.group("parameters")));
                            // And let it prepare.
                            initializer.prepare();
                        }
                    }
                    if (initializers.isEmpty()) {
                        throw new IllegalArgumentException("the model initializer was not found.");
                    }
                } catch (ModelInitializer.PreparationException e) {
                    Log.add("The model initializer gave an exception: " + e.getMessage());
                    exit = true;
                } catch (GroovyRuntimeException e) {
                    //Log.add("Your Groovy script gave an exception: " + e.getMessage());
                    Log.add("Your Groovy script gave an exception: " + e.getStackTrace());
                    e.printStackTrace();
                    exit = true;
                } catch (IllegalArgumentException e) {
                    Log.add("The parameters are not valid: " + e.getMessage());
                    exit = true;
                }
                continue;
            }
            
            // -trace
            matcher = possibleArguments.get("trace").matcher(argument);
            if (matcher.find()) {
                try {
                    // Loop through all registered TraceSelectors.
                    for (TraceSelector selector : greenmirror.getTraceSelectors()) {
                        // Check if we're encountering the one requested by the user.
                        if (selector.getIdentifier().equals(matcher.group("selector"))) {
                            // Remember it.
                            traceSelector = selector;
                            // Pass the parameters.
                            selector.setParameters(getParameters(matcher.group("parameters")));
                            // And let it prepare.
                            selector.prepare();
                        }
                    }
                    if (traceSelector == null) {
                        throw new IllegalArgumentException("the trace selector was not found.");
                    }
                } catch (TraceSelector.PreparationException e) {
                    Log.add("The trace selector gave an exception: " + e.getMessage());
                    exit = true;
                } catch (IllegalArgumentException e) {
                    Log.add("The parameters are not valid: " + e.getMessage());
                    exit = true;
                }
                continue;
            }
        }
            
        // Now check if all required arguments were set and parsed.
        if ((host == null || port == null || initializers.size() == 0
                || traceSelector == null) && !helpAsked) {
            Log.add("You did not (correctly) pass all required arguments.");
            exit = true;
        }
            
        if (exit) {
            Log.add("For (more) help, type -help");
            return;
        }
        
        
        /* 
         * Now execute! We wrap the executing statements in this single loop, so we can skip
         * to the end for a general exit.
         */
        boolean fullyExecuted = false;
        while (!fullyExecuted) {
            // Connect to the server.
            try {
                greenmirror.connect(host, port);
            } catch (SocketTimeoutException e) {
                Log.add("The connection to the server timed out.");
                break;
            } catch (IOException e) {
                Log.add("IO exception while connecting to the server: " + e.getMessage());
                break;
            }
               
            // Initialize the model.
            try {
                greenmirror.initializeModel(initializers);
                
                /* The initialization of the model might be animated, so we execute the initial 
                 * transition without delay. */
                greenmirror.send(new StartTransitionCommand(0));
                
            } catch (GroovyRuntimeException e) {
                Log.add("Your Groovy script gave an exception: ", e);
                break;
            }
            
            // Check if the trace consists of valid transitions.
            List<String> invalidTraceTransitions = greenmirror.validateTrace(traceSelector);
            if (invalidTraceTransitions != null) {
                Log.add("The following trace transitions could not be deemed valid: " 
                        + invalidTraceTransitions.toString());
                break;
            }
            
            // And execute the trace.
            greenmirror.executeTrace(traceSelector);
            
            fullyExecuted = true;
        }
        if (!fullyExecuted) {
            greenmirror.closeStreams();
            return;
        }
        
        Log.add("We seem to be done. I'm closing down now.");
        greenmirror.closeStreams();
    }
    
    
    
    private static String[] getParameters(String parameters) {
        List<String> result = new LinkedList<String>();
        for (String parameter : parameters.split(":")) {
            if (parameter != null && parameter.length() > 0) {
                result.add(parameter);
            }
        }
        return result.toArray(new String[0]);
    }
    
    
    
    // FileTraceSelector test
    public static void main2(String[] args) {
        try {
            TraceSelector ts = new FileTraceSelector();
            ts.setParameters(new String[]{"trace"});
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
            gsmi.setParameters(new String[]{"initialize_script.groovy"});
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