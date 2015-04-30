package greenmirror.client;

import greenmirror.Node;
import greenmirror.NodeList;
import greenmirror.commands.FlushCommand;
import greenmirror.commands.SetCurrentAnimationDurationCommand;
import groovy.lang.Binding;
import groovy.lang.Closure;
import groovy.lang.Script;

import java.util.regex.Pattern;

// Extends groovy.lang.Script.
/**
 * The base class available for the Groovy model initializer. All public methods are 
 * available in any Groovy script that has this class as its base class.
 * 
 * @author Karim El Assal
 */
public class GreenMirrorGroovyBaseScript extends Script {

    // -- Instance variables -----------------------------------------------------------------
    
    /**
     * The controller.
     */
    //@ private invariant controller != null;
    private Client controller;


    // -- Constructors -----------------------------------------------------------------------
    
    /**
     * Groovy creates the new instance of this base class and passes the controller through a
     * <tt>Binding</tt>.
     * @param binding The <tt>Binding</tt> containing the controller.
     */
    //@ requires binding != null && binding.hasVariable("GreenMirrorController");
    //@ ensures getController() != null;
    public GreenMirrorGroovyBaseScript(Binding binding) {
        setController((Client) binding.getVariable("GreenMirrorController"));
    }
    
    
    // -- Class usage ------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see groovy.lang.Script#run()
     */
    @Override
    public Object run() {
        return null;
    }
    
    // -- Queries ----------------------------------------------------------------------------

    /**
     * @return The controller.
     */
    //@ ensures \result != null;
    /*@ pure */ private Client getController() {
        return controller;
    }
    
    // -- Setters ----------------------------------------------------------------------------

    /**
     * @param controller The controller to set.
     */
    //@ requires controller != null;
    //@ ensures getController() == controller;
    private void setController(Client controller) {
        this.controller = controller;
    }
    
    
    // -- Commands for use within a Groovy script --------------------------------------------
    
    // -- Groovy script: initializers ---------------------

    /**
     * Initialize the visualizer.
     * @param width  The width of the canvas.
     * @param height The height of the canvas.
     */
    //@ requires width > 0 && height > 0;
    public void initialize(double width, double height) {
        initialize(width, height, -1.0);
    }
    
    /**
     * Initialize the visualizer.
     * @param width    The width of the canvas.
     * @param height   The height of the canvas.
     * @param duration The default duration for transitions (in milliseconds); -1 for 
     *                 unspecified duration.
     */
    //@ requires width > 0 && height > 0 && duration >= -1.0;
    public void initialize(double width, double height, double duration) {
        getController().initializeVisualizer(width, height, duration);
    }
    
    
    // -- Groovy script: queries --------------------------

    /**
     * @return (A copy of) the list of <tt>Node</tt>s on the visualizer.
     */
    //@ ensures \result != null;
    /*@ pure */ public NodeList nodes() {
        return new NodeList(getController().getNodes());
    }
    
    /**
     * Get a list of <tt>Node</tt>s on the visualizer with a specific identifier.
     * @param identifier {@link greenmirror.Node.Identifier#Identifier(String)}
     * @return           A list in which every <tt>Node</tt> corresponds to <tt>identifier</tt>.
     */
    //@ requires identifier != null;
    //@ ensures \result != null;
    /*@ pure */ public NodeList nodes(String identifier) {
        return getController().getNodes(identifier);
    }

    /**
     * Get the first node on the visualizer that corresponds to <tt>identifier</tt>.
     * @param identifier {@link greenmirror.Node.Identifier#Identifier(String)}
     * @return           The <tt>Node</tt>; <tt>null</tt> if it was not found.
     */
    //@ requires identifier != null'
    /*@ pure */ public Node node(String identifier) {
        NodeList list = nodes(identifier).one();
        return list.isEmpty() ? null : list.getFirst();
    }
    
    
    // -- Groovy script: commands -------------------------

    /**
     * Add a node with identifier <tt>name</tt> to the visualizer.
     * @param identifier The identifier of the node. See 
     *             {@link greenmirror.Node.Identifier#Identifier(String)}.
     * @return     The newly made (and added) <tt>Node</tt>.
     */
    //@ requires identifier != null;
    //@ ensures nodes(identifier).size() > 0;
    public Node addNode(String identifier) {
        return addNode(new Node(identifier));
    }

    /**
     * Add a node to the visualizer.
     * @param node The new <tt>Node</tt>.
     * @return     The newly added <tt>Node</tt>.
     */
    //@ requires node != null;
    //@ ensures \result == node;
    public Node addNode(Node node) {
        getController().addNode(node);
        return node;
    }
    
    /**
     * Add a transition to the list of possible transitions.
     * @param transitionPattern The <tt>Pattern</tt> that indicates the transition name.
     * @param code              The code that will be executed when the transition executes.
     */
    //@ requires transitionPattern != null && code != null;
    public void addTransition(Pattern transitionPattern, Closure<Object> code) {
        getController().getTransitions().add(
                new ModelTransition(transitionPattern, code, -1.0, 0.0));
    }

    /**
     * Add a transition to the list of possible transitions.
     * @param transitionRegex The (regex) string that indicates the transition name.
     * @param code            The code that will be executed when the transition executes.
     */
    //@ requires transitionRegex != null && code != null;
    public void addTransition(String transitionRegex, Closure<Object> code) {
        getController().getTransitions().add(
                new ModelTransition(transitionRegex, code, -1.0, 0.0));
    }
    
    /**
     * Add a transition to the list of possible transitions.
     * @param transitionPattern The <tt>Pattern</tt> that indicates the transition name.
     * @param duration          {@link greenmirror.client.ModelTransition#duration}
     * @param delay             {@link greenmirror.client.ModelTransition#delay}
     * @param code              The code that will be executed when the transition executes.
     */
    //@ requires transitionPattern != null && duration >= -1.0 && delay >= 0.0 && code != null;
    public void addTransition(Pattern transitionPattern, double duration, 
                                double delay, Closure<Object> code) {
        getController().getTransitions().add(
                new ModelTransition(transitionPattern, code, duration, delay));
    }

    /**
     * Add a transition to the list of possible transitions.
     * @param transitionRegex The (regex) string that indicates the transition name.
     * @param duration        {@link greenmirror.client.ModelTransition#duration}
     * @param delay             {@link greenmirror.client.ModelTransition#delay}
     * @param code            The code that will be executed when the transition executes.
     */
    //@ requires transitionRegex != null && duration >= -1.0 && delay >= 0.0 && code != null;
    public void addTransition(String transitionRegex, double duration, 
                                double delay, Closure<Object> code) {
        getController().getTransitions().add(
                new ModelTransition(transitionRegex, code, duration, delay));
    }
    
    /**
     * @param duration The duration in milliseconds of all upcoming animations.
     */
    //@ requires duration >= 0;
    public void setAnimationDuration(double duration) {
        getController().send(new SetCurrentAnimationDurationCommand(duration));;
    }
    
    /**
     * Flushes the animations: all upcoming animations will be animated after the previous ones 
     * (and not in parallel, as is the default).
     */
    public void flush() {
        getController().send(new FlushCommand(0.0));
    }
    
    /**
     * Flushes the animations: all upcoming animations will be animated after the previous ones 
     * (and not in parallel, as is the default). Also, a delay is added after the previous 
     * animations.
     */
    public void flushWithDelay(double delay) {
        getController().send(new FlushCommand(delay));
    }

    /**
     * Remove several <tt>Node</tt>s from the visualizer.
     * @param nodes The <tt>Node</tt>s that will be removed.
     */
    //@ requires nodes != null;
    //@ ensures nodes().size() == \old(nodes().size()) - nodes.size();
    public void removeNodes(NodeList nodes) {
        nodes.forEach(node -> {
            getController().removeNode(node);
        });
    }
    
    public void removeNode(Node... nodes) {
        removeNodes(new NodeList(nodes));
    }
}