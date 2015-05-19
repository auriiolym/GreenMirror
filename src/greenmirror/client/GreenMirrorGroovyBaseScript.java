package greenmirror.client;

import greenmirror.FxContainer;
import greenmirror.Node;
import greenmirror.NodeList;
import greenmirror.Relation;
import greenmirror.commands.AddRelationCommand;
import greenmirror.commands.FlushCommand;
import greenmirror.commands.SetCurrentAnimationDurationCommand;
import greenmirror.commands.SwitchPlacementRelationCommand;
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
     * @return           The <tt>Node</tt>.
     * @throws IllegalArgumentException If the Node was not found.
     */
    //@ requires identifier != null;
    /*@ pure */ public Node node(String identifier) {
        NodeList list = nodes(identifier).one();
        if (list.isEmpty()) {
            throw new IllegalArgumentException("No nodes were found that correspond to the "
                    + "identifier \"" + identifier + "\".");
        }
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
     * Add as many nodes as you want in one statement.
     * @param nodes An array or list of nodes.
     */
    public void addNodes(Node... nodes) {
        for (Node node : nodes) {
            addNode(node);
        }
    }
    
    //@ requires relation != null;
    public void addRelation(Relation relation) {
        relation.addToNodes();
        getController().send(new AddRelationCommand(relation));
    }
    
    public void addRelations(Relation... relations) {
        for (Relation relation : relations) {
            addRelation(relation);
        }
    }
    
    
    public void switchPlacementRelation(Relation newRelation) {
        Node nodeA = newRelation.getNodeA();
        if (!nodeA.hasPlacementRelation()) {
            addRelation(newRelation);
            return;
        }
        Relation currentPlacementRelation = nodeA.getPlacementRelation();
        
        getController().send(new SwitchPlacementRelationCommand(currentPlacementRelation, newRelation));
        currentPlacementRelation.remove();
        newRelation.addToNodes();
    }
    
    /**
     * Add a transition to the list of possible transitions.
     * @param transitionPattern The <tt>Pattern</tt> that indicates the transition name.
     * @param code              The code that will be executed when the transition executes.
     */
    //@ requires transitionPattern != null && code != null;
    public void addTransition(Pattern transitionPattern, Closure<Object> code) {
        getController().getTransitions().add(
                new ModelTransition(transitionPattern, code, -1.0));
    }

    /**
     * Add a transition to the list of possible transitions.
     * @param transitionRegex The (regex) string that indicates the transition name.
     * @param code            The code that will be executed when the transition executes.
     */
    //@ requires transitionRegex != null && code != null;
    public void addTransition(String transitionRegex, Closure<Object> code) {
        getController().getTransitions().add(
                new ModelTransition(transitionRegex, code, -1.0));
    }
    
    /**
     * Add a transition to the list of possible transitions.
     * @param transitionPattern The <tt>Pattern</tt> that indicates the transition name.
     * @param duration          {@link greenmirror.client.ModelTransition#duration}
     * @param code              The code that will be executed when the transition executes.
     */
    //@ requires transitionPattern != null && duration >= -1.0 && code != null;
    public void addTransition(Pattern transitionPattern, double duration, 
                              Closure<Object> code) {
        getController().getTransitions().add(
                new ModelTransition(transitionPattern, code, duration));
    }

    /**
     * Add a transition to the list of possible transitions.
     * @param transitionRegex The (regex) string that indicates the transition name.
     * @param duration        {@link greenmirror.client.ModelTransition#duration}
     * @param code            The code that will be executed when the transition executes.
     */
    //@ requires transitionRegex != null && duration >= -1.0 && code != null;
    public void addTransition(String transitionRegex, double duration, 
                              Closure<Object> code) {
        getController().getTransitions().add(
                new ModelTransition(transitionRegex, code, duration));
    }
    
    /**
     * @param duration The duration in milliseconds of all upcoming animations.
     */
    //@ requires duration >= 0;
    public void setAnimationDuration(double duration) {
        getController().send(new SetCurrentAnimationDurationCommand(duration));;
    }
    
    /**
     * Create a new <tt>FxContainer</tt>.
     * @param type The type of the <tt>FxContainer</tt>.
     * @return     The <tt>FxContainer</tt> instance.
     * @throws IllegalArgumentException If the type was invalid.
     */
    //@ requires type != null;
    public FxContainer fx(String type) {
        return FxContainer.getNewInstance(type);
    }
    
    /**
     * Flushes the animations: all upcoming animations will be animated after the previous ones 
     * (and not in parallel, as is the default).
     */
    public void flush() {
        flush(0);
    }
    
    /**
     * Flushes the animations: all upcoming animations will be animated after the previous ones 
     * (and not in parallel, as is the default). Also, a delay is added after the previous 
     * animations.
     */
    public void flush(double delay) {
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