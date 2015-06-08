package greenmirror.client;

import greenmirror.FxWrapper;
import greenmirror.Node;
import greenmirror.NodeList;
import greenmirror.Placement;
import greenmirror.Relation;
import greenmirror.commands.FlushCommand;
import greenmirror.commands.SetAnimationDurationCommand;
import greenmirror.commands.SwitchPlacementRelationCommand;
import greenmirror.placements.CustomPlacement;
import greenmirror.placements.RandomPlacement;
import groovy.lang.Binding;
import groovy.lang.Closure;
import groovy.lang.Script;

import org.eclipse.jdt.annotation.NonNull;

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
     * <code>Binding</code>.
     * @param binding The <code>Binding</code> containing the controller.
     */
    //@ requires binding != null && binding.hasVariable("GreenMirrorController");
    //@ ensures getController() != null;
    public GreenMirrorGroovyBaseScript(Binding binding) {
        setController((Client) binding.getVariable("GreenMirrorController"));
    }
    
    
    // -- Class usage ------------------------------------------------------------------------

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
        initialize(width, height, -1.0, true);
    }
    
    /**
     * Initialize the visualizer.
     * @param width    The width of the canvas.
     * @param height   The height of the canvas.
     * @param duration The default duration for transitions (in milliseconds); -1 for 
     *                 unspecified duration; 0 if you don't want animations to play
     */
    //@ requires width > 0 && height > 0 && duration >= -1.0;
    public void initialize(double width, double height, double duration) {
        initialize(width, height, duration, true);
    }
    
    /**
     * Initialize the visualizer.
     * @param width    The width of the canvas.
     * @param height   The height of the canvas.
     * @param rotateRigidlyRelatedNodesRigidly
     *                 {@see greenmirror.server.Visualizer#getRotateRigidlyRelatedNodesRigidly()}
     */
    //@ requires width > 0 && height > 0 && duration >= -1.0;
    public void initialize(double width, double height, boolean rotateRigidlyRelatedNodesRigidly) {
        initialize(width, height, -1.0, rotateRigidlyRelatedNodesRigidly);
    }
    
    /**
     * Initialize the visualizer.
     * @param width    The width of the canvas.
     * @param height   The height of the canvas.
     * @param duration The default duration for transitions (in milliseconds); -1 for 
     *                 unspecified duration; 0 if you don't want animations to play
     * @param rotateRigidlyRelatedNodesRigidly
     *                 {@see greenmirror.server.Visualizer#getRotateRigidlyRelatedNodesRigidly()}
     */
    //@ requires width > 0 && height > 0 && duration >= -1.0;
    public void initialize(double width, double height, double duration, 
            boolean rotateRigidlyRelatedNodesRigidly) {
        getController().initializeVisualizer(width, height, duration, 
                rotateRigidlyRelatedNodesRigidly);
    }
    
    
    // -- Groovy script: queries --------------------------

    /**
     * @return (A copy of) the list of <code>Node</code>s on the visualizer.
     */
    //@ ensures \result != null;
    /*@ pure */ public NodeList nodes() {
        return new NodeList(getController().getNodes());
    }
    
    /**
     * Get a list of <code>Node</code>s on the visualizer with a specific identifier.
     * @param identifier {@link greenmirror.Node.Identifier#Identifier(String)}
     * @return           A list in which every <code>Node</code> corresponds to <code>identifier</code>.
     */
    //@ requires identifier != null;
    //@ ensures \result != null;
    /*@ pure */ public NodeList nodes(String identifier) {
        return getController().getNodes(identifier);
    }

    /**
     * Get the first node on the visualizer that corresponds to <code>identifier</code>.
     * @param identifier {@link greenmirror.Node.Identifier#Identifier(String)}
     * @return           The <code>Node</code>.
     * @throws IllegalArgumentException If the Node was not found.
     */
    //@ requires identifier != null;
    /*@ pure */ public Node node(String identifier) {
        NodeList list = nodes(identifier);
        if (list.isEmpty()) {
            throw new IllegalArgumentException("No nodes were found that correspond to the "
                    + "identifier \"" + identifier + "\".");
        }
        return list.getFirst();
    }
    
    
    // -- Groovy script: commands -------------------------

    /**
     * Add a node with identifier <code>name</code> to the visualizer.
     * @param identifier The identifier of the node. See 
     *             {@link greenmirror.Node.Identifier#Identifier(String)}.
     * @return     The newly made (and added) <code>Node</code>.
     */
    //@ requires identifier != null;
    //@ ensures nodes(identifier).size() > 0;
    public Node addNode(String identifier) {
        return addNode(new Node(identifier));
    }

    /**
     * Add a node to the visualizer.
     * @param node The new <code>Node</code>.
     * @return     The newly added <code>Node</code>.
     */
    //@ requires node != null;
    //@ ensures \result == node;
    public Node addNode(Node node) {
        getController().addNode(node);
        return node;
    }
    
    /**
     * Add as many nodes as you want in one statement.
     * @param nodes An array of nodes.
     */
    public void addNodes(Node... nodes) {
        for (Node node : nodes) {
            addNode(node);
        }
    }
    
    /**
     * Add a <code>Relation</code>.
     * @param relation
     */
    //@ requires relation != null;
    //@ ensures relation.getNodeA().hasRelation(relation);
    //@ ensures relation.getNodeB().hasRelation(relation); 
    public void addRelation(Relation relation) {
        getController().addRelation(relation);
    }
    
    /**
     * Add multiple <code>Relation</code>s.
     * @param relations
     */
    public void addRelations(Relation... relations) {
        for (Relation relation : relations) {
            addRelation(relation);
        }
    }
    
    
    public void switchPlacementRelation(Relation newRelation) {
        Node nodeA = newRelation.getNodeA();
        if (!nodeA.hasPlacementRelation() || newRelation.getPlacement() == Placement.NONE) {
            addRelation(newRelation);
            return;
        }
        Relation currentPlacementRelation = nodeA.getPlacementRelation();
        
        // If placement was random, it has been changed to a custom placement, so we need to
        // address it as such (coordinate details are irrelevant at this point).
        if (currentPlacementRelation.getPlacement() instanceof RandomPlacement) {
            currentPlacementRelation.setPlacement(new CustomPlacement());
        }
        
        getController().send(
                new SwitchPlacementRelationCommand(currentPlacementRelation, newRelation));
        currentPlacementRelation.removeFromNodes();
        newRelation.addToNodes();
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
    
    public void addTransition(String transitionRegex, double duration, 
                              boolean supplemental, Closure<Object> code) {
        getController().getTransitions().add(
                new ModelTransition(transitionRegex, code, duration, supplemental));
    }
    
    /**
     * Set the duration of all single (upcoming) animations. This means that when <code>flush()</code>
     * is used, the total duration is doubled. If <code>-1</code> is passed, the duration is set to the
     * default (as determined by the default duration per transition or for the whole visualizer).
     * @param duration The duration in milliseconds; <code>-1</code> to set it to default; 0 if 
     *                 you don't want the animation to play
     */
    //@ requires duration >= -1.0;
    public void setAnimationDuration(double duration) {
        getController().send(new SetAnimationDurationCommand(duration));;
    }
    
    /**
     * Create a new <code>FxWrapper</code>.
     * @param type The type of the <code>FxWrapper</code>.
     * @return     The <code>FxWrapper</code> instance.
     * @throws IllegalArgumentException If the type was invalid.
     */
    //@ requires type != null;
    public FxWrapper fx(@NonNull String type) {
        return FxWrapper.getNewInstance(type);
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
     * Remove a <code>Node</code> from the visualizer.
     * @param node
     */
    //@ requires node != null;
    //@ ensures !getController().getNodes().contains(node);
    public void removeNode(Node node) {
        getController().removeNode(node);
    }

    /**
     * Remove all <code>Node</code>s from <code>nodeList</code> from the visualizer.
     * @param nodeList The <code>Node</code>s that will be removed.
     */
    //@ requires nodes != null;
    //@ ensures nodes().size() == \old(nodes().size()) - nodes.size();
    public void removeNodes(NodeList nodeList) {
        nodeList.forEach(node -> removeNode(node));
    }

    /**
     * Remove all passed <code>Node</code>s from the visualizer.
     * @param nodes The <code>Node</code>s that will be removed.
     */
    public void removeNodes(Node... nodes) {
        removeNodes(new NodeList(nodes));
    }
    
    /**
     * Remove a <code>Relation</code> from the visualizer.
     * @param relation
     */
    //@ requires relation != null;
    //@ ensures !relation.getNodeA().hasRelation(relation);
    //@ ensures !relation.getNodeB().hasRelation(relation); 
    public void removeRelation(Relation relation) {
        getController().removeRelation(relation);
    }
    
    /**
     * Remove all passed <code>Relation</code>s from the visualizer.
     * @param relations
     */
    public void removeRelations(Relation... relations) {
        for (Relation relation : relations) {
            removeRelation(relation);
        }
    }
    
    /**
     * Fail!
     */
    public void fail() {
        throw new IllegalStateException("Your Groovy script encountered a fail() call.");
    }
    
    public void fail(String msg) {
        throw new IllegalStateException("Your Groovy script encountered a fail: " + msg);
    }
}