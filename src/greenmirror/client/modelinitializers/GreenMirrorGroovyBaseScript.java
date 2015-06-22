package greenmirror.client.modelinitializers;

import greenmirror.FxWrapper;
import greenmirror.Log;
import greenmirror.Node;
import greenmirror.NodeList;
import greenmirror.Relation;
import greenmirror.RelationList;
import greenmirror.client.Client;
import greenmirror.client.ModelTransition;
import greenmirror.commands.FlushCommand;
import greenmirror.commands.SetAnimationDurationCommand;
import groovy.lang.Binding;
import groovy.lang.Closure;
import groovy.lang.Script;

import org.eclipse.jdt.annotation.NonNull;

/**
 * The base class available for the Groovy model initializer. All public methods are 
 * available in any Groovy script that has this class as its base class.
 * 
 * @author Karim El Assal
 */
public class GreenMirrorGroovyBaseScript extends Script {

    // -- Instance variables -----------------------------------------------------------------
    
    /** the controller */
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
    public GreenMirrorGroovyBaseScript(@NonNull Binding binding) {
        this.controller = (Client) binding.getVariable("GreenMirrorController");
    }
    
    
    // -- Class usage ------------------------------------------------------------------------

    @Override
    public Object run() {
        return null;
    }
    
    // -- Queries ----------------------------------------------------------------------------

    /** @return the controller */
    //@ ensures \result != null;
    /*@ pure */ private Client getController() {
        return controller;
    }
    
    
    // -- Commands for use within a Groovy script --------------------------------------------
    
    // -- Groovy script: initializers ---------------------

    /**
     * Initializes the visualizer with only the width and height.
     * 
     * @param width  the width of the canvas
     * @param height the height of the canvas
     * @throws IllegalArgumentException if the width and/or height are zero or negative
     */
    //@ requires width > 0 && height > 0;
    public void initialize(double width, double height) {
        if (width <= 0 || height <= 0) {
            throw new IllegalArgumentException("width and/or height are invalid");
        }
        initialize(width, height, -1.0, true);
    }
    
    /**
     * Initializes the visualizer with a default animation duration set.
     * 
     * @param width  the width of the canvas
     * @param height the height of the canvas
     * @param duration the default duration for animations (in milliseconds); see 
     *                 {@link SetAnimationDurationCommand} for details
     * @throws IllegalArgumentException if the width and/or height are zero or negative, or if 
     *                                  the duration is invalid
     */
    //@ requires width > 0 && height > 0 && duration >= -1.0;
    public void initialize(double width, double height, double duration) {
        if (width <= 0 || height <= 0 || duration < 1.0) {
            throw new IllegalArgumentException("width, height and/or duration are invalid");
        }
        initialize(width, height, duration, true);
    }
    
    /**
     * Initializes the visualizer with the <code>rotateRigidlyRelatedNodesRigidly</code> setting
     * (see {@link greenmirror.commands.InitializationCommand}).
     * 
     * @param width  the width of the canvas
     * @param height the height of the canvas
     * @param rotateRigidlyRelatedNodesRigidly see 
     *                                  {@link greenmirror.commands.InitializationCommand}
     * @throws IllegalArgumentException if the width and/or height are zero or negative
     * @see greenmirror.commands.InitializationCommand
     */
    //@ requires width > 0 && height > 0 && duration >= -1.0;
    public void initialize(double width, double height, boolean rotateRigidlyRelatedNodesRigidly) {
        if (width <= 0 || height <= 0) {
            throw new IllegalArgumentException("width and/or height are invalid");
        }
        initialize(width, height, -1.0, rotateRigidlyRelatedNodesRigidly);
    }
    
    /**
     * Initializes the visualizer with both the default animation duration and the
     * <code>rotateRigidlyRelatedNodesRigidly</code> setting set
     * (see {@link greenmirror.commands.InitializationCommand}).
     * 
     * @param width  the width of the canvas
     * @param height the height of the canvas
     * @param duration the default duration for animations (in milliseconds); see 
     *                 {@link SetAnimationDurationCommand} for details
     * @param rotateRigidlyRelatedNodesRigidly see 
     *                                  {@link greenmirror.commands.InitializationCommand}
     * @throws IllegalArgumentException if the width and/or height are zero or negative, or if 
     *                                  the duration is invalid
     * @see     greenmirror.commands.InitializationCommand
     * @see     greenmirror.commands.SetAnimationDurationCommand
     */
    //@ requires width > 0 && height > 0 && duration >= -1.0;
    public void initialize(double width, double height, double duration, 
            boolean rotateRigidlyRelatedNodesRigidly) {
        if (width <= 0 || height <= 0 || duration < -1.0) {
            throw new IllegalArgumentException("width, height and/or duration are invalid");
        }
        getController().initializeVisualizer(width, height, duration, 
                rotateRigidlyRelatedNodesRigidly);
    }
    
    
    // -- Groovy script: queries --------------------------

    /** @return (a copy of) the list of {@link Node}s on the visualizer */
    /*@ pure */ @NonNull public NodeList nodes() {
        return new NodeList(getController().getNodes());
    }
    
    /**
     * Gets a list of {@link Node}s on the visualizer with a specific identifier.
     * 
     * @param identifier see {@link Node.Identifier#Identifier(String)}
     * @return          a list in which every <code>Node</code> corresponds to 
     *                  <code>identifier</code>
     */
    /*@ pure */ @NonNull public NodeList nodes(@NonNull String identifier) {
        return getController().getNodes(identifier);
    }

    /**
     * Gets the first node on the visualizer that corresponds to <code>identifier</code>.
     * 
     * @param identifier see {@link Node.Identifier#Identifier(String)}
     * @return           the {@link Node}
     * @throws IllegalArgumentException if the node was not found
     */
    /*@ pure */ public Node node(@NonNull String identifier) {
        final NodeList list = nodes(identifier);
        if (list.isEmpty()) {
            throw new IllegalArgumentException("no nodes were found that correspond to the "
                    + "identifier \"" + identifier + "\"");
        }
        return list.getFirst();
    }
    
    
    // -- Groovy script: commands -------------------------

    /**
     * Adds a node with <code>identifier</code> to the visualizer.
     * 
     * @param identifier the identifier of the node. See {@link Node.Identifier#Identifier(String)}
     * @return           the newly created (and added) {@link Node}
     */
    //@ ensures nodes(identifier).size() > 0;
    @NonNull public Node addNode(String identifier) {
        return addNode(new Node(identifier));
    }

    /**
     * Adds a node to the visualizer.
     * 
     * @param node the new {@link Node}
     * @return     the newly added <code>Node</code>
     */
    @NonNull public Node addNode(@NonNull Node node) {
        getController().addNode(node);
        return node;
    }
    
    /**
     * Adds as many nodes as are passed, in one statement.
     * 
     * @param nodes an array of {@link Node}s
     */
    public void addNodes(@NonNull Node... nodes) {
        for (Node node : nodes) {
            if (node != null) {
                addNode(node);
            }
        }
    }
    
    /**
     * Adds a {@link Relation} to the controller and the visualizer. If it's a placement
     * relation and the node A already has a placement relation, it gets overwritten.
     * 
     * @param relation the relation to add
     */
    //@ requires relation.getNodeA() != null;
    //@ requires relation.getNodeB() != null;
    //@ ensures relation.getNodeA().hasRelation(relation);
    //@ ensures relation.getNodeB().hasRelation(relation); 
    public void addRelation(@NonNull Relation relation) {
        getController().addRelation(relation);
    }
    
    /**
     * Adds multiple {@link Relation}s.
     * 
     * @param relations the relations to add
     * @see   #addRelation(Relation)
     */
    public void addRelations(@NonNull Relation... relations) {
        for (Relation relation : relations) {
            if (relation != null) {
                addRelation(relation);
            }
        }
    }
    
    /**
     * This is a synonym of {@link #addRelation(Relation)}, because {@link #addRelation(Relation)}
     * replaces the placement relation if the passed relation also is a placement relation.
     * 
     * @param newRelation the new relation
     * @see   #addRelation(Relation)
     */
    public void switchPlacementRelation(@NonNull Relation newRelation) {
        addRelation(newRelation);
    }

    /**
     * Adds to the list of possible state-transitions a new transition with a default 
     * animation duration and a false <code>supplemental</code> setting. 
     * See {@link #addTransition(String, double, boolean, Closure)}.
     * 
     * @param transitionRegex the (regex) string that indicates the transition labels it 
     *                        should match 
     * @param code            the code that will be executed when the transition executes
     * @see                   #addTransition(String, double, boolean, Closure)
     */
    public void addTransition(@NonNull String transitionRegex, @NonNull Closure<Object> code) {
        addTransition(transitionRegex, -1.0, false, code);
    }

    /**
     * Adds to the list of possible state-transitions a new transition with an animation 
     * duration and a false <code>supplemental</code> setting. 
     * See {@link #addTransition(String, double, boolean, Closure)}.
     * 
     * @param transitionRegex the (regex) string that indicates the transition labels it 
     *                        should match 
     * @param duration        see {@link greenmirror.commands.SetAnimationDurationCommand}
     * @param code            the code that will be executed when the transition executes
     * @see                   #addTransition(String, double, boolean, Closure)
     */
    //@ requires duration >= -1.0;
    public void addTransition(@NonNull String transitionRegex, double duration, 
                              @NonNull Closure<Object> code) {
        addTransition(transitionRegex, duration, false, code);
    }

    /**
     * Adds to the list of possible state-transitions a new transition with an animation 
     * duration and a <code>supplemental</code> setting. 
     * 
     * @param transitionRegex the (regex) string that indicates the transition labels it 
     *                        should match 
     * @param duration        see {@link greenmirror.commands.SetAnimationDurationCommand}
     * @param supplemental    whether this transition is supplemental to a previous or next
     *                        one. If so, the controller won't send an 
     *                        {@link greenmirror.commands.EndTransitionCommand} after this
     *                        transition finishes
     * @param code            the code that will be executed when the transition executes
     * @see                   #addTransition(String, double, boolean, Closure)
     * @see                   greenmirror.client.ModelTransition
     */
    //@ requires duration >= -1.0;
    public void addTransition(@NonNull String transitionRegex, double duration, 
                              boolean supplemental, @NonNull Closure<Object> code) {
        getController().getTransitions().add(
                new ModelTransition(transitionRegex, code, duration, supplemental));
    }
    
    /**
     * Sets the duration of all single (upcoming) animations. This means that when 
     * {@link #flush()} is used, the total duration is doubled. If <code>-1</code> 
     * is passed, the duration is set to the default value. See
     * {@link greenmirror.commands.SetAnimationDurationCommand} for details on the default 
     * value.
     *  
     * @param duration the duration in milliseconds; <code>-1</code> to set it to default; 0 if 
     *                 you don't want the animation to play at all
     * @see            greenmirror.commands.SetAnimationDurationCommand
     */
    //@ requires duration >= -1.0;
    public void setAnimationDuration(double duration) {
        getController().send(new SetAnimationDurationCommand(duration));
    }
    
    /**
     * Creates a new {@link FxWrapper}.
     * 
     * @param type the type of the <code>FxWrapper</code>
     * @return     the <code>FxWrapper</code> instance
     * @throws IllegalArgumentException if the type was invalid
     */
    @NonNull public FxWrapper fx(@NonNull String type) {
        return FxWrapper.getNewInstance(type);
    }
    
    /**
     * Flushes the animations: all upcoming animations will be animated after the previous ones 
     * (and not in parallel, as is the default) without delay.
     */
    public void flush() {
        flush(0);
    }
    
    /**
     * Flushes the animations: all upcoming animations will be animated after the previous ones 
     * (and not in parallel, as is the default). Also, a delay is added after the previous 
     * animations.
     * 
     * @param delay the delay in miliseconds
     */
    public void flush(double delay) {
        getController().send(new FlushCommand(delay));
    }
    
    /**
     * Removes a {@link Node} from the visualizer.
     * 
     * @param node the node to remove
     */
    //@ ensures !getController().getNodes().contains(node);
    public void removeNode(@NonNull Node node) {
        getController().removeNode(node);
    }

    /**
     * Removes all {@link Node}s on <code>nodeList</code> from the visualizer.
     * 
     * @param nodeList the nodes that will be removed
     */
    //@ ensures nodes().size() == \old(nodes().size()) - nodeList.size();
    public void removeNodes(@NonNull NodeList nodeList) {
        for (Node node : nodeList) {
            if (node != null) {
                removeNode(node);
            }
        }
    }

    /**
     * Removes all passed {@link Node}s from the visualizer.
     * 
     * @param nodes the nodess that will be removed
     */
    //@ ensures nodes().size() == \old(nodes().size()) - nodes.size();
    public void removeNodes(@NonNull Node... nodes) {
        removeNodes(new NodeList(nodes));
    }
    
    /**
     * Removes a {@link Relation} from the visualizer.
     * 
     * @param relation the relation; if <code>null</code> is passed, nothing happens
     */
    //@ ensures relation != null ? !relation.getNodeA().hasRelation(relation) : true;
    //@ ensures relation != null ? !relation.getNodeB().hasRelation(relation) : true; 
    public void removeRelation(Relation relation) {
        getController().removeRelation(relation);
    }
    
    /**
     * Removes all passed {@link Relation}s from the visualizer.
     * 
     * @param relations the relations to remove
     */
    public void removeRelations(Relation... relations) {
        if (relations != null) {
            for (Relation relation : relations) {
                removeRelation(relation);
            }
        }
    }
    
    /**
     * Removes all passed {@link Relation}s from the visualizer.
     * 
     * @param relations the relations to remove
     */
    public void removeRelations(RelationList relations) {
        removeRelations(relations.toArray(new Relation[]{}));
    }
    
    /**
     * Sends all node and relation data to the log. Used for debugging.
     */
    public void sendStateToLog() {
        String str = "Here are all the current nodes with their data.";
        for (Node node : nodes()) {
            str += "\n" + node.toString();
        }
        Log.add(str);
    }
    
    /**
     * Lets the script fail by throwing an {@link IllegalStateException}.
     * 
     * @throws IllegalStateException because that's the purpose of this method
     */
    public void fail() {
        throw new IllegalStateException("your Groovy script encountered a fail() call");
    }

    /**
     * Let the script fail by throwing an {@link IllegalStateException} with a message.
     * 
     * @param msg the message indicating why the script failed
     * @throws IllegalStateException because that's the purpose of this method
     */
    public void fail(String msg) {
        throw new IllegalStateException("your Groovy script encountered a fail: " + msg);
    }
}