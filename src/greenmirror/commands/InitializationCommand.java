package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import greenmirror.Relation;
import greenmirror.server.Visualizer;
import groovy.json.JsonOutput;

import org.eclipse.jdt.annotation.NonNull;

import java.util.LinkedHashMap;

/**
 * The command to initialize the visualizer. This command is sent to the server.
 * 
 * <table><caption>Values sent:</caption>
 * <tr><th>variable</th><th>type</th><th>description</th></tr>
 * <tr><td>width </td><td>int</td><td>      the width of the window</td></tr>
 * <tr><td>height </td><td>int</td><td>     the height of the window</td></tr>
 * <tr><td>defaultAnimationDuration </td><td>double</td><td>
 *                      the default time animations will take. See
 *                      {@link SetAnimationDurationCommand} for details</td></tr>
 * <tr><td>rotateRigidlyRelatedNodesRigidly </td><td>boolean</td><td>
 *                      This setting determines if the "A" node of a rigid relation should rotate
 *                      rigidly when the "B" node is rotated. This feature is not finished and is
 *                      still buggy. When set to true, the "A" node gets the same rotation as the
 *                      "B" node, resulting in its original rotation being overridden. When set
 *                      to false, node A doesn't rotate which might be desirable with specific
 *                      models. See the implementation of {@link Visualizer#doPlacement(Relation)}
 *                      for the specific workings.</td></tr>
 * </table>
 * 
 * @author  Karim El Assal
 * @see     InitializationCommandHandler
 * @see     SetAnimationDurationCommand
 */
public class InitializationCommand extends Command {
    
    
    // -- Instance variables -----------------------------------------------------------------

    //@ private invariant width > 0;
    private double width;
    //@ private invariant height > 0;
    private double height;
    //@ private invariant defaultAnimationDuration >= -1.0;
    private double defaultAnimationDuration;
    private boolean rotateRigidlyRelatedNodesRigidly;

    // -- Constructors -----------------------------------------------------------------------

    /**
     * Initializes this {@link greenmirror.Command}.
     * 
     * @param width                     the width of the canvas
     * @param height                    the height of the canvas
     * @param defaultAnimationDuration  the default duration of animations
     * @param rotateRigidlyRelatedNodesRigidly  see {@link InitializationCommand}
     */
    //@ requires width > 0 && height > 0 && defaultAnimationDuration >= -1.0;
    public InitializationCommand(double width, double height, double defaultAnimationDuration,
            boolean rotateRigidlyRelatedNodesRigidly) {
        setWidth(width);
        setHeight(height);
        setDefaultAnimationDuration(defaultAnimationDuration);
        setRotateRigidlyRelatedNodesRigidly(rotateRigidlyRelatedNodesRigidly);
    }

    // -- Queries ----------------------------------------------------------------------------
    
    /** @return the width of the canvas */
    //@ ensures \result > 0;
    /*@ pure */ public double getWidth() {
        return width;
    }
    
    /** @return the height of the canvas */
  //@ ensures \result > 0;
    /*@ pure */ public double getHeight() {
        return height;
    }

    /** @return the default animation duration
     *  @see    SetAnimationDurationCommand  */
    //@ ensures \result >= -1.0;
    /*@ pure */ public double getDefaultAnimationDuration() {
        return defaultAnimationDuration;
    }

    /** @return the rotateRigidlyRelatedNodesRigidly 
     *  @see    InitializationCommand */
    /*@ pure */ public boolean isRotateRigidlyRelatedNodesRigidly() {
        return rotateRigidlyRelatedNodesRigidly;
    }


    // -- Setters ----------------------------------------------------------------------------

    /** @param width the width of the canvas */
    //@ requires width > 0;
    //@ ensures getWidth() == width;
    private void setWidth(double width) {
        this.width = width;
    }

    /** @param height the height of the canvas */
    //@ requires height > 0;
    //@ ensures getHeight() == height;
    private void setHeight(double height) {
        this.height = height;
    }
    
    /** @param defaultAnimationDuration the default animation duration */
    //@ requires defaultAnimationDuration >= -1.0;
    //@ ensures getdefaultAnimationDuration() == defaultAnimationDuration;
    private void setDefaultAnimationDuration(double defaultAnimationDuration) {
        this.defaultAnimationDuration = defaultAnimationDuration;
    }

    /** @param rotateRigidlyRelatedNodesRigidly the rotateRigidlyRelatedNodesRigidly setting */
    //@ ensures isRotateRigidlyRelatedNodesRigidly() == rotateRigidlyRelatedNodesRigidly;
    public void setRotateRigidlyRelatedNodesRigidly(boolean rotateRigidlyRelatedNodesRigidly) {
        this.rotateRigidlyRelatedNodesRigidly = rotateRigidlyRelatedNodesRigidly;
    }

    
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public String getFormattedString(@NonNull CommunicationFormat format) {
        switch (format) {
        default: case JSON:
            return JsonOutput.toJson(new LinkedHashMap<String, Object>() {
                {
                    put("width", getWidth());
                    put("height", getHeight());
                    put("defaultAnimationDuration", getDefaultAnimationDuration());
                    put("rotateRigidlyRelatedNodesRigidly", isRotateRigidlyRelatedNodesRigidly());
                }
            });
        }
    }
}