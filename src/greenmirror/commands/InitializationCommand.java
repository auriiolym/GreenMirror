package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import groovy.json.JsonOutput;

import java.util.LinkedHashMap;

/**
 * The command to initialize the visualizer. This command is sent to the server.
 * 
 * Values sent:
 * width : int          The width of the window.
 * height : int         The height of the window.
 * defaultTransitionDuration : String
 *                      The default time transitions will take. This value is optional and 
 *                      defaults to the sum of the included "sub-"transitions. Set it to UNKNOWN
 *                      if it shouldn't be set.
 * rotateRigidlyRelatedNodesRigidly : boolean
 */
public class InitializationCommand extends Command {
    
    
    // -- Instance variables -----------------------------------------------------------------

    //@ private invariant width > 0;
    private double width;
    //@ private invariant height > 0;
    private double height;
    //@ private invariant defaultTransitionDuration >= -1.0;
    private double defaultTransitionDuration;
    private boolean rotateRigidlyRelatedNodesRigidly;

    // -- Constructors -----------------------------------------------------------------------

    /**
     * 
     * @param width                     Width of the canvas.
     * @param height                    Height of the canvas.
     * @param defaultTransitionDuration The default duration of transitions.
     * @param rotateRigidlyRelatedNodesRigidly
     *                 {@see greenmirror.server.Visualizer#getRotateRigidlyRelatedNodesRigidly()}
     */
    //@ requires width > 0 && height > 0 && defaultTransitionDuration >= -1.0;
    public InitializationCommand(double width, double height, double defaultTransitionDuration,
            boolean rotateRigidlyRelatedNodesRigidly) {
        setWidth(width);
        setHeight(height);
        setDefaultTransitionDuration(defaultTransitionDuration);
        setRotateRigidlyRelatedNodesRigidly(rotateRigidlyRelatedNodesRigidly);
    }

    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @return The width of the canvas.
     */
    //@ ensures \result > 0;
    /*@ pure */ public double getWidth() {
        return width;
    }
    
    /**
     * @return The height.
     */
  //@ ensures \result > 0;
    /*@ pure */ public double getHeight() {
        return height;
    }

    /**
     * @return The default transition duration.
     */
    //@ ensures \result >= -1.0;
    /*@ pure */ public double getDefaultTransitionDuration() {
        return defaultTransitionDuration;
    }

    /**
     * @return The rotateRigidlyRelatedNodesRigidly.
     */
    /*@ pure */ public boolean isRotateRigidlyRelatedNodesRigidly() {
        return rotateRigidlyRelatedNodesRigidly;
    }


    // -- Setters ----------------------------------------------------------------------------

    /**
     * @param width The width of the canvas.
     */
    //@ requires width > 0;
    //@ ensures getWidth() == width;
    private void setWidth(double width) {
        this.width = width;
    }

    /**
     * @param height The height of the canvas.
     */
    //@ requires height > 0;
    //@ ensures getHeight() == height;
    private void setHeight(double height) {
        this.height = height;
    }
    
    /**
     * @param defaultTransitionDuration The default transition duration.
     */
    //@ requires defaultTransitionDuration >= -1.0;
    //@ ensures getDefaultTransitionDuration() == defaultTransitionDuration;
    private void setDefaultTransitionDuration(double defaultTransitionDuration) {
        this.defaultTransitionDuration = defaultTransitionDuration;
    }

    /**
     * @param rotateRigidlyRelatedNodesRigidly The rotateRigidlyRelatedNodesRigidly to set.
     */
    //@ ensures isRotateRigidlyRelatedNodesRigidly() == rotateRigidlyRelatedNodesRigidly;
    public void setRotateRigidlyRelatedNodesRigidly(boolean rotateRigidlyRelatedNodesRigidly) {
        this.rotateRigidlyRelatedNodesRigidly = rotateRigidlyRelatedNodesRigidly;
    }

    
    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * Nothing to prepare.
     */
    public void prepare() {
        
    }

    /**
     * @param format
     * @return The formatted <code>String</code>.
     */
    //@ requires format != null;
    //@ ensures \result != null;
    public String getFormattedString(CommunicationFormat format) {
        switch (format) {
        default: case JSON:
            return JsonOutput.toJson(new LinkedHashMap<String, Object>() {
                {
                    put("width", getWidth());
                    put("height", getHeight());
                    put("defaultTransitionDuration", getDefaultTransitionDuration());
                    put("rotateRigidlyRelatedNodesRigidly", isRotateRigidlyRelatedNodesRigidly());
                }
            });
        }
    }
}