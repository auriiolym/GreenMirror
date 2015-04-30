package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import groovy.json.JsonOutput;

import java.util.HashMap;

/**
 * Sets the animation duration for following animations. This command is sent to the server.
 * 
 * values sent:
 * duration : double       The animation duration.
 * 
 * @author Karim El Assal
 */
public class SetCurrentAnimationDurationCommand extends Command {

    // -- Instance variables -----------------------------------------------------------------

    //@ private invariant duration >= duration;
    private double duration;
    

    // -- Constructors -----------------------------------------------------------------------

    /**
     * Initialize the <tt>Command</tt>.
     * @param duration The duration of following animations.
     */
    //@ requires duration >= 0.0;
    //@ ensures getDuration() == duration;
    public SetCurrentAnimationDurationCommand(double duration) {
        this.duration = duration;
    }

    
    // -- Queries ----------------------------------------------------------------------------

    /**
     * @return The duration of following animations.
     */
    //@ ensures \result >= 0;
    /*@ pure */ public double getDuration() {
        return duration;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    /**
     * Prepare the <tt>Command</tt>.
     */
    public void prepare() {
        // Nothing to prepare.
    }

    /**
     * Fetch the raw data that will be sent.
     * @param format The format in which the data will be.
     */
    //@ requires format != null;
    public String getFormattedString(CommunicationFormat format) {
        switch (format) {
        default: case JSON:
            return JsonOutput.toJson(new HashMap<String, Double>() {
                {
                    put("duration", getDuration());
                }
            });
        }
    }
}
