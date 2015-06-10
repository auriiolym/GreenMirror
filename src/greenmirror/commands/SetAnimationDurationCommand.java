package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import groovy.json.JsonOutput;

import java.util.LinkedHashMap;

/**
 * Sets the animation duration for following animations. This command is sent to the server.
 * 
 * values sent:
 * duration : double       The animation duration.
 * 
 * @author Karim El Assal
 */
public class SetAnimationDurationCommand extends Command {

    // -- Instance variables -----------------------------------------------------------------

    //@ private invariant duration >= -1.0;
    private double duration;
    

    // -- Constructors -----------------------------------------------------------------------

    /**
     * Initialize the <code>Command</code>.
     * @param duration The duration of following animations.
     */
    //@ requires duration >= -1.0;
    //@ ensures getDuration() == duration;
    public SetAnimationDurationCommand(double duration) {
        this.duration = duration;
    }

    
    // -- Queries ----------------------------------------------------------------------------

    /**
     * @return The duration of following animations.
     */
    //@ ensures \result >= -1.0;
    /*@ pure */ public double getDuration() {
        return duration;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    /**
     * Fetch the raw data that will be sent.
     * @param format The format in which the data will be.
     */
    //@ requires format != null;
    public String getFormattedString(CommunicationFormat format) {
        switch (format) {
        default: case JSON:
            return JsonOutput.toJson(new LinkedHashMap<String, Double>() {
                {
                    put("duration", getDuration());
                }
            });
        }
    }
}
