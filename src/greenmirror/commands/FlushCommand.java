package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import groovy.json.JsonOutput;

import java.util.HashMap;

/**
 * The command to create a new sub-queue of visualizations. This command is sent to the server.
 * 
 * Values sent:
 * delay : double       The delay that is added after the previous animations.
 */
public class FlushCommand extends Command {

    // -- Instance variables -----------------------------------------------------------------

    //@ private invariant duration >= duration;
    private double delay;
    

    // -- Constructors -----------------------------------------------------------------------

    /**
     * Initialize the <tt>Command</tt>.
     * @param delay The delay that is added after the previous animations.
     */
    //@ requires delay >= 0.0;
    //@ ensures getDelay() == delay;
    public FlushCommand(double delay) {
        this.delay = delay;
    }

    
    // -- Queries ----------------------------------------------------------------------------

    /**
     * @return The duration of following animations.
     */
    //@ ensures \result >= 0;
    /*@ pure */ public double getDelay() {
        return delay;
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
                    put("delay", getDelay());
                }
            });
        }
    }
}