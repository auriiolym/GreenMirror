package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import groovy.json.JsonOutput;

import org.eclipse.jdt.annotation.NonNull;

import java.util.LinkedHashMap;

/**
 * The command that tells the visualizer to create a new sub-queue of animations, meaning all
 * upcoming animations will be played after the current sub-queue. 
 * This command is sent to the server.
 * 
 * <table><caption>Values sent:</caption>
 * <tr><th>variable</th><th>type</th><th>description</th></tr>
 * <tr><td>delay </td><td>double</td><td>the delay that is added after the previous 
 *                                        animations</td></tr>
 * </table>
 * 
 * @author  Karim El Assal
 * @see     FlushCommandHandler
 */
public class FlushCommand extends Command {

    // -- Instance variables -----------------------------------------------------------------

    //@ private invariant delay >= 0.0;
    private double delay;
    

    // -- Constructors -----------------------------------------------------------------------

    /**
     * Initializes this {@link greenmirror.Command}.
     * 
     * @param delay the delay that is added after the previous animations
     */
    //@ requires delay >= 0.0;
    //@ ensures getDelay() == delay;
    public FlushCommand(double delay) {
        this.delay = delay;
    }

    
    // -- Queries ----------------------------------------------------------------------------

    /** @return the delay that is added after the previous animations */
    //@ ensures \result >= 0;
    /*@ pure */ public double getDelay() {
        return delay;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public String getFormattedString(@NonNull CommunicationFormat format) {
        switch (format) {
        default: case JSON:
            return JsonOutput.toJson(new LinkedHashMap<String, Double>() {
                {
                    put("delay", getDelay());
                }
            });
        }
    }
}