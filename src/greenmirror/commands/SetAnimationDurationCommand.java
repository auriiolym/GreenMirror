package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import groovy.json.JsonOutput;

import org.eclipse.jdt.annotation.NonNull;

import java.util.LinkedHashMap;

/**
 * Sets the animation duration for following animations. This command is sent to the server.
 * 
 * <table><caption>Values sent:</caption>
 * <tr><th>variable</th><th>type</th><th>description</th></tr>
 * <tr><td>duration</td><td>double</td><td>the animation duration</td></tr>
 * </table>
 * <p>
 * The current version of GreenMirror uses the following order of priority on the 
 * animation duration:
 * <ol>
 *  <li>duration set during a state-transition;</li>
 *  <li>duration set with the state-transition (see 
 *      {@link greenmirror.client.ModelTransition#setDuration(double)});</li>
 *  <li>duration set while initializing the visualizer (see 
 *      {@link greenmirror.client.modelinitializers.GreenMirrorGroovyBaseScript#initialize
                                                                 (double, double, double)}).
 *      This duration setting is stored by use of 
 *      {@link greenmirror.server.Visualizer#setDefaultAnimationDuration(double)};</li>  
 *  <li>1000ms</li>
 * </ol>
 * This means that if scenario 1 does not apply, the duration of 2 is chosen. If scenario 2 does
 * not apply, the duration of 3 is chosen. If scenario 3 does not apply, duration 4 is chosen.
 * Additionally, after each transition the duration gets reset, so scenario 1 is isolated to
 * the state-transition it applies to. In both scenarios 1 and 2, the duration setting gets
 * stored by use of {@link greenmirror.server.Visualizer#setCurrentAnimationDuration(double)}.
 * 
 * @author  Karim El Assal
 * @see     SetAnimationDurationCommandHandler
 */
public class SetAnimationDurationCommand extends Command {

    // -- Instance variables -----------------------------------------------------------------

    //@ private invariant duration >= -1.0;
    private double duration;
    

    // -- Constructors -----------------------------------------------------------------------

    /**
     * Initializes this {@link greenmirror.Command}.
     *
     * @param duration the duration of upcoming animations
     */
    //@ requires duration >= -1.0;
    //@ ensures getDuration() == duration;
    public SetAnimationDurationCommand(double duration) {
        this.duration = duration;
    }

    
    // -- Queries ----------------------------------------------------------------------------

    /** @return the duration of upcoming animations */
    //@ ensures \result >= -1.0;
    /*@ pure */ public double getDuration() {
        return duration;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public String getFormattedString(@NonNull CommunicationFormat format) {
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
