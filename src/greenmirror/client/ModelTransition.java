package greenmirror.client;

import groovy.lang.Closure;

import java.util.LinkedList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * A type specific for the transitions that are available on the clientside.
 * 
 * @author Karim El Assal
 */
public class ModelTransition {
    
    // -- Instance variables -----------------------------------------------------------------

    /**
     * The pattern to match transitions from a trace to.
     */
    //@ private invariant pattern != null;
    private Pattern pattern;

    /**
     * The closure which holds the code that will be executed when this transition is
     * encountered in a trace.
     */
    //@ private invariant closure != null;
    private Closure<Object> closure;    
    
    /**
     * The base duration of the transition animations. (in milliseconds); 
     * -1.0 for unspecified duration.
     */
    //@ private invariant duration >= -1.0;
    private double duration = -1.0;
    
    /**
     * The delay at the start of the transition.
     */
    //@ private invariant delay >= 0;
    private double delay = 0;
    
    
    // -- Constructors -----------------------------------------------------------------------
    
    /**
     * @param pattern  {@link greenmirror.client.ModelTransition#pattern}
     * @param closure  {@link greenmirror.client.ModelTransition#closure}
     * @param duration {@link greenmirror.client.ModelTransition#duration}
     * @param delay    {@link greenmirror.client.ModelTransition#delay}
     */
    //@ requires pattern != null && closure != null && duration >= -1.0;
    //@ ensures getPattern() == pattern && getClosure() == closure;
    //@ ensures getDuration() == duration && getDlay() == delay;
    public ModelTransition(Pattern pattern, Closure<Object> closure,
                            double duration, double delay) {
        setPattern(pattern);
        setClosure(closure);
        setDuration(duration);
        setDelay(delay);
    }

    /**
     * @param regex    A valid regex which compiles into a <tt>Pattern</tt>.
     * @param closure  {@link greenmirror.client.ModelTransition#closure}
     * @param duration {@link greenmirror.client.ModelTransition#duration}
     * @param delay    {@link greenmirror.client.ModelTransition#delay}
     */
    //@ requires pattern != null && closure != null && duration >= -1.0;
    //@ ensures getPattern().equals(Pattern.compile(regex)) && getClosure() == closure
    //@ ensures getDuration() == duration && getDlay() == delay;
    public ModelTransition(String regex, Closure<Object> closure, 
                            double duration, double delay) {
        setPattern(regex);
        setClosure(closure);
        setDuration(duration);
        setDelay(delay);
    }

    
    // -- Queries ----------------------------------------------------------------------------

    /**
     * @return The pattern.
     */
    //@ ensures \result != null;
    /*@ pure */ public Pattern getPattern() {
        return pattern;
    }

    /**
     * @return The closure.
     */
    //@ ensures \result != null;
    /*@ pure */ public Closure<Object> getClosure() {
        return closure;
    }
    
    /**
     * @return The base duration of the transition animations.
     */
    //@ ensures \result >= -1.0;
    /*@ pure */ public double getDuration() {
        return duration;
    }
    
    /**
     * @return The delay of the transition.
     */
    //@ ensures \result >= 0;
    /*@ pure */ public double getDelay() {
        return delay;
    }
    
    
    // -- Setters ----------------------------------------------------------------------------

    /**
     * @param pattern The pattern to set.
     */
    //@ requires pattern != null;
    //@ ensures getPattern() == pattern;
    public void setPattern(Pattern pattern) {
        this.pattern = pattern;
    }

    /**
     * @param regex The regex which compiles to a valid <tt>Pattern</tt> to set.
     */
    //@ requires pattern != null;
    //@ ensures getPattern() == Pattern.compile(regex);
    public void setPattern(String regex) {
        this.pattern = Pattern.compile(regex);
    }

    /**
     * @param closure The closure to set.
     */
    //@ requires closure != null;
    //@ ensures getClosure() == closure;
    public void setClosure(Closure<Object> closure) {
        this.closure = closure;
    }
    
    /**
     * @param duration The duration of the transition.
     */
    //@ requires duration >= -1.0;
    //@ ensures getDuration() == duration;
    public void setDuration(double duration) {
        this.duration = duration;
    }
    
    /**
     * @param delay The duration of the transition.
     */
    //@ requires delay >= 0;
    //@ ensures getDelay() == delya;
    public void setDelay(double delay) {
        this.delay = delay;
    }
    

    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * @param  traceTransition A transition given by a trace.
     * @return Whether <tt>traceTransition</tt> is a match for this <tt>ModelTransition</tt>.
     */
    //@ requires traceTransition != null;
    public boolean executableBy(String traceTransition) {
        return getPattern().matcher(traceTransition).matches();
    }
    
    /**
     * Executes the closure of this transition while extracting its optional arguments from 
     * <tt>traceTransition</tt>. If <tt>traceTransition</tt> doesn't match this transition's
     * <tt>Pattern</tt>, nothing happens and <tt>null</tt> is returned.
     * @param  traceTransition A transition given by a trace.
     * @return                 The return value of the <tt>Closure</tt>; <tt>null</tt> if
     *                         <tt>traceTransition</tt> doesn't match the <tt>Pattern</tt>.
     */
    //@ requires traceTransition != null;
    public Object execute(String traceTransition) {
        Matcher matcher = getPattern().matcher(traceTransition);
        if (!matcher.matches()) {
            return null;
        }

        List<Object> arguments = new LinkedList<>();
        Class<?>[] argumentTypes = getClosure().getParameterTypes();
        for (int i = 0; i < matcher.groupCount(); i++) {
            // i + 1 because group 0 is the whole string.
            final String matchedArgument = matcher.group(i + 1);
            // Cast to integer if the user expects an integer, else keep the String type.
            arguments.add(
                    argumentTypes[i] == int.class || argumentTypes[i] == Integer.class
                    ? Integer.parseInt(matchedArgument) : matchedArgument
            );
        }
        return getClosure().call(arguments);
    }
}
