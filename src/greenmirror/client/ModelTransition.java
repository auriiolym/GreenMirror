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
     * -1.0 for unspecified duration; 0 if you don't want animations to play.
     */
    //@ private invariant duration >= -1.0;
    private double duration = -1.0;
    
    private boolean supplemental = false;
    
    
    // -- Constructors -----------------------------------------------------------------------

    /**
     * @param regex    A valid regex which compiles into a <code>Pattern</code>.
     * @param closure  {@link greenmirror.client.ModelTransition#closure}
     * @param duration {@link greenmirror.client.ModelTransition#duration}
     */
    //@ requires pattern != null && closure != null && duration >= -1.0;
    //@ ensures getPattern().equals(Pattern.compile(regex)) && getClosure() == closure;
    //@ ensures getDuration() == duration;
    public ModelTransition(String regex, Closure<Object> closure, 
                            double duration, boolean supplemental) {
        setPattern(regex);
        setClosure(closure);
        setDuration(duration);
        setSupplemental(supplemental);
    }
    
    public ModelTransition(String regex, Closure<Object> closure, 
            double duration) {
        this(regex, closure, duration, false);
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
    
    /*@ pure */ public boolean isSupplemental() {
        return supplemental;
    }
    
    
    // -- Setters ----------------------------------------------------------------------------

    /**
     * @param regex The regex which compiles to a valid <code>Pattern</code> to set.
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
    
    //@ ensures isSupplemental() == supplemental;
    public void setSupplemental(boolean supplemental) {
        this.supplemental = supplemental;
    }
    

    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * @param traceTransition A transition given by a trace.
     * @return                Whether <code>traceTransition</code> is a match for this 
     *                        <code>ModelTransition</code>.
     */
    //@ requires traceTransition != null;
    public boolean executableBy(String traceTransition) {
        return getPattern().matcher(traceTransition).matches();
    }
    
    /**
     * Executes the closure of this transition while extracting its optional arguments from 
     * <code>traceTransition</code>. If <code>traceTransition</code> doesn't match this transition's
     * <code>Pattern</code>, nothing happens and <code>null</code> is returned.
     * @param  traceTransition A transition given by a trace.
     * @return                 The return value of the <code>Closure</code>; <code>null</code> if
     *                         <code>traceTransition</code> doesn't match the <code>Pattern</code>.
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
