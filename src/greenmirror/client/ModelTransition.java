package greenmirror.client;

import groovy.lang.Closure;

import org.eclipse.jdt.annotation.NonNull;

import java.util.LinkedList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * A class that stores the execution of state-transitions. These instances should be defined 
 * by the model initializers. Whenever a transition is encountered on a trace that matches the 
 * pattern of an instance of <code>ModelTransition</code>, the code from the closure is executed
 * and that should actually execute the state-transition. 
 * This class is only used on the client side.
 * 
 * @author Karim El Assal
 */
public class ModelTransition {
    
    // -- Instance variables -----------------------------------------------------------------

    /** the pattern to match transitions from a trace to */
    private Pattern pattern;

    /**
     * the closure that holds the code that will be executed when this transition is
     * encountered in a trace
     */
    private Closure<Object> closure;    
    
    /**
     * the default duration of the transition animations. (in milliseconds); 
     * -1.0 for unspecified duration; 0 if you don't want animations to play
     */
    //@ private invariant duration >= -1.0;
    private double duration = -1.0;
    
    /** whether this model transition is supplementing another one */
    private boolean supplemental = false;
    
    
    // -- Constructors -----------------------------------------------------------------------

    /**
     * Creates a new model transition.
     * 
     * @param regex    A valid regex which compiles into a <code>Pattern</code>.
     * @param closure  {@link greenmirror.client.ModelTransition#closure}
     * @param duration {@link greenmirror.client.ModelTransition#duration}
     */
    //@ requires duration >= -1.0;
    //@ ensures getPattern().equals(Pattern.compile(regex)) && getClosure() == closure;
    //@ ensures getDuration() == duration;
    public ModelTransition(@NonNull String regex, Closure<Object> closure, 
                            double duration, boolean supplemental) {
        setPattern(regex);
        //this.closure = closure;
        setClosure(closure);
        setDuration(duration);
        setSupplemental(supplemental);
    }
    
    public ModelTransition(@NonNull String regex, @NonNull Closure<Object> closure, 
            double duration) {
        this(regex, closure, duration, false);
    }
    

    
    // -- Queries ----------------------------------------------------------------------------

    /** @return the pattern */
    /*@ pure */ public Pattern getPattern() {
        return pattern;
    }

    /** @return the closure */
    /*@ pure */ public Closure<Object> getClosure() {
        return closure;
    }
    
    /** @return the base duration of the transition animations */
    //@ ensures \result >= -1.0;
    /*@ pure */ public double getDuration() {
        return duration;
    }
    
    /** whether this model transition is supplemental to other ones */
    /*@ pure */ public boolean isSupplemental() {
        return supplemental;
    }
    
    
    // -- Setters ----------------------------------------------------------------------------

    /** @param regex the regex which compiles into a valid {@link Pattern} */
    //@ ensures getPattern() == Pattern.compile(regex);
    public void setPattern(@NonNull String regex) {
        this.pattern = Pattern.compile(regex);
    }

    /** @param closure the closure to set */
    //@ ensures getClosure() == closure;
    public void setClosure(Closure<Object> closure) {
        this.closure = closure;
    }
    
    /** @param duration the base duration of the transition animations */
    //@ requires duration >= -1.0;
    //@ ensures getDuration() == duration;
    public void setDuration(double duration) {
        this.duration = duration;
    }
    
    /** @param whether this model transition is supplemental to others */
    //@ ensures isSupplemental() == supplemental;
    public void setSupplemental(boolean supplemental) {
        this.supplemental = supplemental;
    }
    

    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * @param traceTransition a transition given by a trace
     * @return                whether <code>traceTransition</code> is a match for this 
     *                        <code>ModelTransition</code>
     */
    public boolean executableBy(@NonNull String traceTransition) {
        return getPattern().matcher(traceTransition).matches();
    }
    
    /**
     * Executes the closure of this transition while extracting its optional arguments from 
     * <code>traceTransition</code>. If <code>traceTransition</code> doesn't match this transition's
     * <code>Pattern</code> or the closure is <code>null</code>, nothing happens and 
     * <code>null</code> is returned.
     * 
     * @param  traceTransition a transition given by a trace.
     * @return                 the return value of the <code>Closure</code>; <code>null</code> if
     *                         <code>traceTransition</code> doesn't match the <code>Pattern</code>
     */
    public Object execute(@NonNull String traceTransition) {
        final Matcher matcher = getPattern().matcher(traceTransition);
        if (!matcher.matches() || getClosure() == null) {
            return null;
        }

        final List<Object> arguments = new LinkedList<>();
        final Class<?>[] argumentTypes = getClosure().getParameterTypes();
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
