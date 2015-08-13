package greenmirror.client;

import groovy.lang.Closure;

import org.eclipse.jdt.annotation.NonNull;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * A class that stores the execution of state-transitions. These instances should be defined 
 * by the model initializers. Whenever a transition is encountered on a trace that matches the 
 * pattern of an instance of <code>ModelTransition</code>, the code from the closure is executed
 * and that should actually execute the state-transition. If the code (the <code>Closure</code>
 * returns boolean <code>false</code>, further state-transitions are cancelled. 
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
     * Creates a new model transition without any values set (yet).
     */
    public ModelTransition() {
        
    }

    /**
     * Creates a new model transition.
     * 
     * @param regex        a valid regex which compiles into a {@link Pattern}
     * @param closure      see {@link ModelTransition}
     * @param duration     see {@link greenmirror.commands.SetAnimationDurationCommand}
     * @param supplemental whether this transition is supplemental to a previous or next
     *                     one. If so, the controller won't send an 
     *                     {@link greenmirror.commands.EndTransitionCommand} after this
     *                     transition finishes
     */
    //@ requires duration >= -1.0;
    //@ ensures getPattern().equals(Pattern.compile(regex)) && getClosure() == closure;
    //@ ensures getDuration() == duration;
    public ModelTransition(@NonNull String regex, Closure<Object> closure, 
                            double duration, boolean supplemental) {
        setPattern(regex);
        setClosure(closure);
        setDuration(duration);
        setSupplemental(supplemental);
    }

    /**
     * Creates a new model transition with the <code>supplemental</code> setting set to false.
     * 
     * @param regex        a valid regex which compiles into a {@link Pattern}
     * @param closure      see {@link ModelTransition}
     * @param duration     see {@link greenmirror.commands.SetAnimationDurationCommand}
     */
    //@ requires duration >= -1.0;
    //@ ensures getPattern().equals(Pattern.compile(regex)) && getClosure() == closure;
    //@ ensures getDuration() == duration;
    public ModelTransition(@NonNull String regex, Closure<Object> closure, 
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
    
    /** @return whether this model transition is supplemental to other ones */
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
    
    /** @param supplemental whether this model transition is supplemental to others */
    //@ ensures isSupplemental() == supplemental;
    public void setSupplemental(boolean supplemental) {
        this.supplemental = supplemental;
    }
    

    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * @param traceTransition a transition given by a trace
     * @return                whether <code>traceTransition</code> is a match for this 
     *                        <code>ModelTransition</code>; <code>false</code> if 
     *                        {@link #getPattern()} returns <code>null</code>
     */
    //@ requires getPattern() != null;
    public boolean executableBy(@NonNull String traceTransition) {
        return getPattern() == null ? false : getPattern().matcher(traceTransition).matches();
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
    //@ requires getClosure() != null && getPattern() != null;
    public Object execute(@NonNull String traceTransition) {
        if (getPattern() == null) { 
            return null;
        }
        
        final Matcher matcher = getPattern().matcher(traceTransition);
        if (getClosure() == null || !matcher.matches()) {
            return null;
        }

        final List<Object> arguments = new LinkedList<>();
        final Class<?>[] argumentTypes = getClosure().getParameterTypes();
        for (int i = 0; i < matcher.groupCount() && i < argumentTypes.length; i++) { 
            // i + 1 because group 0 is the whole string.
            final String matchedArgument = matcher.group(i + 1);
            
            arguments.add(
                // Cast to integer if the user expects an integer, else keep the String type.
                argumentTypes[i] == int.class || argumentTypes[i] == Integer.class
                ? Integer.parseInt(matchedArgument) : matchedArgument
            );
        }
        
        // Remove redundant stacktrace: leave everything from the point where the exception
        // was thrown to the line in the Groovy script.
        try {
            return getClosure().call(arguments);
        } catch (Exception e) {
            final List<StackTraceElement> st = Arrays.asList(e.getStackTrace());
            for (StackTraceElement ste : e.getStackTrace()) {
                if (ste != null && ste.getFileName() != null 
                 && ste.getFileName().startsWith("Script") 
                 && ste.getFileName().endsWith(".groovy")) {
                    e.setStackTrace(st.subList(0, st.indexOf(ste) + 1)
                                    .toArray(new StackTraceElement[]{}));
                }
            }
            throw e;
        }
    }
}
