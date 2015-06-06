package greenmirror;

import joptsimple.OptionParser;
import joptsimple.OptionSpec;
import org.eclipse.jdt.annotation.NonNull;

import java.util.List;

/**
 * The interface that encapsulates all command line argument handlers.
 * 
 * All implementing classes should have at least one of the 
 * {@link greenmirror.ClientSide ClientSide} and {@link greenmirror.ServerSide ServerSide} 
 * annotations to indicate on which part of the application they are used.
 * 
 * Command line options are processed by 
 * <a href="https://pholser.github.io/jopt-simple/">JOpt Simple</a> and thus the syntax tries to
 * honor the syntaxes of POSIX getopt() and GNU getopt_long().
 * 
 * A note on <b>terminology</b>: all different strings passed on the command line are called the
 * <b>options</b>. For example:
 *      <code>greenmirror.client.Client --option1 --option2</code>
 * All parameters belonging to options are called <b>arguments</b>. For example:
 *      <code>greenmirror.client.Client --option1=argument1 -o argument2 
 * 
 * @author Karim El Assal
 * @see <a href="https://pholser.github.io/jopt-simple/">JOpt Simple</a>
 */
public interface CommandLineOptionHandler extends Cloneable {
    
    // -- Exceptions -------------------------------------------------------------------------
    
    /**
     * An <code>Exception</code> thrown when validating or processing the argument gave an exception
     * that prohibits the continuation of the application.
     * 
     * @author Karim El Assal
     */
    public static class FatalException extends Exception {
        
        /** the <code>Throwable</code> that is relevant to this <code>FatalException</code> */
        private Throwable throwable;
        
        /**
         * Creates a new FatalException with a message.
         * 
         * @param msg the message that can be retrieved by using <code>getMessage()</code>
         */
        //@ ensures getMessage() == msg;
        public FatalException(String msg) {
            super(msg);
        }
        
        /**
         * Creates a new <code>FatalException</code> with a message and a <code>Throwable</code>
         * that is relevant to this <code>FatalException</code>.
         * 
         * @param msg       the message that can be retrieved by using <code>getMessage()</code>
         * @param throwable a relevant <code>Throwable</code>
         */
        //@ ensures getMessage() == msg && getThrowable() == throwable;
        public FatalException(String msg, Throwable throwable) {
            super(msg);
            this.throwable = throwable;
        }
        
        /**
         * @return the relevant <code>Throwable</code> that was set during creation
         */
        /*@ pure */ public Throwable getThrowable() {
            return this.throwable;
        }
    }


    // -- Queries ----------------------------------------------------------------------------

    /**
     * @return the description of this option
     */
    /*@ pure */ @NonNull public String getDescription();
    
    /**
     * @return the options of this option handler. For example: "help" for a help command
     */
    //@ ensures \result.size() > 0;
    /*@ pure */ @NonNull public List<String> getOptions();
    
    /**
     * Returns the processing priority of this option handler. Option handlers with a lower 
     * priority integer are handled first. There are no limits to the integer, it's just that
     * the option handlers are sorted according to their processing priority.
     * 
     * @return the processing priority
     */
    /*@ pure */ public int getProcessPriority();
    
    /**
     * Returns the amount of arguments this option handler accepts. This becomes relevant
     * when {@link #allowMultiple()} returns true.
     * 
     * @return the amount of arguments
     */
    //@ ensures \result >= 0;
    /*@ pure */ public int getArgumentCount();
    
    /**
     * @return whether the option can be passed multiple times
     */
    public boolean allowMultiple();
    
    
    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * Sets the settings for the JOpt Simple parser. This sets settings like which options are
     * part of this option handler (according to <code>getOptions()</code>), whether arguments
     * are required and how they are described in the help message.
     * 
     * @param optionParser the <code>OptionParser</code> of JOpt Simple
     * @return             the option specification of this option handler
     * @see <a href="https://pholser.github.io/jopt-simple/apidocs/joptsimple/OptionParser.html">
     *      JOpt Simple: OptionParser</a>
     */
    @NonNull public OptionSpec<?> setParserSettings(@NonNull OptionParser optionParser);
    
    /**
     * Validates the passed arguments. It throws a <code>FatalException</code> if the arguments
     * couldn't be validated. It might need the GreenMirror controller to validate the arguments.
     * 
     * @param controller      the GreenMirror controller
     * @param arguments       the arguments of this option
     * @throws FatalException if the arguments can't be validated
     */
    //@ requires arguments.length > 0;
    public void validate(@NonNull GreenMirrorController controller, 
                         @NonNull String... arguments) throws FatalException;
    
    /**
     * Process this option.
     * 
     * @param controller      the GreenMirror controller
     * @throws FatalException if something went wrong during processing
     */
    public void process(@NonNull GreenMirrorController controller) throws FatalException;
    
    /**
     * @return a new instance of this option handler
     */
    @NonNull public CommandLineOptionHandler clone();
}
