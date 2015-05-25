package greenmirror;

import joptsimple.OptionParser;
import joptsimple.OptionSpec;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.util.Arrays;
import java.util.List;

/**
 * The interface that encapsulates all command line argument handlers. All implementing classes 
 * should have either the <tt>ClientSide</tt> or <tt>ServerSide</tt> annotation (or both).
 * 
 * @author Karim El Assal
 */
public interface CommandLineOptionHandler {
    
    // -- Annotations ------------------------------------------------------------------------

    @Retention(RetentionPolicy.RUNTIME)
    public static @interface ClientSide {}
    @Retention(RetentionPolicy.RUNTIME)
    public static @interface ServerSide {}
    
    // -- Exceptions -------------------------------------------------------------------------
    
    /**
     * An <tt>Exception</tt> thrown when validating or processing the argument gave an exception
     * that prohibits the continuation of the application.
     * 
     * @author Karim El Assal
     */
    public static class FatalException extends Exception {
        private Throwable throwable;
        
        public FatalException(String msg) {
            super(msg);
        }
        
        public FatalException(String msg, Throwable throwable) {
            super(msg);
            this.throwable = throwable;
        }
        
        public Throwable getThrowable() {
            return this.throwable;
        }
    }


    // -- Queries ----------------------------------------------------------------------------

    /**
     * @return The description of this option handler.
     */
    //@ ensures \result != null;
    /*@ pure */ public String getDescription();
    
    /**
     * @return The options of this option handler. E.g.: "help" for a help command.
     */
    //@ ensures \result != null && \result.size() > 0;
    /*@ pure */ public List<String> getOptions();
    
    /**
     * @return The processing priority of this option handler. Option handlers with a lower 
     *         priority integer are handled first.
     */
    /*@ pure */ public int getProcessPriority();
    
    /**
     * @return The amount of arguments.
     */
    //@ ensures \result >= 0;
    /*@ pure */ public int getArgumentCount();
    
    /**
     * @return Whether the option can be passed multiple times.
     */
    public boolean allowMultiple();
    
    
    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * Set the settings for the JOpt Simple parser.
     * @param optionParser The <tt>OptionParser</tt> of JOpt Simple.
     * @return             The option specification of this option handler.
     */
    //@ requires optionParser != null;
    //@ ensures \result != null;
    public OptionSpec<?> setParserSettings(OptionParser optionParser);
    
    /**
     * Validate the passed arguments.
     * @param controller            The controller.
     * @param arguments             The arguments of this option.
     * @throws FatalException       If the arguments can't be validated.
     */
    //@ requires controller != null && arguments != null && arguments.length > 0;
    public void validate(GreenMirrorController controller, String... arguments)
            throws FatalException;
    
    /**
     * Process this option.
     * @param controller      The controller.
     * @throws FatalException If something went wrong during processing.
     */
    //@ equires controller != null;
    public void process(GreenMirrorController controller) throws FatalException;
    
    /**
     * @return A new instance of this handler.
     */
    //@ ensures \result != null;
    public CommandLineOptionHandler clone();
    
    
    // -- Class Usage ------------------------------------------------------------------------
    
    /**
     * Add the verbose option to the parser.
     * @param parser The parser to add it to.
     */
    //@ requires parser != null;
    public static void addVerboseOption(OptionParser parser) {
        parser.acceptsAll(Arrays.asList("v", "verbose"), "use verbose output");
    }
}
