package greenmirror.commandlineoptionhandlers;

import greenmirror.CommandLineOptionHandler;
import greenmirror.GreenMirrorController;
import greenmirror.client.Client;
import greenmirror.client.TraceSelector;
import groovy.lang.GroovyRuntimeException;

import joptsimple.OptionParser;
import joptsimple.OptionSpec;

import java.util.Arrays;
import java.util.List;

/**
 * The trace selector <tt>CommandLineOptionHandler</tt> (client side).
 * 
 * @author Karim El Assal
 */
@CommandLineOptionHandler.ClientSide
public class TraceCommandLineOptionHandler implements CommandLineOptionHandler {
    
    // -- Instance variables -----------------------------------------------------------------

    private TraceSelector traceSelector;
    

    // -- Queries ----------------------------------------------------------------------------
   
    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#getDescription()
     */
    @Override
    public String getDescription() {
        return "";
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#getOptions()
     */
    @Override
    public List<String> getOptions() {
        return Arrays.asList("trace", "t");
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#getProcessPriority()
     */
    @Override
    public int getProcessPriority() {
        return 8;
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#getParameterCount()
     */
    @Override
    public int getArgumentCount() {
        return 2;
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#allowMultiple()
     */    
    @Override
    public boolean allowMultiple() {
        return false;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#setParserSettings(joptsimple.OptionParser)
     */
    @Override
    public OptionSpec<?> setParserSettings(OptionParser optionParser) {

        return optionParser.acceptsAll(getOptions())
                    .withRequiredArg()
                    .required()
                    .describedAs("selector:parameter")
                    .withValuesSeparatedBy(':');
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#validate(greenmirror.GreenMirrorController, 
     *                                                                      java.lang.String[])
     */
    @Override
    public void validate(GreenMirrorController controller, String... parameters)
            throws FatalException {
        if (parameters.length != 2) {
            throw new FatalException("The model option has the wrong number of parameters.");
        }
        final Client client = (Client) controller;

        try {
            // Loop through all registered TraceSelectors to find the correct one.
            for (TraceSelector selector : client.getTraceSelectors()) {
                // Check if we're encountering the one requested by the user.
                if (selector.getIdentifier().equals(parameters[0])) {
                    // Remember it.
                    traceSelector = selector;
                    // Pass the parameters.
                    selector.setParameter(parameters[1]);
                    // And let it prepare.
                    selector.prepare();
                    break;
                }
            }
            if (traceSelector == null) {
                throw new IllegalArgumentException("the trace selector was not found.");
            }
        } catch (TraceSelector.PreparationException e) {
            throw new FatalException("The trace selector gave an exception: " + e.getMessage());
        } catch (IllegalArgumentException e) {
            throw new FatalException("The parameters are not valid: " + e.getMessage());
        }
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#process(greenmirror.GreenMirrorController)
     */
    @Override
    public void process(GreenMirrorController controller) throws FatalException {
        Client client = (Client) controller;

        // Check if the trace consists of valid transitions.
        List<String> invalidTraceTransitions = client.validateTrace(traceSelector);
        if (invalidTraceTransitions != null) {
            throw new FatalException("The following trace transitions could not be deemed valid: " 
                    + invalidTraceTransitions.toString());
        }
        
        // And execute the trace.
        try {
            client.executeTrace(traceSelector);
        } catch (GroovyRuntimeException e) {
            throw new FatalException("Your Groovy trace script gave an exception: ", e);
        } catch (Exception e) {
            throw new FatalException("The transition gave an exception: ", e);
        }
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#clone()
     */
    @Override
    public CommandLineOptionHandler clone() {
        return new TraceCommandLineOptionHandler();
    }

}
