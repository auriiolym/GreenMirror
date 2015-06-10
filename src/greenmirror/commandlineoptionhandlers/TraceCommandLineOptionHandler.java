package greenmirror.commandlineoptionhandlers;

import greenmirror.ClientSide;
import greenmirror.CommandLineOptionHandler;
import greenmirror.GreenMirrorController;
import greenmirror.client.Client;
import greenmirror.client.TraceSelector;
import groovy.lang.GroovyRuntimeException;

import joptsimple.OptionParser;
import joptsimple.OptionSpec;

import org.eclipse.jdt.annotation.NonNull;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * The trace selector <code>CommandLineOptionHandler</code> (client side).
 * 
 * @author Karim El Assal
 */
@ClientSide
public class TraceCommandLineOptionHandler implements CommandLineOptionHandler {
    
    // -- Instance variables -----------------------------------------------------------------

    private TraceSelector traceSelector;
    

    // -- Queries ----------------------------------------------------------------------------
   
    @Override @NonNull
    public String getDescription() {
        return "the selector that will select the trace of the model";
    }

    @Override @NonNull
    public List<String> getOptions() {
        return new ArrayList<String>(Arrays.asList("trace", "t"));
    }

    @Override
    public double getProcessPriority() {
        return 8;
    }

    @Override
    public int getArgumentCount() {
        return 2;
    }

    @Override
    public boolean allowMultiple() {
        return false;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public OptionSpec<?> setParserSettings(@NonNull OptionParser optionParser) {

        return optionParser.acceptsAll(getOptions(), getDescription())
                    .withRequiredArg()
                    .required()
                    .describedAs("selector:parameter")
                    .withValuesSeparatedBy(':');
    }

    @Override
    public void validate(@NonNull GreenMirrorController controller, String... parameters)
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
            throw new FatalException("the trace selector gave an exception: " + e.getMessage());
        } catch (IllegalArgumentException e) {
            throw new FatalException("the parameters are not valid: " + e.getMessage());
        }
    }

    @Override
    public void process(@NonNull GreenMirrorController controller) throws FatalException {
        final Client client = (Client) controller;
        
        final TraceSelector traceSelector = this.traceSelector;
        if (traceSelector == null) { // @NonNull formality
            throw new FatalException("the trace selector is null");
        }

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

    @Override @NonNull 
    public CommandLineOptionHandler clone() {
        return new TraceCommandLineOptionHandler();
    }

}
