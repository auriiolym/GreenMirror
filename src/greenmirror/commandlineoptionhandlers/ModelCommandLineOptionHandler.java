package greenmirror.commandlineoptionhandlers;

import greenmirror.ClientSide;
import greenmirror.CommandLineOptionHandler;
import greenmirror.GreenMirrorController;
import greenmirror.client.Client;
import greenmirror.client.ModelInitializer;
import greenmirror.commands.EndTransitionCommand;
import groovy.lang.GroovyRuntimeException;
import joptsimple.OptionParser;
import joptsimple.OptionSpec;
import org.eclipse.jdt.annotation.NonNull;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

/**
 * The model <code>CommandLineOptionHandler</code> (client side). It validates the model 
 * initializers and their parameters, lets them prepare and ultimately executes them. When
 * they're all done, a {@link greenmirror.commands.EndTransitionCommand} is sent to the server.
 * 
 * @author Karim El Assal
 */
@ClientSide
public class ModelCommandLineOptionHandler implements CommandLineOptionHandler {
    
    // -- Instance variables -----------------------------------------------------------------

    /** all selected initializers */
    @NonNull private final List<ModelInitializer> initializers = new LinkedList<>();
    

    // -- Queries ----------------------------------------------------------------------------
   
    @Override @NonNull
    public String getDescription() {
        return "select an initializer that initializes your model. Multiple are possible.";
    }

    @Override @NonNull
    public List<String> getOptions() {
        return new ArrayList<String>(Arrays.asList("model", "m"));
    }

    @Override
    public double getProcessPriority() {
        return 5;
    }

    @Override
    public int getArgumentCount() {
        return 2;
    }

    @Override
    public boolean allowMultiple() {
        return true;
    }
    
    /** @return the selected initializers */
    @NonNull private List<ModelInitializer> getInitializers() {
        return this.initializers;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public OptionSpec<?> setParserSettings(@NonNull OptionParser optionParser) {

        return optionParser.acceptsAll(getOptions(), getDescription())
                    .withRequiredArg()
                    .required()
                    .describedAs("initializer:parameter")
                    .withValuesSeparatedBy(':');
    }

    @Override
    public void validate(@NonNull GreenMirrorController controller, String... parameters)
            throws FatalException {
        
        if (parameters.length != 2) {
            throw new FatalException("the model option has the wrong number of parameters");
        }
        final Client client = (Client) controller;
        
        try {
            // Loop through all registered ModelInitializers.
            for (ModelInitializer initializer : client.getModelInitializers()) {
                // Check if we're encountering one requested by the user.
                if (initializer.getIdentifier().equals(parameters[0])) {
                    // Remember it.
                    getInitializers().add(initializer);
                    // Pass the parameters.
                    initializer.setParameter(parameters[1]);
                    // And let it prepare.
                    initializer.prepare();
                }
            }
            if (getInitializers().isEmpty()) {
                throw new IllegalArgumentException("the model initializer was not found.");
            }
        } catch (ModelInitializer.PreparationException e) {
            throw new FatalException("The model initializer gave an exception: " + e.getMessage());
        } catch (GroovyRuntimeException e) {
            throw new FatalException("Your Groovy script gave an exception: ", e);
        } catch (IllegalArgumentException e) {
            throw new FatalException("The parameters are not valid: " + e.getMessage());
        }
    }

    
    @Override
    public void process(@NonNull GreenMirrorController controller) throws FatalException {
        Client client = (Client) controller;

        // Initialize the model.
        try {
            client.initializeModel(getInitializers());
            
            /* The initialization of the model might be animated, so we execute the initial 
             * transition without delay. */
            client.send(new EndTransitionCommand());
            
        } catch (GroovyRuntimeException e) {
            throw new FatalException("Your Groovy initialization script gave an exception: ", e);
        } catch (Exception e) {
            throw new FatalException("The model initialization gave an exception: ", e);
        }
    }

    @Override @NonNull
    public CommandLineOptionHandler clone() {
        return new ModelCommandLineOptionHandler();
    }

}
