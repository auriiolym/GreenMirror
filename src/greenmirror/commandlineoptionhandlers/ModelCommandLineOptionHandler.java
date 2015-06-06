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

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

/**
 * The model <code>CommandLineOptionHandler</code> (client side).
 * 
 * @author Karim El Assal
 */
@ClientSide
public class ModelCommandLineOptionHandler implements CommandLineOptionHandler {
    
    // -- Instance variables -----------------------------------------------------------------

    private List<ModelInitializer> initializers = new LinkedList<>();
    

    // -- Queries ----------------------------------------------------------------------------
   
    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#getDescription()
     */
    @Override
    public String getDescription() {
        return "select a initializer that initializes your model. Multiple are possible.";
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#getOptions()
     */
    @Override
    public List<String> getOptions() {
        return Arrays.asList("model", "m");
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#getProcessPriority()
     */
    @Override
    public int getProcessPriority() {
        return 5;
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
        return true;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#setParserSettings(joptsimple.OptionParser)
     */
    @Override
    public OptionSpec<?> setParserSettings(OptionParser optionParser) {

        return optionParser.acceptsAll(getOptions(), getDescription())
                    .withRequiredArg()
                    .required()
                    .describedAs("initializer:parameter")
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
            // Loop through all registered ModelInitializers.
            for (ModelInitializer initializer : client.getModelInitializers()) {
                // Check if we're encountering one requested by the user.
                if (initializer.getIdentifier().equals(parameters[0])) {
                    // Remember it.
                    initializers.add(initializer);
                    // Pass the parameters.
                    initializer.setParameter(parameters[1]);
                    // And let it prepare.
                    initializer.prepare();
                }
            }
            if (initializers.isEmpty()) {
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

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#process(greenmirror.GreenMirrorController)
     */
    @Override
    public void process(GreenMirrorController controller) throws FatalException {
        Client client = (Client) controller;

        // Initialize the model.
        try {
            client.initializeModel(initializers);
            
            /* The initialization of the model might be animated, so we execute the initial 
             * transition without delay. */
            client.send(new EndTransitionCommand());
            
        } catch (GroovyRuntimeException e) {
            throw new FatalException("Your Groovy initialization script gave an exception: ", e);
        } catch (Exception e) {
            throw new FatalException("The model initialization gave an exception: ", e);
        }
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#clone()
     */
    @Override
    public CommandLineOptionHandler clone() {
        return new ModelCommandLineOptionHandler();
    }

}
