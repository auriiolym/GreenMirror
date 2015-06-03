package greenmirror.commandlineoptionhandlers;

import greenmirror.CommandLineOptionHandler;
import greenmirror.GreenMirrorController;
import greenmirror.ServerSide;
import greenmirror.server.ServerController;

import joptsimple.OptionParser;
import joptsimple.OptionSpec;

import java.util.Arrays;
import java.util.List;

/**
 * The port <code>CommandLineOptionHandler</code> (server side).
 * 
 * @author Karim El Assal
 */
@ServerSide
public class PortCommandLineOptionHandler implements CommandLineOptionHandler {
    
    // -- Instance variables -----------------------------------------------------------------
    
    private int port;

    
    // -- Queries ----------------------------------------------------------------------------
   
    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#getDescription()
     */
    @Override
    public String getDescription() {
        return "the port the server will listen on";
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#getOptions()
     */
    @Override
    public List<String> getOptions() {
        return Arrays.asList("port", "p");
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
        return 1;
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
                    .describedAs("portnumber");
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#validate(greenmirror.GreenMirrorController, 
     *                                                                      java.lang.String[])
     */
    @Override
    public void validate(GreenMirrorController controller, String... arguments)
            throws FatalException {
        if (arguments.length != getArgumentCount()) {
            throw new FatalException("The port option has the wrong number of parameters.");
        }
        
        try {
            port = Integer.valueOf(arguments[0]);
            if (port < 0) { 
                throw new NumberFormatException();
            }
        } catch (NumberFormatException e) {
            throw new FatalException("The port number was invalid.");
        }
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#process(greenmirror.GreenMirrorController)
     */
    @Override
    public void process(GreenMirrorController controller) throws FatalException {
        // Set port.
        ((ServerController) controller).setPort(port);
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#clone()
     */
    @Override
    public CommandLineOptionHandler clone() {
        return new PortCommandLineOptionHandler();
    }

}
