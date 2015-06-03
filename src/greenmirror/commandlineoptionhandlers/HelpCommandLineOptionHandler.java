package greenmirror.commandlineoptionhandlers;

import greenmirror.ClientSide;
import greenmirror.CommandLineOptionHandler;
import greenmirror.GreenMirrorController;
import greenmirror.GreenMirrorUtils;
import greenmirror.Log;
import greenmirror.ServerSide;

import java.io.IOException;
import java.io.StringWriter;
import java.util.Arrays;
import java.util.List;

import joptsimple.OptionParser;
import joptsimple.OptionSpec;

/**
 * The help <code>CommandLineOptionHandler</code> (client and server side).
 * 
 * @author Karim El Assal
 */
@ClientSide
@ServerSide
public class HelpCommandLineOptionHandler implements CommandLineOptionHandler {
    
    // -- Instance variables -----------------------------------------------------------------
    
    // -- Queries ----------------------------------------------------------------------------
   
    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#getDescription()
     */
    @Override
    public String getDescription() {
        return "display this help message";
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#getOptions()
     */
    @Override
    public List<String> getOptions() {
        return Arrays.asList("help", "?");
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#getProcessPriority()
     */
    @Override
    public int getProcessPriority() {
        return 1;
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#getParameterCount()
     */
    @Override
    public int getArgumentCount() {
        return 0;
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

        return optionParser.acceptsAll(getOptions()).forHelp();
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#validate(greenmirror.GreenMirrorController, 
     *                                                                      java.lang.String[])
     */
    @Override
    public void validate(GreenMirrorController controller, String... parameters)
            throws FatalException {
        // Nothing to validate.
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#process(greenmirror.GreenMirrorController)
     */
    @Override
    public void process(GreenMirrorController controller) throws FatalException {
        
        // Rebuild the parser.
        final OptionParser parser = new OptionParser();
        controller.getCommandLineOptionHandlers().forEach(handler -> {
            handler.setParserSettings(parser);
        });
        GreenMirrorUtils.addCommandLineVerboseOption(parser);
        
        // Build help string.
        StringWriter stringWriter = new StringWriter();
        try {
            parser.printHelpOn(stringWriter);
        } catch (IOException e) {
            Log.add("Something went wrong with building the help message.");
        }
        Log.add(String.format(controller.getHelpMessage(), stringWriter.toString()));
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#clone()
     */
    @Override
    public CommandLineOptionHandler clone() {
        return new HelpCommandLineOptionHandler();
    }

}
