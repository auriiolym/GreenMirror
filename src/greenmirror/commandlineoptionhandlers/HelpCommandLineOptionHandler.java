package greenmirror.commandlineoptionhandlers;

import greenmirror.ClientSide;
import greenmirror.CommandLineOptionHandler;
import greenmirror.GreenMirrorController;
import greenmirror.GreenMirrorUtils;
import greenmirror.Log;
import greenmirror.ServerSide;

import joptsimple.OptionParser;
import joptsimple.OptionSpec;

import org.eclipse.jdt.annotation.NonNull;

import java.io.IOException;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

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

    @Override @NonNull
    public String getDescription() {
        return "display this help message";
    }

    @Override @NonNull
    public List<String> getOptions() {
        return new ArrayList<String>(Arrays.asList("help", "?"));
    }

    @Override
    public double getProcessPriority() {
        return 1.0;
    }

    @Override
    public int getArgumentCount() {
        return 0;
    }
    
    @Override
    public boolean allowMultiple() {
        return false;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public OptionSpec<?> setParserSettings(@NonNull OptionParser optionParser) {
        return optionParser.acceptsAll(getOptions(), getDescription()).forHelp();
    }

    @Override
    public void validate(@NonNull GreenMirrorController controller, String... parameters)
            throws FatalException {
        // Nothing to validate.
    }

    @Override
    public void process(@NonNull GreenMirrorController controller) throws FatalException {
        
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

    @Override @NonNull
    public CommandLineOptionHandler clone() {
        return new HelpCommandLineOptionHandler();
    }

}
