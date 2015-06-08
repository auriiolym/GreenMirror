package greenmirror.commandlineoptionhandlers;

import greenmirror.CommandLineOptionHandler;
import greenmirror.GreenMirrorController;
import greenmirror.ServerSide;
import greenmirror.server.ServerController;

import joptsimple.OptionParser;
import joptsimple.OptionSpec;

import org.eclipse.jdt.annotation.NonNull;

import java.util.ArrayList;
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
   
    @Override @NonNull 
    public String getDescription() {
        return "the port the server will listen on";
    }

    @Override @NonNull 
    public List<String> getOptions() {
        return new ArrayList<String>(Arrays.asList("port", "p"));
    }

    @Override
    public double getProcessPriority() {
        return 5;
    }

    @Override
    public int getArgumentCount() {
        return 1;
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
                    .describedAs("portnumber");
    }

    @Override
    public void validate(@NonNull GreenMirrorController controller, String... arguments)
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

    @Override
    public void process(@NonNull GreenMirrorController controller) throws FatalException {
        // Set port.
        ((ServerController) controller).setPort(port);
    }

    @Override @NonNull 
    public CommandLineOptionHandler clone() {
        return new PortCommandLineOptionHandler();
    }

}
