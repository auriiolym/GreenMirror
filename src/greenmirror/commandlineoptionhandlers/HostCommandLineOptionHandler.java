package greenmirror.commandlineoptionhandlers;

import greenmirror.ClientSide;
import greenmirror.CommandLineOptionHandler;
import greenmirror.GreenMirrorController;
import greenmirror.client.Client;
import joptsimple.OptionParser;
import joptsimple.OptionSpec;
import org.eclipse.jdt.annotation.NonNull;

import java.io.IOException;
import java.net.InetAddress;
import java.net.SocketTimeoutException;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * The host <code>CommandLineOptionHandler</code> (client side). It checks if the host and port
 * arguments are valid and connects (via the client controller) to the server. Select port -1
 * to debug.
 * 
 * @author Karim El Assal
 */
@ClientSide
public class HostCommandLineOptionHandler implements CommandLineOptionHandler {
    
    // -- Instance variables -----------------------------------------------------------------
    
    /** the selected server host */
    private InetAddress host;
    
    /** the selected server port */
    private int port;

    
    // -- Queries ----------------------------------------------------------------------------
   
    @Override @NonNull
    public String getDescription() {
        return "connect to a server";
    }

    @Override @NonNull
    public List<String> getOptions() {
        return new ArrayList<String>(Arrays.asList("host", "h"));
    }

    @Override
    public double getProcessPriority() {
        return 2;
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
                    .describedAs("address:port")
                    .withValuesSeparatedBy(':');
    }

    @Override
    public void validate(@NonNull GreenMirrorController controller, String... parameters)
            throws FatalException {
        
        if (parameters.length != 2) {
            throw new FatalException("the host option has the wrong number of arguments");
        }
        
        try {
            host = InetAddress.getByName(parameters[0]);
            port = Integer.valueOf(parameters[1]);
            if (port < -1) { // -1 is for debug purposes. 
                throw new NumberFormatException();
            }
        } catch (UnknownHostException e) {
            throw new FatalException("the host is unknown");
        } catch (NumberFormatException e) {
            throw new FatalException("the port number was invalid");
        }
    }

    @Override
    public void process(@NonNull GreenMirrorController controller) throws FatalException {
        
        if (port == -1) {
            return;
        }
        
        // Connect.
        try {
            ((Client) controller).connect(host, port);
        } catch (SocketTimeoutException e) {
            throw new FatalException("The connection to the server timed out.");
        } catch (IOException e) {
            throw new FatalException("IO exception while connecting to the server: " 
                    + e.getMessage());
        }
    }

    @Override @NonNull
    public CommandLineOptionHandler clone() {
        return new HostCommandLineOptionHandler();
    }

}
