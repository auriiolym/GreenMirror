package greenmirror.commandlineoptionhandlers;

import greenmirror.ClientSide;
import greenmirror.CommandLineOptionHandler;
import greenmirror.GreenMirrorController;
import greenmirror.client.Client;

import java.io.IOException;
import java.net.InetAddress;
import java.net.SocketTimeoutException;
import java.net.UnknownHostException;
import java.util.Arrays;
import java.util.List;

import joptsimple.OptionParser;
import joptsimple.OptionSpec;

/**
 * The host <code>CommandLineOptionHandler</code> (client side).
 * 
 * @author Karim El Assal
 */
@ClientSide
public class HostCommandLineOptionHandler implements CommandLineOptionHandler {
    
    // -- Instance variables -----------------------------------------------------------------
    
    private InetAddress host;
    private int port;

    
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
        return Arrays.asList("host", "h");
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#getProcessPriority()
     */
    @Override
    public int getProcessPriority() {
        return 2;
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
                    .describedAs("address:port")
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
            throw new FatalException("The host option has the wrong number of parameters.");
        }
        
        try {
            host = InetAddress.getByName(parameters[0]);
            port = Integer.valueOf(parameters[1]);
            if (port < 0) { 
                throw new NumberFormatException();
            }
        } catch (UnknownHostException e) {
            throw new FatalException("The host is unknown.");
        } catch (NumberFormatException e) {
            throw new FatalException("The port number was invalid.");
        }
    }

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#process(greenmirror.GreenMirrorController)
     */
    @Override
    public void process(GreenMirrorController controller) throws FatalException {
        
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

    /* (non-Javadoc)
     * @see greenmirror.CommandLineOptionHandler#clone()
     */
    @Override
    public CommandLineOptionHandler clone() {
        return new HostCommandLineOptionHandler();
    }

}
