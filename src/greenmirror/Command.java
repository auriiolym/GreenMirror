package greenmirror;

import org.eclipse.jdt.annotation.NonNull;

/**
 * All commands that are sent over the network are wrapped in subclasses of this abstract class. 
 * The order of using a subclass is as follows:
 * <ol>
 *  <li>instantiate (with the appropriate parameters, according to the specifications);</li>
 *  <li>set the controller;</li>
 *  <li>execute the <code>prepare</code> method;</li>
 *  <li>get the formatted string using <code>getFormattedString(CommunicationFormat)</code>;
 *  <li>send the formatted string over the network with your own implementation;</li>
 * </ol>
 * 
 * @author Karim El Assal
 */
public abstract class Command {

    // -- Instance variables -----------------------------------------------------------------
    
    /** The GreenMirror controller. */
    private GreenMirrorController controller;

    
    // -- Queries ----------------------------------------------------------------------------
    
    /** @return the GreenMirror controller */
    /*@ pure spec_public */ protected GreenMirrorController getController() {
        return controller;
    }

    /**
     * Returns a one word description of this command. For example, an instance of
     * {@link greenmirror.commands.AddNodeCommand} would let this method return 
     * "<code>AddNode</code>".
     * 
     * @return the textual, one word description of this command
     */
    /*@ pure */ @NonNull public String getCommand() {
        final String str = getClass().getSimpleName().replace("Command", "");
        return str == null ? "" : str;
    }

    /**
     * Returns this {@link Command} as a formatted string in the specified format, which 
     * will be sent to the server.
     * 
     * @param format the communication format
     * @return       the formatted string
     * @see          CommunicationFormat
     */
    public abstract String getFormattedString(@NonNull CommunicationFormat format);
    

    // -- Setters ----------------------------------------------------------------------------

    /**
     * Stores the GreenMirror controller.
     * 
     * @param controller the controller
     */
    //@ ensures getController() == controller;
    public void setController(@NonNull GreenMirrorController controller) {
        this.controller = controller;
    }

    
    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * A method to prepare this <code>Command</code> before the formatted string is 
     * constructed and retrieved. Does nothing by default, but subclasses might want to do 
     * something.
     */
    public void prepare() {}
}