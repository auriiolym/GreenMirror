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
     * <code>AddNodeCommand</tt> would let this method return <code>AddNode</code>.
     * 
     * @return the textual, one word description of this command
     */
    /*@ pure */ @NonNull public String getCommand() {
        return "" + getClass().getSimpleName().replace("Command", "");
    }

    /**
     * Returns this <code>Command</code> as a formatted string which will be sent to the server in
     * the specified format.
     * 
     * @param format The communication format.
     * @see          CommunicationFormat
     */
    @NonNull public abstract String getFormattedString(@NonNull CommunicationFormat format);
    

    // -- Setters ----------------------------------------------------------------------------

    /**
     * Stores the GreenMirror controller.
     * 
     * @param controller
     */
    //@ ensures getController() == controller;
    public void setController(@NonNull GreenMirrorController controller) {
        this.controller = controller;
    }

    
    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * A method to prepare this <code>Command</code> before the formatted string is 
     * constructed and retrieved.
     */
    public abstract void prepare();
}