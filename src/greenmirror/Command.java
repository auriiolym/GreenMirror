package greenmirror;

/**
 * The abstract <tt>Command</tt> class. It contains some shared code for all
 * network <tt>Command</tt>s.
 * 
 * @author Karim El Assal
 */
public abstract class Command {

    // -- Instance variables -----------------------------------------------------------------
    
    /**
     * The controller.
     */
    private GreenMirrorController controller;

    
    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @return The controller.
     */
    /*@ pure */ public GreenMirrorController getController() {
        return controller;
    }

    /**
     * @return The textual description of this <tt>Command</tt>.
     */
    //@ ensures \result != null;
    /*@ pure */ public String getCommand() {
        return this.getClass().getSimpleName().replace("Command", "");
    }

    /**
     * Retrieve this <tt>Command</tt> as a <tt>String</tt> which will be sent to the server with
     * the specified communication <tt>format</tt>.
     * @param format The communication format.
     */
    //@ requires format != null;
    //@ ensures \result != null;
    public abstract String getFormattedString(CommunicationFormat format);
    

    // -- Setters ----------------------------------------------------------------------------

    /**
     * @param controller The controller to set.
     */
    //@ ensures getController() == controller;
    public void setController(GreenMirrorController controller) {
        this.controller = controller;
    }

    
    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * A method to prepare this <tt>Command</tt> before the formatted <tt>String</tt> is 
     * constructed and sent to the peer.
     */
    public abstract void prepare();
}