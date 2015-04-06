package greenmirror;


/**
 * The abstract <tt>CommandHandler</tt> class. It contains shared code for all 
 * <tt>CommandHandler</tt>s.
 * 
 * @author Karim El Assal
 */
public abstract class CommandHandler {

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
     * @return The textual description of the <tt>Command</tt> belonging to this handler.
     */
    //@ ensures \result != null;
    /*@ pure */ public String getCommand() {
        return this.getClass().getSimpleName().replace("CommandHandler", "");
    }
    
    
    // -- Setters ----------------------------------------------------------------------------

    /**
     * @param controllerArg  The controller to set.
     */
    //@ ensures getController() == controllerArg;
    public void setController(GreenMirrorController controllerArg) {
        controller = controllerArg;
    }

    // -- Commands ---------------------------------------------------------------------------

    /**
     * The method that actually handles the received <tt>Command</tt>. The <tt>Command</tt> is
     * passed via <tt>data</tt> in the specified <tt>format</tt>.
     * @param format The communication format in which <tt>data</tt> is.
     * @param data   The <tt>String</tt> representation of the received <tt>Command</tt>.
     */
    //@ requires format != null && data != null && getController() != null;
    public abstract void handle(CommunicationFormat format, String data);

    /**
     * Get the <tt>List</tt> of <tt>Transition</tt>s in the queue.
     * @return
     * /
    public List<javafx.animation.Transition> getTransitions() {
        // TODO - implement CommandHandler.getTransitions
        throw new UnsupportedOperationException();
    }*/

}