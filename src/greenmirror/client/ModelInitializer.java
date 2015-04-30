package greenmirror.client;

import greenmirror.client.TraceSelector.PreparationException;

/**
 * The interface which defines how model initializers should be structured.
 * 
 * @author Karim El Assal
 */
public interface ModelInitializer {
    
    // -- Exceptions -------------------------------------------------------------------------
    
    /**
     * A custom exception for use by the <tt>ModelInitializer</tt> implementations.
     * 
     * @author Karim El Assal
     */
    public static class PreparationException extends Exception {
        public PreparationException(String msg) {
            super(msg);
        }
    }

    // -- Queries ----------------------------------------------------------------------------

    /**
     * @return A unique identifier for this <tt>ModelInitializer</tt>.
     */
    //@ ensures \result != null;
    public String getIdentifier();
    
    /**
     * @return A specification of the parameters.
     */
    //@ ensures \result != null;
    public String getParameterSpecification();
    
    /**
     * @return The GreenMirror controller.
     */
    public Client getController();
    
    
    // -- Setters ----------------------------------------------------------------------------
    
    /**
     * @param controller The GreenMirror controller to set.
     */
    public void setController(Client controller);
    
    /**
     * @param parameters Parameters to store.
     */
    public void setParameters(String... parameters);
    
    
    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * Do some preparing, like retrieving the contents of a file.
     * @throws PreparationException If something goes wrong during the preparation.
     */
    public void prepare() throws PreparationException;
    
    /**
     * Execute the model initializer. After executing, the model should be known to the 
     * application.
     */
    public void executeInitializer();
}
