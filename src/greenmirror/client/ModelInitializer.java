package greenmirror.client;

import org.eclipse.jdt.annotation.NonNull;


/**
 * The interface that defines how model initializers should be structured.
 * <p>
 * The order of executing is: {@link #setParameter(String)}, {@link #prepare()} and 
 * {@link #executeInitializer()}. The complete set of available model initializers is first 
 * prepared before they are all executed.
 * 
 * @author Karim El Assal
 */
public interface ModelInitializer {
    
    // -- Exceptions -------------------------------------------------------------------------
    
    /**
     * A custom exception for use by the <code>ModelInitializer</code> implementations.
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
     * @return a unique identifier for this <code>ModelInitializer</code> used on the command line
     */
    @NonNull public String getIdentifier();
    
    /** @return a specification of the parameters used in a help message */
    @NonNull public String getParameterSpecification();
    
    /** @return the GreenMirror controller */
    public Client getController();
    
    
    // -- Setters ----------------------------------------------------------------------------
    
    /** @param controller the GreenMirror controller to set */
    public void setController(@NonNull Client controller);
    
    /** @param parameter parameter to store */
    public void setParameter(String parameter);
    
    
    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * Do some preparing, like retrieving the contents of a file.
     * 
     * @throws PreparationException if something goes wrong during the preparation
     */
    public void prepare() throws PreparationException;
    
    /**
     * Execute the model initializer. After executing, the model should be known to the 
     * application.
     */
    public void executeInitializer();
}
