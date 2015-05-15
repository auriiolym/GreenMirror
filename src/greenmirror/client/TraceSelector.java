package greenmirror.client;

import java.util.List;

/**
 * The interface that defines how trace selectors should be structured.
 * 
 * @author Karim El Assal
 */
public interface TraceSelector {
    
    // -- Exceptions -------------------------------------------------------------------------
    
    /**
     * A custom exception for use by the <tt>TraceSelector</tt> implementations.
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
     * @return A specification of the parameters. For example, in command line usage: 
     *         "<param1>:<param2>".
     */
    //@ ensures \result != null;
    public String getParameterSpecification();
    
    /**
     * @return The trace this selector has selected.
     */
    //@ ensures \result != null;
    public List<String> getTrace();
    
    
    // -- Setters ----------------------------------------------------------------------------
    
    /**
     * @param parameters Parameters to store .
     */
    public void setParameters(String... parameters);
    
    
    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * Do some preparing, like retrieving the trace from a file or other class. This method 
     * should only be called once.
     * @throws PreparationException If something goes wrong during the preparation.
     */
    public void prepare() throws PreparationException;
    
}