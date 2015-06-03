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
     * A custom exception for use by the <code>TraceSelector</code> implementations.
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
     * @return a unique identifier for this <code>TraceSelector</code>
     */
    //@ ensures \result != null;
    public String getIdentifier();
    
    /**
     * @return a specification of the parameters. For example, in command line usage: 
     *         "&lt;param1&gt;". Only one parameter is allowed.
     */
    //@ ensures \result != null;
    public String getParameterSpecification();
    
    /**
     * @return the trace this selector has selected
     */
    //@ ensures \result != null;
    public List<String> getTrace();
    
    
    // -- Setters ----------------------------------------------------------------------------
    
    /**
     * @param parameter parameter to store (like an input source)
     */
    public void setParameter(String parameter);
    
    
    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * Do some preparing, like retrieving the trace from a file or other class. This method 
     * should only be called once.
     * 
     * @throws PreparationException if something goes wrong during the preparation
     */
    public void prepare() throws PreparationException;
    
}