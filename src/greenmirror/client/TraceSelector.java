package greenmirror.client;

import org.eclipse.jdt.annotation.NonNull;

import java.util.List;

/**
 * The interface that defines how trace selectors should be structured.
 * <p>
 * Traces should be selected and retrieved in {@link #prepare()}, not in {@link #getTrace()}. 
 * <code>getTrace()</code> is only meant to be the simple getter.
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

    /** @return a unique identifier for this <code>TraceSelector</code> */
    @NonNull public String getIdentifier();
    
    /**
     * @return a specification of the parameters. For example, in command line usage: 
     *         "&lt;param1&gt;". Only one parameter is allowed
     */
    @NonNull public String getParameterSpecification();
    
    /** @return the trace this selector has selected */
    @NonNull public List<String> getTrace();
    
    
    // -- Setters ----------------------------------------------------------------------------
    
    /** @param parameter parameter to store (like an input source) */
    public void setParameter(String parameter);
    
    
    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * Do some preparing, like retrieving the trace from a file or other class. This method 
     * should only be called once. This method might be renamed in the future to something
     * like <code>selectTrace()</code> or <code>retrieveTrace()</code>.
     * 
     * @throws PreparationException if something goes wrong during the preparation
     */
    public void prepare() throws PreparationException;
    
}