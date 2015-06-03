package greenmirror.client;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

/**
 * The <code>TraceSelector</code> that selects its trace from a file. In the file, transitions
 * should be separated by a newline.
 * 
 * @author Karim El Assal
 */
public class FileTraceSelector implements TraceSelector {

    // -- Constants --------------------------------------------------------------------------

    /**
     * The unique identifier of this <code>TraceSelector</code>.
     */
    private static final String UID = "file";
    
    /**
     * The parameter description.
     */
    private static final String PARAMS = "<filename>";
    
    // -- Instance variables -----------------------------------------------------------------
    
    /**
     * The retrieved trace.
     */
    //@ private invariant trace != null;
    private List<String> trace = new LinkedList<String>();
    
    /**
     * The reader that reads from the file.
     */
    private FileReader filereader;

    
    // -- Queries ----------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see greenmirror.client.TraceSelector#getIdentifier()
     */
    @Override
    //@ ensures \result != null;
    /*@ pure */ public String getIdentifier() {
        return UID;
    }

    /* (non-Javadoc)
     * @see greenmirror.client.TraceSelector#getParameterSpecification()
     */
    @Override
    //@ ensures \result != null;
    /*@ pure */ public String getParameterSpecification() {
        return PARAMS;
    }

    /* (non-Javadoc)
     * @see greenmirror.client.TraceSelector#getTrace()
     */
    @Override
    //@ ensures \result != null;
    /*@ pure */ public List<String> getTrace() {
        return trace;
    }

    
    // -- Setters ----------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see greenmirror.client.TraceSelector#setParameter(java.lang.String)
     */
    @Override
    public void setParameter(String parameter) throws IllegalArgumentException {
        
        // Check if the file can be found.
        try {
            filereader = new FileReader(parameter);
        } catch (FileNotFoundException e) {
            throw new IllegalArgumentException("the file trace selector could not find the "
                    + "file \"" + parameter + "\".");
        }
    }

    
    // -- Commands ---------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see greenmirror.client.TraceSelector#prepare()
     */
    @Override
    public void prepare() throws TraceSelector.PreparationException {
        try (BufferedReader reader = new BufferedReader(filereader)) {
            String line = reader.readLine();

            while (line != null) {
                getTrace().add(line.trim());
                line = reader.readLine();
            }
        } catch (IOException e) {
            throw new TraceSelector.PreparationException("an IO error occured while handling "
                    + "the file.");
        }
    }

}