package greenmirror.client.traceselectors;

import greenmirror.client.TraceSelector;

import org.eclipse.jdt.annotation.NonNull;

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

    /** the unique identifier of this <code>TraceSelector</code> */
    @NonNull private static final String UID = "file";
    
    /** the parameter description */
    @NonNull private static final String PARAMS = "<filename>";
    
    
    // -- Instance variables -----------------------------------------------------------------
    
    /** the retrieved trace */
    @NonNull private List<String> trace = new LinkedList<String>();
    
    /** the reader that reads from the file */
    private FileReader filereader;

    
    // -- Queries ----------------------------------------------------------------------------

    @Override @NonNull
    /*@ pure */ public String getIdentifier() {
        return UID;
    }

    @Override @NonNull
    /*@ pure */ public String getParameterSpecification() {
        return PARAMS;
    }

    @Override @NonNull
    /*@ pure */ public List<String> getTrace() {
        return trace;
    }

    
    // -- Setters ----------------------------------------------------------------------------

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

    @Override
    public void prepare() throws TraceSelector.PreparationException {
        try (BufferedReader reader = new BufferedReader(filereader)) {
            String line = reader.readLine();

            while (line != null) {
                if (!line.trim().equals("")) {
                    getTrace().add(line.trim());
                }
                line = reader.readLine();
            }
        } catch (IOException e) {
            throw new TraceSelector.PreparationException("an IO error occured while handling "
                    + "the file.");
        }
    }

}