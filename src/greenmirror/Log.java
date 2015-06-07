package greenmirror;

import org.eclipse.jdt.annotation.NonNull;

import java.io.PrintStream;
import java.text.SimpleDateFormat;
import java.util.Calendar;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

/**
 * A simple singleton class handling the log.
 * <p>
 * The most simple usage is <code>Log.add("message");</code>, which will use the default
 * <code>System.out</code> as output.
 * 
 * @author Karim El Assal
 */
public class Log {
    
    // -- Constants --------------------------------------------------------------------------
    
    /**
     * The default output stream. It overrides the <code>print</code> method to add a timestamp
     * before any string.
     */
    public static final PrintStream DEFAULT = new PrintStream(System.out) {
        
        @Override
        public void print(String str) {
            super.print("[" + getTimestamp() + "] " + str);
        }
    };
    
    
    // -- Class variables --------------------------------------------------------------------
    
    /** all entries of the log */
    @NonNull private static final List<String> entries = new LinkedList<String>();
    
    /** the selected log output streams */
    @NonNull private static final Set<PrintStream> outputs = new TreeSet<PrintStream>();
    
    /** whether to log verbose data */
    private static boolean verbose = false;
    

    // -- Queries ----------------------------------------------------------------------------
    
    /** @return a copy of the log entries */
    /*@ pure */ @NonNull public static List<String> getEntries() {
        return new LinkedList<String>(entries);
    }
    
    /** @return the current date and time in YYYY-MM-dd HH:mm:ss.SSS format */
    /*@ pure */ @NonNull public static String getTimestamp() {
        final String str = new SimpleDateFormat("YYYY-MM-dd HH:mm:ss.SSS")
                                .format(Calendar.getInstance().getTime());
        return str == null ? "" : str;
    }
    
    /** @return whether to output verbose data */
    /*@ pure */ public static boolean isVerbose() {
        return verbose;
    }
    
    // -- Setters ----------------------------------------------------------------------------

    /**
     * @param verbose set whether to be verbose
     */
    //@ ensures isVerbose() == verbose;
    public static void setVerbose(boolean verbose) {
        Log.verbose = verbose;
    }
    
    /**
     * Adds <code>output</code> to the list of outputs.
     * 
     * @param output the output stream
     */
    public static void addOutput(@NonNull PrintStream output) {
        outputs.add(output);
    }
    
    
    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * Removes the selected output and clean up if necessary.
     * 
     * @param output the output
     */
    public static void removeOutput(PrintStream output) {
        if (outputs.contains(output)) {
            output.close();
        }
        outputs.remove(output);
    }
    
    
    /**
     * Adds data to the log.
     * 
     * @param obj any (stringifiable) object
     */
    public static void add(Object obj) {
        // Get String value.
        final String data = String.valueOf(obj);
        
        // Store in the list.
        entries.add(data);
        
        // Output to every selected output type.
        for (PrintStream outputType : outputs) {
            outputType.println(data);
            outputType.flush();
        }
        
        // Add to default output if there were no output types selected.
        if (outputs.size() == 0) {
            DEFAULT.println(data);
            DEFAULT.flush();
        }
    }
    
    /**
     * Adds data to the log with the information of an <code>Exception</code> appended.
     * 
     * @param obj       any (stringifiable) data
     * @param throwable the thrown exception
     */
    public static void add(Object obj, Throwable throwable) {
        if (throwable == null) {
            add(obj);
            return;
        }
        String data = String.valueOf(obj) + String.valueOf(throwable) + "\nWith stacktrace:";
        for (StackTraceElement stElement : throwable.getStackTrace()) {
            data += "\n    " + stElement.toString();
        }
        add(data);
    }
    
    /**
     * Adds verbose data to the log, but only if the verbose setting is enabled.
     * 
     * @param obj any (stringifiable) data
     */
    public static void addVerbose(Object obj) {
        if (isVerbose()) {
            add(obj);
        }
    }
    
    /**
     * An auxiliary, shorthand method to get an identifying string of a node for the logs.
     *  
     * @param node the relevant node
     * @return     the identifying string in the format: "(id,type:name)"
     */
    /*@ pure */ @NonNull public static String n(@NonNull Node node) {
        return "(" + node.getId() + "," + node.getIdentifier() + ")";
    }
}