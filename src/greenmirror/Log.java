package greenmirror;

import java.io.PrintStream;
import java.text.SimpleDateFormat;
import java.util.Calendar;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;


/**
 * The class handling the log.
 * 
 * @author Karim El Assal
 */
public class Log {
    
    public static final PrintStream DEFAULT = new PrintStream(System.out) {
        
        @Override
        public void print(String str) {
            super.print("[" + getTimestamp() + "] " + str);
        }
        
        @Override
        public void close() {
            print("Default log output closed.");
        }
    };
    
    // -- Enumerations -----------------------------------------------------------------------

    // -- Constants --------------------------------------------------------------------------
    
    //public static final PrintStream DEFAULT = System.out;
    

    // -- Class variables --------------------------------------------------------------------
    
    /**
     * Entries of the log.
     */
    //@ private invariant entries != null;
    private static List<String> entries = new LinkedList<String>();
    
    /**
     * The selected log outputs.
     */
    //@ private invariant outputs != null;
    private static Set<PrintStream> outputs = new HashSet<>();
    
    /**
     * Whether to log verbose data.
     */
    private static boolean verbose = false;
    

    // -- Class usage ------------------------------------------------------------------------
 


    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @return The log entries.
     */
    //@ private ensures \result != null && \result == entries;
    /*@ pure */ private static List<String> getEntries() {
        return entries;
    }
    
    /**
     * @return The current date and time.
     */
    //@ ensures \result != null;
    /*@ pure */ public static String getTimestamp() {
        return new SimpleDateFormat("YYYY-MM-dd HH:mm:ss.SSS")
                    .format(Calendar.getInstance().getTime());
    }
    
    /**
     * @return Whether to output verbose data.
     */
    /*@ pure */ public static boolean isVerbose() {
        return verbose;
    }
    
    // -- Setters ----------------------------------------------------------------------------

    /**
     * @param verbose Set whether to be verbose.
     */
    //@ ensures isVerbose() == verbose;
    public static void setVerbose(boolean verbose) {
        Log.verbose = verbose;
    }
    
    /**
     * Add <tt>output</tt> to the list of outputs.
     * @param output The type of output.
     */
    //@ requires output != null;
    public static void addOutput(PrintStream output) {
        outputs.add(output);
    }
    
    
    // -- Commands ---------------------------------------------------------------------------
    
    
    /**
     * Remove the selected output and clean up if necessary.
     * @param output The output.
     */
    public static void removeOutput(PrintStream output) {
        if (outputs.contains(output)) {
            output.close();
        }
        outputs.remove(output);
    }
    
    
    /**
     * Add data to the log.
     * @param obj Any (stringifiable) data.
     */
    public static void add(Object obj) {
        // Get String value.
        String data = String.valueOf(obj);
        
        // Store in the list.
        getEntries().add(data);
        
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
     * Add data to the log with the information of an <tt>Exception</tt> appended.
     * @param obj       Any (stringifiable) data.
     * @param throwable The thrown exception.
     */
    //@ requires obj != null && exception != null;
    public static void add(Object obj, Throwable throwable) {
        String data = String.valueOf(obj) + String.valueOf(throwable) + "\nWith stacktrace:";
        for (StackTraceElement stElement : throwable.getStackTrace()) {
            data += "\n    " + stElement.toString();
        }
        add(data);
    }
    
    /**
     * Add verbose data to the log, but only if the verbose setting is enabled.
     * @param obj Any (stringifiable) data.
     */
    public static void addVerbose(Object obj) {
        if (isVerbose()) {
            add(obj);
        }
    }
}