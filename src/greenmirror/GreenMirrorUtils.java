package greenmirror;

import joptsimple.OptionParser;
import org.eclipse.jdt.annotation.NonNull;

import java.util.Arrays;
import java.util.Random;

/**
 * An auxiliary class containing several simple methods.
 * 
 * @author Karim El Assal
 */
public abstract class GreenMirrorUtils {
    
    // -- Constants --------------------------------------------------------------------------
    
    /** the IllegalStateException message set when a JavaFX node should've been set */
    public static final String MSG_NO_FXNODE = "no JavaFX node set";

    /** the seed for the random number generator */
    private static final Random RAND = new Random();
    
    
    // -- Commands ---------------------------------------------------------------------------

    /**
     * Adds the verbose option to the command line option parser.
     * 
     * @param parser the JOpt Simple parser to add it to
     * @see   OptionParser
     * @see   CommandLineOptionHandler#setParserSettings(OptionParser)
     */
    public static void addCommandLineVerboseOption(@NonNull OptionParser parser) {
        parser.acceptsAll(Arrays.asList("v", "verbose"), "use verbose output");
    }

    /**
     * Capitalizes the first character of a <code>String</code>.
     * 
     * @param str the string
     * @return    the string with its first character capitalized
     */
    //@ ensures Character.toUpperCase(str.charAt(0)) + (str.length() > 1 ? str.substring(1) : "");
    /*@ pure */ @NonNull public static String capitalizeFirstChar(@NonNull String str) {
        return Character.toUpperCase(str.charAt(0)) + (str.length() > 1 ? str.substring(1) : "");
    }
    
    /**
     * Calculates a random value between <code>min</code> and <code>max</code>.
     * 
     * @param min the lower boundary
     * @param max the upper boundary
     * @return    a random value
     */
    /*@ pure */ public static double getRandomBetween(double min, double max) {
        return min + RAND.nextDouble() * (max - min);
    }
    
}
