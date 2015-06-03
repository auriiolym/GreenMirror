package greenmirror;

import joptsimple.OptionParser;

import java.util.Arrays;
import java.util.Random;

/**
 * An auxiliary class for several basic methods.
 * 
 * @author Karim El Assal
 */
public abstract class GreenMirrorUtils {
    
    // -- Constants --------------------------------------------------------------------------
    
    /** the IllegalArgumentException message set when a JavaFX node should've been set */
    public static final String MSG_NO_FXNODE = "no JavaFX node set.";
    
    /** the postfix of any NullPointerException message */
    public static final String MSG_NOT_NULL_POSTFIX = " can't be null.";
    
    
    // -- Commands ---------------------------------------------------------------------------
    
    /**
     * Checks if <code>variable</code> is <code>null</code> and if so, throw a 
     * <code>NullPointerException</code> with a message if <code>description</code> is set.
     * 
     * @param variable    the object to check if it's <code>null</code>
     * @param description the short description of the object that will be checked.
     *                    {@link #MSG_NOT_NULL_POSTFIX} will be appended to it
     * @throws NullPointerException if <code>variable</code> is <code>null</code>
     */
    public static void checkNull(Object variable, String description) {
        if (variable == null) {
            if (description == null) {
                throw new NullPointerException();
            } else {
                throw new NullPointerException(description + MSG_NOT_NULL_POSTFIX);
            }
        }
    }

    /**
     * Adds the verbose option to the command line option parser.
     * 
     * @param parser the parser to add it to
     * @see   OptionParser
     * @see   CommandLineOptionHandler#setParserSettings(OptionParser)
     */
    public static void addCommandLineVerboseOption(/*@ non_null */ OptionParser parser) {
        parser.acceptsAll(Arrays.asList("v", "verbose"), "use verbose output");
    }

    /**
     * Capitalizes the first character of a <code>String</code>.
     * 
     * @param str the <code>String</code>
     * @return    the <code>String</code> with its first character capitalized
     * @throws NullPointerException if <code>str</code> is <code>null</code>
     */
    //@ ensures \result.equals(Character.toUpperCase(str.charAt(0)) + str.substring(1));
    /*@ pure non_null */ public static String capitalizeFirstChar(/*@ non_null */ String str) {
        if (str == null) {
            throw new NullPointerException("string" + GreenMirrorUtils.MSG_NOT_NULL_POSTFIX);
        }
        return Character.toUpperCase(str.charAt(0)) + str.substring(1);
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
    private final static Random RAND = new Random();
}
