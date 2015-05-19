package greenmirror;

import groovy.json.JsonException;
import groovy.json.JsonParserType;
import groovy.json.JsonSlurper;
import groovy.json.internal.LazyValueMap;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.util.HashMap;
import java.util.Map;


/**
 * The abstract <tt>CommandHandler</tt> class. It contains shared code for all 
 * <tt>CommandHandler</tt>s. All extending classes should either use the <tt>ClientSide</tt> or
 * the <tt>ServerSide</tt> annotation, or else they won't be registered.
 * 
 * @author Karim El Assal
 */
public abstract class CommandHandler {
    
    // -- Annotations ------------------------------------------------------------------------

    @Retention(RetentionPolicy.RUNTIME)
    public static @interface ClientSide {}
    @Retention(RetentionPolicy.RUNTIME)
    public static @interface ServerSide {}
    
    // -- Exceptions -------------------------------------------------------------------------
    
    /**
     * An <tt>Exception</tt> to indicate that the received data couldn't be parsed correctly.
     * 
     * @author Karim El Assal
     */
    public static class DataParseException extends Exception {
        public DataParseException(String msg) {
            super(msg);
        }
    }
    
    /**
     * An <tt>Exception</tt> to indicate that the received data is incomplete.
     * 
     * @author Karim El Assal
     */
    public static class MissingDataException extends Exception {

    }

    // -- Instance variables -----------------------------------------------------------------
    
    /**
     * The controller.
     */
    private GreenMirrorController controller;
    

    // -- Queries ----------------------------------------------------------------------------

    /**
     * @return The controller.
     */
    /*@ pure */ public GreenMirrorController getController() {
        return controller;
    }

    /**
     * @return The textual description of the <tt>Command</tt> belonging to this handler.
     */
    //@ ensures \result != null;
    /*@ pure */ public String getCommand() {
        return this.getClass().getSimpleName().replace("CommandHandler", "");
    }
    
    
    // -- Setters ----------------------------------------------------------------------------

    /**
     * @param controller  The controller to set.
     */
    //@ ensures getController() == controller;
    public void setController(GreenMirrorController controller) {
        this.controller = controller;
    }

    // -- Commands ---------------------------------------------------------------------------

    /**
     * The method that actually handles the received <tt>Command</tt>. The <tt>Command</tt> is
     * passed via <tt>data</tt> in the specified <tt>format</tt>.
     * @param format The communication format in which <tt>data</tt> is.
     * @param data   The <tt>String</tt> representation of the received <tt>Command</tt>.
     * @throws MissingDataException When the data is incomplete.
     * @throws DataParseException   When the data can't be parsed correctly.
     */
    //@ requires format != null && data != null && getController() != null;
    public abstract void handle(CommunicationFormat format, String data) 
            throws MissingDataException, DataParseException;

    /**
     * Get the <tt>List</tt> of <tt>Transition</tt>s in the queue.
     * @return
     * /
    public List<javafx.animation.Transition> getTransitions() {
        // TODO - implement CommandHandler.getTransitions
        throw new UnsupportedOperationException();
    }*/

    // -- Class usage ------------------------------------------------------------------------
    
    /**
     * Parse JSON data.
     * @param data The JSON data.
     * @return     A <tt>Map</tt> which contains the parsed data.
     * @throws DataParseException If the JSON string was invalid.
     */
    //@ requires data != null;
    public static Map<String, Object> parseJson(String data) throws DataParseException {
        
        try {
            Map<String, Object> res = new HashMap<>();
            res.putAll((LazyValueMap) new JsonSlurper()
                            .setType(JsonParserType.INDEX_OVERLAY).parseText(data));
            return res;
        } catch (JsonException e) {
            throw new DataParseException("There was an error in the received JSON data: " 
                            + e.getMessage());
        }
    }
    
    public static Map<String, Object> toMap(Map<Object, Object> map) {
        Map<String, Object> resultMap = new HashMap<>();
        for (Map.Entry<Object, Object> entry : map.entrySet()) {
            resultMap.put((String) entry.getKey(), (Object) entry.getValue());
        }
        return resultMap;
    }
}