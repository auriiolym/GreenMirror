package greenmirror.client;

/**
 * An interface which can be implemented by handlers designed for specific script types. After execution, mutation commands should have been passed to the controller.
 */
public interface ScriptHandler {

    GMClient getController();

    GMClient getController();

    /**
     * 
     * @param controller
     */
    void setController(GMClient controller);

    /**
     * 
     * @param script
     */
    void parse(String script);

    void execute();

}