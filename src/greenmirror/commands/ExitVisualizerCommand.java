package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import groovy.json.JsonOutput;

import java.util.LinkedHashMap;

/**
 * The command that signals that the visualizer should exit.
 * This command is sent to the server.
 * 
 * Values sent:
 * none
 */
public class ExitVisualizerCommand extends Command {

    // -- Instance variables -----------------------------------------------------------------
    

    // -- Constructors -----------------------------------------------------------------------

    
    // -- Queries ----------------------------------------------------------------------------
    
    
    // -- Commands ---------------------------------------------------------------------------

    /**
     * Prepare the <code>Command</code>.
     */
    public void prepare() {
        // Nothing to prepare.
    }

    /**
     * Fetch the raw data that will be sent.
     * @param format The format in which the data will be.
     */
    //@ requires format != null;
    public String getFormattedString(CommunicationFormat format) {
        switch (format) {
        default: case JSON:
            return JsonOutput.toJson(new LinkedHashMap<String, Double>() {
                {
                    // Nothing to send.
                }
            });
        }
    }
}