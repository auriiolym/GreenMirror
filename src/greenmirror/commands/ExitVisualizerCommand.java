package greenmirror.commands;

import greenmirror.Command;
import greenmirror.CommunicationFormat;
import groovy.json.JsonOutput;

import org.eclipse.jdt.annotation.NonNull;

import java.util.LinkedHashMap;

/**
 * The command that signals that the visualizer should exit. This command is sent to the server.
 * 
 * Values sent: none
 */
public class ExitVisualizerCommand extends Command {

    // -- Commands ---------------------------------------------------------------------------

    @Override
    public String getFormattedString(@NonNull CommunicationFormat format) {
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