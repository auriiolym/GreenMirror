package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.Node;
import greenmirror.Relation;
import greenmirror.ServerSide;
import greenmirror.server.ServerController;
import greenmirror.server.Visualizer;
import org.eclipse.jdt.annotation.NonNull;

import java.util.Map;

import javafx.util.Duration;


/**
 * The handler that removes a node from the visualizer. It doesn't actually remove it, but 
 * just makes it invisible and untouchable. This command is received from the client.
 * 
 * @author  Karim El Assal
 * @see     RemoveNodeCommand
 */
@ServerSide
public class RemoveNodeCommandHandler extends CommandHandler {

    
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public void handle(@NonNull CommunicationFormat format, @NonNull String data) 
            throws MissingDataException, DataParseException {


        final Node node;
        
        switch (format) {
        default: case JSON:
            
            // Check data existence.
            final Map<String, Object> map = CommandHandler.parseJson(data);
            if (!map.containsKey("id")) {
                throw new MissingDataException();
            }

            // Parse data.
            try {
                // Node id.
                node = getController().getNode(Integer.parseInt(String.valueOf(map.get("id"))));
            } catch (NumberFormatException e) {
                throw new DataParseException("the id of the node is invalid: " + map.get("id"));
            } catch (IllegalArgumentException e) {
                throw new DataParseException("the node with id " + map.get("id") + " is not "
                        + "found on the visualizer");
            }
        }
        
        Log.add("Node removed: " + Log.n(node));
        

        final Visualizer visualizer = ((ServerController) getController()).getVisualizer();
        final Duration duration = Duration.millis(visualizer.getCurrentAnimationDuration());
        if (duration == null) { // @NonNull annotation formality.
            throw new RuntimeException("Duration.millis(double) returned null");
        }
        
        /**
         * A node will be removed, so this is what will happen:
         * - All nodes that have a connection with this node and have a temporary FX set, will be
         *   reverted to their original FX.
         * - All relations will be removed.
         * - This node will get a fade out if it has an FX.
         */
        for (Relation relation : node.getRelations(-1)) {
            // Revert the temporary FX of node A.
            if (relation.getTemporaryFxOfNodeA() != null) {
                final Node nodeA = relation.getNodeA();
                visualizer.changeFx(nodeA, 
                        nodeA.getFxWrapper().getOriginalFxWrapper().toMapWithoutPositionData());
                nodeA.getFxWrapper().saveAsOriginal();
            }
        }
        // Remove relations.
        node.getRelations().removeAll();
        // Only remove from visualizer if node has an FX.
        if (node.getFxWrapper() != null) {
            visualizer.addToVisualizationsQueue(
                    node.getFxWrapper().animateOpacity(0.0, 
                            duration));
        }
    }
}