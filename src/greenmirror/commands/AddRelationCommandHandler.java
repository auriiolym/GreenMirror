package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.Log;
import greenmirror.Node;
import greenmirror.Placement;
import greenmirror.Relation;
import greenmirror.VisualComponent;
import greenmirror.server.ServerController;
import groovy.json.internal.LazyValueMap;

import java.util.Map;

import javafx.animation.Transition;
import javafx.util.Duration;

/**
 * The handler that adds a relation. This command is received from the client.
 */
public class AddRelationCommandHandler extends CommandHandler {


    // -- Queries ----------------------------------------------------------------------------
    
    /* (non-Javadoc)
     * @see greenmirror.CommandHandler#getController()
     */
    @Override
    //@ ensures \result != null;
    /*@ pure */ public ServerController getController() {
        return (ServerController) super.getController();
    }

    
    // -- Commands ---------------------------------------------------------------------------

    /**
     * Handle the received command. 
     * @param format The format in which the data is received.
     * @param data   The (raw) received data.
     * @throws MissingDataException When the data is incomplete.
     * @throws DataParseException   When parsing the data went wrong.
     */
    //@ requires getController() != null && format != null && data != null;
    public void handle(CommunicationFormat format, String data) 
            throws MissingDataException, DataParseException {
        
        String id;
        String name;
        Node nodeA;
        Node nodeB;
        Placement placement;
        boolean rigid;
        LazyValueMap tempAppearance = null;
        Relation relation;
        
        switch (format) {
        default: case JSON:
            
            // Check existence of variables.
            Map<String, Object> map = CommandHandler.parseJson(data);
            if (!map.containsKey("id") || !map.containsKey("name") || !map.containsKey("nodeA") 
             || !map.containsKey("nodeB") || !map.containsKey("placement") 
             || !map.containsKey("rigid") || !map.containsKey("tempAppearance")) {
                throw new MissingDataException();
            }
            
            // Parse data.
            // id.
            id = String.valueOf(map.get("id"));
            // rigidity.
            rigid = Boolean.valueOf(String.valueOf(map.get("rigid")));
            // tempAppearance.
            tempAppearance = (LazyValueMap) map.get("tempAppearance");
            try {
                // node A
                if ((nodeA = getController().getNode(
                        Integer.parseInt(String.valueOf(map.get("nodeA"))))) == null) {
                    throw new DataParseException("Node A was not found on the visualizer.");
                }
                // node B
                if ((nodeB = getController().getNode(
                        Integer.parseInt(String.valueOf(map.get("nodeB"))))) == null) {
                    throw new DataParseException("Node B was not found on the visualizer.");
                }
            } catch (NumberFormatException e) {
                throw new DataParseException("The id of node A and/or B is invalid.");
            }
            try {
                // name, placement.
                if ((name = String.valueOf(map.get("name"))) == null 
                        || (placement = Placement.fromData(String.valueOf(
                                map.get("placement")))) == null) {
                    throw new DataParseException("The name and/or placement data was null.");
                }
            } catch (IllegalArgumentException e) {
                throw new DataParseException("The placment data was invalid.");
            }
        }
        
        Duration animationDuration = Duration.millis(
                getController().getVisualizer().getCurrentAnimationDuration());

        // Execute adding the relation.
        relation = new Relation()
                        .setName(name)
                        .setNodeB(nodeB)
                        .setPlacement(placement)
                        .setRigid(rigid)
                        //.setTemporaryAppearanceOfNodeA(tempAppearance) // not needed.
                        ;
        nodeA.addRelation(relation);
        
        // Place the node correctly.
        if (placement != Placement.NONE) {
            Transition transition = nodeA.getAppearance().animateToPositionWithMiddlePoint(
                                nodeB.getAppearance().calculatePosition(placement), 
                                animationDuration);

            // Add a log entry.
            Log.add("Placement of node " + nodeA.getId() + " changed to " 
                    + placement.toData() + " on nod " + nodeB.getId());
            
            // And put the visualization in the queue.
            getController().getVisualizer().addToVisualizationsQueue(transition);
        }
        
        // Alter the location of nodes of other, rigid relations.
        /*TODO: if node A has a rigid relation with another node (on which the current 
        node A is node B there), change it's location {recursive). */
        
        
        // Change the node A's appearance according to the tempAppearance.
        if (tempAppearance != null) {
            Transition transition = nodeA.getAppearance().animateFromMap(tempAppearance, 
                    VisualComponent.ChangeType.NORMAL, 
                    getController().getVisualizer().getCurrentAnimationDuration());
            
            Log.add("Appearance of node " + nodeA.getId() + " temporarily changed due to "
                    + "the relation with node " + nodeB.getId() + ".");
            
            // And put the visualization in the queue.
            getController().getVisualizer().addToVisualizationsQueue(transition);
        }
    }

}