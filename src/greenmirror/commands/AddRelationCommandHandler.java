package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.FxWrapper;
import greenmirror.Node;
import greenmirror.Placement;
import greenmirror.Relation;
import greenmirror.ServerSide;
import greenmirror.server.ServerController;
import groovy.json.internal.LazyValueMap;

import java.util.Map;

/**
 * The handler that adds a relation. This command is received from the client.
 * 
 * @author Karim El Assal
 */
@ServerSide
public class AddRelationCommandHandler extends CommandHandler {


    // -- Queries ----------------------------------------------------------------------------
    
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
        
        Relation relation;
        Node nodeA;
        
        switch (format) {
        default: case JSON:
            
            // Check existence of variables.
            Map<String, Object> map = CommandHandler.parseJson(data);
            if (!map.containsKey("name") || !map.containsKey("nodeA") 
             || !map.containsKey("nodeB") || !map.containsKey("placement") 
             || !map.containsKey("rigid") || !map.containsKey("tempFx")) {
                throw new MissingDataException();
            }

            String name;
            Node nodeB;
            Placement placement;
            boolean rigid;
            LazyValueMap tempFxMap = null;
            
            // Parse data.
            // rigidity.
            rigid = Boolean.valueOf(String.valueOf(map.get("rigid")));
            // tempFx.
            tempFxMap = (LazyValueMap) map.get("tempFx");
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
                throw new DataParseException("The placement data was invalid.");
            }
            
            
            
            // Execute adding the relation.
            relation = new Relation()
                            .setName(name)
                            .setNodeB(nodeB)
                            .setPlacement(placement)
                            .setRigid(rigid);
            if (tempFxMap != null && nodeA.getFxWrapper() != null) {
                FxWrapper tempFxWrapper = nodeA.getFxWrapper().clone();
                tempFxWrapper.setFromMap(tempFxMap);
                relation.setTemporaryFxOfNodeA(tempFxWrapper);
            }
        }
        

        
        
        nodeA.addRelation(relation);
        
        

        

        

        // Change node A's FX according to the tempFx.
        if (relation.getTemporaryFxOfNodeA() != null) {
            // We're assuming here that the FX of the Node itself has been set.
            
            // Save the current FX as the original, so we can revert back when the relation is 
            //  removed.
            nodeA.getFxWrapper().saveAsOriginal();
            
            // Apply the changes (animated).
            getController().getVisualizer().changeFx(nodeA, 
                    relation.getTemporaryFxOfNodeA().toMap());
        }

        // Do this AFTER applying the temporary FX, so the positioning properties are ignored 
        // because they haven't changed yet. 
        getController().getVisualizer().doPlacement(relation);        
        
        // Alter the location of nodes of other, rigid relations.
        /*TODO: if node A has a rigid relation with another node (on which the current 
        node A is node B there), change it's location {recursive). */
    }

}