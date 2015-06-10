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
public class SwitchPlacementRelationCommandHandler extends CommandHandler {


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


        Relation oldRelation;
        Relation newRelation;
        Node nodeA;
        
        switch (format) {
        default: case JSON:
            
            // Check existence of variables.
            Map<String, Object> map = CommandHandler.parseJson(data);
            if (!map.containsKey("oldId") || !map.containsKey("name") || !map.containsKey("nodeA") 
             || !map.containsKey("nodeB") || !map.containsKey("placement") 
             || !map.containsKey("rigid") || !map.containsKey("tempFx")) {
                throw new MissingDataException();
            }

            String oldId;
            String name;
            Node nodeB;
            Placement placement;
            boolean rigid;
            LazyValueMap tempFxMap = null;
            
            // Parse data.
            // old id.
            oldId = String.valueOf(map.get("oldId"));
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
                throw new DataParseException("The placment data was invalid.");
            }
            
            //TODO: do something when the old relation wasn't found
            System.err.println(nodeA.getRelations());
            // Create the Relation objects.
            oldRelation = nodeA.getRelations().withId(oldId).getFirst();
            newRelation = new Relation()
                            .setName(name)
                            .setNodeB(nodeB)
                            .setPlacement(placement)
                            .setRigid(rigid);
            if (tempFxMap != null && nodeA.getFxWrapper() != null) {
                FxWrapper tempFxWrapper = nodeA.getFxWrapper().clone();
                tempFxWrapper.setFromMap(tempFxMap);
                newRelation.setTemporaryFxOfNodeA(tempFxWrapper);
            }
        }
        

        
        oldRelation.removeFromNodes();
        nodeA.addRelation(newRelation);
        
        

        
        getController().getVisualizer().doPlacement(newRelation);
        
        //TODO: account for already set tempFx from the previous relation.
        // Change node A's FX according to the tempFx.
        if (newRelation.getTemporaryFxOfNodeA() != null) {
            // We're assuming here that the FX of the Node itself has been set.
            
            // Save the current FX as the original, so we can revert back when the relation is 
            //  removed.
            nodeA.getFxWrapper().saveAsOriginal();
            
            // Apply the changes (animated).
            getController().getVisualizer().changeFx(nodeA, 
                        newRelation.getTemporaryFxOfNodeA().toMap());
        }
        
        
        // Alter the location of nodes of other, rigid relations.
        /*TODO: if node A has a rigid relation with another node (on which the current 
        node A is node B there), change it's location {recursive). */
    }

}