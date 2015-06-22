package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.FxWrapper;
import greenmirror.Node;
import greenmirror.Placement;
import greenmirror.Relation;
import greenmirror.ServerSide;
import greenmirror.server.ServerController;
import greenmirror.server.Visualizer;
import groovy.json.internal.LazyValueMap;

import org.eclipse.jdt.annotation.NonNull;

import java.util.Map;

/**
 * The handler that switches a placement relation. This command is received from the client.
 * 
 * @author  Karim El Assal
 * @see     SwitchPlacementRelationCommand
 */
@ServerSide
public class SwitchPlacementRelationCommandHandler extends CommandHandler {

 
    // -- Commands ---------------------------------------------------------------------------

    @Override
    public void handle(@NonNull CommunicationFormat format, @NonNull String data) 
            throws MissingDataException, DataParseException {


        final Relation oldRelation;
        final Relation newRelation;
        final Node nodeA;
        
        switch (format) {
        default: case JSON:
            final Map<String, Object> map = CommandHandler.parseJson(data);
            
            // Check data existence.
            if (!map.containsKey("oldId") || !map.containsKey("name") || !map.containsKey("nodeA") 
             || !map.containsKey("nodeB") || !map.containsKey("placement") 
             || !map.containsKey("rigid") || !map.containsKey("tempFx")) {
                throw new MissingDataException();
            }

            final String oldId;
            final String name;
            final Node nodeB;
            final Placement placement;
            final boolean rigid;
            final LazyValueMap tempFxMap;
            
            // Parse data.
            // Old id.
            oldId = String.valueOf(map.get("oldId"));
            if (oldId == null) {
                throw new DataParseException("old relation id is invalid");
            }
            
            // Rigidity.
            rigid = Boolean.valueOf(String.valueOf(map.get("rigid")));
            // Temporary FX.
            tempFxMap = (LazyValueMap) map.get("tempFx");
            try {
                // Node A.
                nodeA = getController().getNode(Integer.parseInt(String.valueOf(map.get("nodeA"))));
                // Node B.
                nodeB = getController().getNode(Integer.parseInt(String.valueOf(map.get("nodeB"))));
            } catch (NumberFormatException e) {
                throw new DataParseException("the id of node A and/or B is invalid");
            } catch (IllegalArgumentException e) {
                throw new DataParseException("node A and/or B are not found on the visualizer");
            }
            
            try {
                // Name and placement.
                if ((name = String.valueOf(map.get("name"))) == null 
                        || (placement = Placement.fromData(String.valueOf(
                                map.get("placement")))) == null) {
                    throw new DataParseException("the name and/or placement data is null");
                }
            } catch (IllegalArgumentException e) {
                throw new DataParseException("the placment data is invalid");
            }
            
            
            //TODO: do something when the old relation wasn't found
            // Get the old relation instance and create the new relation. 
            oldRelation = nodeA.getRelations().withId(oldId).getFirst();
            newRelation = new Relation()
                            .setName(name)
                            .setNodeB(nodeB)
                            .setPlacement(placement)
                            .setRigid(rigid);
            if (tempFxMap != null && nodeA.getFxWrapper() != null) {
                final FxWrapper tempFxWrapper = nodeA.getFxWrapper().clone();
                tempFxWrapper.setFromMap(tempFxMap);
                newRelation.setTemporaryFxOfNodeA(tempFxWrapper);
            }
        }


        final Visualizer visualizer = ((ServerController) getController()).getVisualizer();
        
        
        // Remove old relation.
        oldRelation.removeFromNodes();
        nodeA.addRelation(newRelation);
        
        
        /*
         * cases:
         *  1. no old temp fx, no new temp fx: do nothing
         *  2. no old temp fx,    new temp fx: save current as original, change to new
         *  3.    old temp fx, no new temp fx: revert to original
         *  4.    old temp fx,    new temp fx:                           change to new
         */
        
        // Case 3: revert to original FX.
        if (oldRelation.getTemporaryFxOfNodeA() != null 
         && newRelation.getTemporaryFxOfNodeA() == null) {
            visualizer.changeFx(nodeA, 
                    nodeA.getFxWrapper().getOriginalFxWrapper().toMapWithoutPositionData());
            nodeA.getFxWrapper().saveAsOriginal();
        }
        
        // Cases 2 and 4: change node A's FX according to the tempFx.
        if (newRelation.getTemporaryFxOfNodeA() != null) {
            // We're assuming here that the FX of the Node itself has been set (which 
            //  is checked around line 95).
            
            // Case 2: save the current FX as the original, so we can revert back when the 
            //  relation is removed.
            if (oldRelation.getTemporaryFxOfNodeA() == null) {
                nodeA.getFxWrapper().saveAsOriginal();
            }
            
            // Apply the changes (animated).
            visualizer.changeFx(nodeA, 
                        newRelation.getTemporaryFxOfNodeA().toMap());
        }

        
        visualizer.doPlacement(newRelation);
    }
}