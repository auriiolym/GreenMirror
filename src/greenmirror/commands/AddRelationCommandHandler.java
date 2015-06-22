package greenmirror.commands;

import greenmirror.CommandHandler;
import greenmirror.CommunicationFormat;
import greenmirror.FxWrapper;
import greenmirror.Log;
import greenmirror.Node;
import greenmirror.Placement;
import greenmirror.Relation;
import greenmirror.ServerSide;
import greenmirror.server.ServerController;
import groovy.json.internal.LazyValueMap;

import org.eclipse.jdt.annotation.NonNull;

import java.util.Map;

/**
 * The handler that adds a relation. This command is received from the client. A temporary FX
 * of node A is only added if node A already has an FX.
 * 
 * @author  Karim El Assal
 * @see     AddRelationCommand
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

    @Override
    public void handle(@NonNull CommunicationFormat format, @NonNull String data) 
            throws MissingDataException, DataParseException {
        
        final Relation relation;
        final Node nodeA;
        
        switch (format) {
        default: case JSON:
            
            // Check existence of variables.
            Map<String, Object> map = CommandHandler.parseJson(data);
            if (!map.containsKey("name") || !map.containsKey("nodeA") 
             || !map.containsKey("nodeB") || !map.containsKey("placement") 
             || !map.containsKey("rigid") || !map.containsKey("tempFx")) {
                throw new MissingDataException();
            }

            final String name;
            final Node nodeB;
            final Placement placement;
            final boolean rigid;
            LazyValueMap tempFxMap = null;
            
            // Parse data.
            // rigidity.
            rigid = Boolean.valueOf(String.valueOf(map.get("rigid")));
            // tempFx.
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
                // name and placement.
                if ((name = String.valueOf(map.get("name"))) == null 
                        || (placement = Placement.fromData(String.valueOf(
                                map.get("placement")))) == null) {
                    throw new DataParseException("the name and/or placement data was null");
                }
            } catch (IllegalArgumentException e) {
                throw new DataParseException("the placement data was invalid");
            }
            
            // Create the new relation, still without a node A.
            relation = new Relation()
                            .setName(name)
                            .setNodeB(nodeB)
                            .setPlacement(placement)
                            .setRigid(rigid);
            if (tempFxMap != null && nodeA.getFxWrapper() != null) {
                final FxWrapper tempFxWrapper = nodeA.getFxWrapper().clone();
                tempFxWrapper.setFromMap(tempFxMap);
                relation.setTemporaryFxOfNodeA(tempFxWrapper);
            }
        }
        

        // Add the relation.
        nodeA.addRelation(relation);
        

        // Change node A's FX according to the tempFx.
        if (relation.getTemporaryFxOfNodeA() != null) {
            // We're assuming here that the FX of the Node itself has been set, or else the
            // relation's temporary FX wasn't set (see a few lines up).
            
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
        
        // Add to log.
        Log.add("Relation added: " + relation.toString());
    }

}