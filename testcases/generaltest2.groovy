initialize(800, 500);

// Add simple center node.
addNode("center").fx("rectangle")
                 .setSize(400, 200)
                 .setPosition(200, 200)
                 .setFill("red")
                 .setArcs(5, 5)
                 .setOpacity(0.5)
                 ;


addTransition("trans1", 2000, {


    // Animate fill and opacity.
    node("center").fx().setFill("white")
                       .setOpacity(1);
                       
    // Add nodes on all placements.
    Node prototype = new Node("placed:").set(fx("rectangle")
                                             .setSize(30, 30)
                                             .setArcs(30, 30));
    addNode(prototype.clone().addRelation(new Relation("on")
                                            .setNodeB(node("center"))
                                            .setPlacement(Placement.RANDOM)));
    addNode(prototype.clone().addRelation(new Relation("on")
                                            .setNodeB(node("center"))
                                            .setPlacement(new Placement.Custom(-30, 0))));
    addNode(prototype.clone().addRelation(new Relation("on")
                                            .setNodeB(node("center"))
                                            .setPlacement(Placement.MIDDLE)));
    addNode(prototype.clone().addRelation(new Relation("on")
                                            .setNodeB(node("center"))
                                            .setPlacement(Placement.EDGE_TOP)));
    addNode(prototype.clone().addRelation(new Relation("on")
                                            .setNodeB(node("center"))
                                            .setPlacement(Placement.EDGE_RIGHT)));
    addNode(prototype.clone().addRelation(new Relation("on")
                                            .setNodeB(node("center"))
                                            .setPlacement(Placement.EDGE_BOTTOM)));
    addNode(prototype.clone().addRelation(new Relation("on")
                                            .setNodeB(node("center"))
                                            .setPlacement(Placement.EDGE_LEFT)));
    addNodes(
        prototype.clone().addRelation(new Relation("on")
                                        .setNodeB(node("center"))
                                        .setPlacement(Placement.CORNER_TOP_LEFT)),
        prototype.clone().addRelation(new Relation("on")
                                        .setNodeB(node("center"))
                                        .setPlacement(Placement.CORNER_TOP_RIGHT)),
        prototype.clone().addRelation(new Relation("on")
                                        .setNodeB(node("center"))
                                        .setPlacement(Placement.CORNER_BOTTOM_RIGHT)),
        prototype.clone().addRelation(new Relation("on")
                                        .setNodeB(node("center"))
                                        .setPlacement(Placement.CORNER_BOTTOM_LEFT)));
    flush();

    // Add relation with temporary FX.
    addNode("eye").fx("rectangle").setSize(100, 100).setArcs(100, 100).setOpacity(0.9).setFill("red").setPosition(0,0);
    flush();
    node("eye").addRelation(
        new Relation("of").setNodeB(node("center"))
                          .setPlacement(Placement.MIDDLE)
                          .setTemporaryFxOfNodeA(node("eye").fx().clone()
                                                            .setFill("blue"))
    );

    flush();
    // Remove relation with temporary FX.
    int cr1 = node("center").getRelations().size();
    removeRelation(
        node("eye").getRelations().withName("of").getFirst()
    );

    flush();
    // Remove node
    int n1 = nodes().size();
    removeNode(
        node("eye")
    );

    //node("eye").fx().setArcs(0, 0); // No nodes were found!

});

// Test remove all nodes.
addTransition("trans2", {
    removeNodes(nodes());
})

// Test moving of multiple rigidly related nodes.
addTransition("trans3", {
    addNodes(
        new Node("n1").set(fx("rectangle")
                            .setSize(100, 50)
                            .setFill(Color.WHITE)),
        new Node("n2").set(fx("rectangle")
                            .setSize(30, 20)
                            .setFill(Color.BROWN)),
        new Node("n3").set(fx("rectangle")
                            .setSize(10, 5)
                            .setFill(Color.GREEN))
    );
    node("n1").fx().setPosition(400, 400);
    addRelations(
        new Relation("on").setNodeA(node("n2"))
                          .setNodeB(node("n1"))
                          .setPlacement(Placement.CORNER_TOP_LEFT)
                          .setRigid(true),
        new Relation("on").setNodeA(node("n3"))
                          .setNodeB(node("n2"))
                          .setPlacement(Placement.CORNER_TOP_LEFT)
                          .setRigid(true)
    );
    
    flush(1000);
    
    node("n1").fx().setPosition(400, 200);
    
    flush(1000);
    
    node("n1").fx().setRotateBy(-90); // doesn't work!
});
addTransition("trans4", {});


// Test rigidly related nodes.

// Test: remove rigid relation, then move the node B of the relation.











