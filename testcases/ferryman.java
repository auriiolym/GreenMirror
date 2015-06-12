// Ferryman
initialize(500, 300, 1000);


// Background.
addNodes(
    new Node("bank:left").set(fx("Rectangle")
                                .setSize(150, 300)
                                .setPosition(0, 0)
                                .setFill("linear-gradient(to right, darkgreen 0%, limegreen 92.5%, #00F0F0 100%)")),
    new Node("river").set(fx("rectangle")
                                .setSize(200, 300)
                                .setPosition(150, 0)
                                .setFill("linear-gradient(to right, #00F0F0 0%, #00DEDE 50%, #00F0F0 100%)")),
    new Node("bank:left").set(fx("Rectangle")
                                .setSize(150, 300)
                                .setPosition(350, 0)
                                .setFill("linear-gradient(to left, darkgreen 0%, limegreen 92.5%, #00F0F0 100%)"))
);

                     
// Ferry.
addNodes(
    new Node("ferry").set(fx("image")
                                .setImageFromFile("testcases/img/boat.png")
                                .setFitWidth(100)
                                .setPreserveRatio(true))
);

// Cargo.
addNodes(
    new Node("cargo:goat").set(fx("image")
                                .setImageFromFile("testcases/img/goat.png")
                                .setFitWidth(50)
                                .setPreserveRatio(true)),
    new Node("cargo:wolf").set(fx("image")
                                .setImageFromFile("testcases/img/wolf.png")
                                .setFitWidth(50)
                                .setPreserveRatio(true)),
    new Node("cargo:cabb").set(fx("image")
                                .setImageFromFile("testcases/img/cabbage.png")
                                .setFitWidth(50)
                                .setPreserveRatio(true)),
);

// Relations.
Relation onRelation = new Relation("on")
                                .setNodeB(node("bank:left"))
                                .setPlacement(Placement.RANDOM);
addRelations(
    new Relation("moored_to").setNodeA(node("ferry"))
                             .setNodeB(node("bank:left"))
                             .setPlacement(Placement.EDGE_RIGHT),
    onRelation.clone().setNodeA(node("cargo:goat")),
    onRelation.clone().setNodeA(node("cargo:wolf")),
    onRelation.clone().setNodeA(node("cargo:cabb")),
    new Relation("likes").setNodeA(node("cargo:wolf")).setNodeB(node("cargo:goat")),
    new Relation("likes").setNodeA(node("cargo:goat")).setNodeB(node("cargo:cabb")),
);



// Load cargo.
addTransition("load_(goat|wolf|cabb)", { String cargo ->
    switchPlacementRelation(
        new Relation("on").setNodeA(node("cargo:" + cargo))
                          .setNodeB(node("ferry"))
                          .setPlacement(Placement.RANDOM)
                          .setRigid(true)
    );
});
// Make the ferry cross the river.
addTransition("cross", {
    node("ferry").fx().setRotateBy(180);
    
    switchPlacementRelation(
        node("ferry").getRelation(1, "moored_to").clone()
                                                 .setNextNodeB(nodes().ofType("bank"))
                                                 .setNextPlacement(Placement.EDGE_RIGHT,
                                                                   Placement.EDGE_LEFT)
    );
});
// Unload all cargo.
addTransition("unload", {
    for (Node cargo : node("ferry").getRelatedNodes(-1, "on").ofType("cargo")) {
        switchPlacementRelation(
            new Relation("on").setNodeA(cargo)
                              .setNodeB(node("ferry").getRelatedNode(1, "moored_to"))
                              .setPlacement(Placement.RANDOM)
        );
    }
});
// Make one cargo object eat another.
addTransition("(.*)_eat_(.*)", {String eaterStr, String preyStr ->
    Node eater = node("cargo:" + eaterStr); 
    Node prey  = node("cargo:" + preyStr);
    
    // Make it bigger, so it is scarier.
    eater.fx().setFitWidth(eater.fx().getFitWidth() * 3);
    // Move it to its prey.
    addRelation(
        new Relation("eats").setNodeA(eater)
                            .setNodeB(prey)
                            .setPlacement(Placement.MIDDLE)
    );
    flush();
    // And remove the prey.
    removeNode(prey); 
});