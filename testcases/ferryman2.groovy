initialize(1000, 600, 2000);


// Background
addNode("bank:left").fx("Rectangle")
                    .setSize(300, 600)
                    .setPosition(0, 0)
                    .setFill(Color.GREEN);
addNode("bank:right").fx("rectangle")
                     .setSize(300, 600)
                     .setPosition(700, 0)
                     .setFill(Color.GREEN);

                     
// Boat
addNodes(
    new Node("boat").set(fx("image")
                    .setImageFromFile("testcases/boat.png")
                    .setFitWidth(100)
                    .setPreserveRatio(true)),
    new Node("ferryman").set(fx("circle")
                    .setRadius(10)
                    .setFill(Color.BLUE))
);
addRelations(
    new Relation("moored_to")
                    .setNodeA(node("boat"))
                    .setNodeB(node("bank:left"))
                    .setPlacement(Placement.EDGE_RIGHT),
    new Relation("on")
                    .setNodeA(node("ferryman"))
                    .setNodeB(node("boat"))
                    .setPlacement(Placement.MIDDLE)
                    .setRigid(true)
);

// Movable objects
addNodes(
    new Node("cargo:goat").set(
                    fx("image")
                    .setImageFromFile("testcases/goat2.png")
                    .setFitWidth(50)
                    .setPreserveRatio(true)),
    new Node("cargo:wolf").set(
                    fx("image")
                    .setImageFromFile("testcases/wolf.png")
                    .setFitWidth(50)
                    .setPreserveRatio(true)),
    new Node("cargo:cabb").set(
                    fx("image")
                    .setImageFromFile("testcases/cabbage.png")
                    .setFitWidth(50)
                    .setPreserveRatio(true)),
);

// Relations.
Relation onRelation = new Relation("on")
                                .setNodeB(node("bank:left"))
                                .setPlacement(Placement.RANDOM);
addRelations(
    onRelation.clone().setNodeA(node("cargo:goat")),
    onRelation.clone().setNodeA(node("cargo:wolf")),
    onRelation.clone().setNodeA(node("cargo:cabb")),
    new Relation("likes").setNodeA(node("cargo:wolf")).setNodeB(node("cargo:goat")),
    new Relation("likes").setNodeA(node("cargo:goat")).setNodeB(node("cargo:cabb")),
);




addTransition("load(.*)", { String cargo ->
    switchPlacementRelation(
        new Relation("on").setNodeA(node("cargo:" + cargo))
                          .setNodeB(node("boat"))
                          .setPlacement(Placement.RANDOM)
                          .setRigid(true)
    );
});
addTransition("cross", {
    node("boat").fx().setRotateBy(180);
    //flush();
    switchPlacementRelation(
        // Option 1:
        new Relation().fromRelation(node("boat").getRelation(1, "moored_to"))
                      .setNextNodeB(nodes().ofType("bank"))
                      .setNextPlacement(Placement.EDGE_RIGHT,
                                        Placement.EDGE_LEFT)
    );
});
addTransition("unload", {
    NodeList cargo = node("boat").getRelatedNodes(-1, "on").ofType("cargo");
    for (Node cargoNode : cargo) {
        switchPlacementRelation(
            new Relation("on").setNodeA(cargoNode)
                              .setNodeB(node("boat").getRelatedNode(1, "moored_to"))
                              .setPlacement(Placement.RANDOM)
                              .setRigid(false)
        );
    }
});
addTransition("(.*)_eat_(.*)", {String eater, String eatee ->
    addRelation(
        new Relation("eats").setNodeA(node("cargo:" + eater))
                            .setNodeB(node("cargo:" + eatee))
                            .setPlacement(Placement.EDGE_RIGHT)
    );
    flush();
    removeNode(node("cargo:" + eatee)); 
});





