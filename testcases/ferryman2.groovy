initialize(1000, 600, 3000);


// Background
addNode("bank:left").fx("Rectangle")
                    .setWidth(300)
                    .setHeight(600)
                    .setX(0)
                    .setY(0)
                    .setFill(Color.GREEN);
addNode("bank:right").fx("rectangle")
                     .setWidth(300)
                     .setHeight(600)
                     .setPosition(700, 0)
                     .setFill(Color.GREEN);


                     
// Boat
addNodes(
    new Node("boat").set(fx("Rectangle")
                    .setSize(150, 50)
                    .setFill(Color.WHITE)),
    /*new Node("ferryman").set(fx("Circle")
                    .setRadius(20)
                    .setFill(Color.BLACK))*/
    new Node("ferryman").set(fx("rectangle")
                    .setSize(20, 20)
                    .setFill(Color.BLACK)),
);
addRelations(
    new Relation("moored_to")
                    .setNodeA(node("boat"))
                    .setNodeB(node("bank:left"))
                    .setPlacement(Placement.EDGE_RIGHT_MIDDLE),
    new Relation("on")
                    .setNodeA(node("ferryman"))
                    .setNodeB(node("boat"))
                    .setPlacement(Placement.MIDDLE)
                    .setRigid(true)
);

// Movable objects
addNodes(
    new Node("cargo:goat").set(
                    fx("rectangle")
                    .setSize(30, 20)
                    .setFill(Color.RED)),
    new Node("cargo:wolf").set(
                    fx("rectangle")
                    .setSize(30, 25)
                    .setFill(Color.YELLOW)),
    new Node("cargo:cabb").set(
                    fx("rectangle")
                    .setSize(20, 20)
                    .setFill(Color.DARKBLUE)),
);
    // option one for adding the Relations.
    /*
addRelations(
    new Relation("on").setPlacement(Placement.RANDOM))
                      .setNodeA(node("bank:left"))
                      .setNodeB(node("cargo:goat")),
    new Relation("on").setPlacement(Placement.RANDOM))
                      .setNodeA(node("bank:left"))
                      .setNodeB(node("cargo:wolf")),
    new Relation("on").setPlacement(Placement.RANDOM))
                      .setNodeA(node("bank:left"))
                      .setNodeB(node("cargo:cabb")),
    new Relation("likes").setNodeA(node("cargo:wolf")).setNodeB(node("cargo:goat")),
    new Relation("likes").setNodeA(node("cargo:goat")).setNodeB(node("cargo:cabb")),
);
*/
    // option two for adding the Relations.
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
                      .setNextPlacement(Placement.EDGE_RIGHT_MIDDLE,
                                        Placement.EDGE_LEFT_MIDDLE)
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
                            .setPlacement(Placement.EDGE_RIGHT_MIDDLE)
    );
    flush();
    //removeNode(node("cargo:" + eatee)); // This is how it should go.
    node("cargo:" + eatee).fx().setOpacity(0);
});





