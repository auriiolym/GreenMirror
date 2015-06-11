initialize(600, 400);
addNodes(
    new Node("loc:1").set(fx("rectangle")
                          .setSize(200, 400).setPosition(0, 0)
                          .setFill("radial-gradient(center 100px 200px, "
                                                 + "radius 200px, white, red)")),
    new Node("loc:2").set(fx("rectangle")
                          .setSize(200, 400).setPosition(400, 0)
                          .setFill("radial-gradient(center 500px 200px, "
                                                 + "radius 200px, white, red)")),
    new Node("obj").set(fx("circle")
                          .setRadius(20)
                          .setFill("linear-gradient(to bottom, "
                                 + "limegreen, black)"))
);
addRelation(
    new Relation("on").setNodeA(node("obj"))
                      .setNodeB(node("loc:1"))
                      .setPlacement(Placement.MIDDLE)
);

addTransition("switch", {
    switchPlacementRelation(
        node("obj").getPlacementRelation().clone()
                                          .setNextNodeB(nodes("loc:"))
    );
});