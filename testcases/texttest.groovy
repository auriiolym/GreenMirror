initialize(700, 500);

addNodes(
    new Node("r1").set(fx("rectangle")
                        .setFill("white")
                        .setPosition(1, 1)
                        .setSize(100, 50)),
    new Node("t1").set(fx("text")
                        .setText("foooooo!")
                        .setPosition(0, 0)),
    new Node("r2").set(fx("rectangle")
                        .setFill("red")
                        .setOpacity(0.5)
                        .setSize(10, 10)
                        .setArcs(10, 10)),
    new Node("r3").set(fx("rectangle")
                        .setFill("blue")
                        .setOpacity(0.2)
                        .setSize(10, 10)
                        .setArcs(10, 10))
);

flush(1000);

addRelation(
    new Relation("on").setNodeA(node("r2"))
                      .setNodeB(node("t1"))
                      .setPlacement(Placement.EDGE_BOTTOM)
);

flush(1000);

node("t1").fx().setText("barbarbarbarbarbar\nbarbarbarbarbar\nbarbarbarbarbar");

flush(1000);
Relation newR = node("t1").getRelations().getFirst().setPlacement(Placement.EDGE_BOTTOM.withRelativePosition(0, 1));
switchPlacementRelation(newR);

addRelation(
    new Relation("on1").setNodeA(node("r3"))
                      .setNodeB(node("t1"))
                      .setPlacement(Placement.EDGE_BOTTOM));