initialize(700, 400, 5000);

addNode(
    new Node("1").set(fx("rectangle")
                      .setSize(200, 100)
                      .setPosition(0, 200)
                      .setRotate(0)
                      .setFill("red")));
addNodes(
    new Node("2").set(fx("rectangle")
                      .setSize(20, 10))
                 .addRelation(new Relation("on")
                              .setNodeB(node("1"))
                              .setPlacement(Placement.EDGE_RIGHT_MIDDLE)
                              .setRigid(true)),
    new Node("3").set(fx("rectangle")
                      .setSize(20, 10))
                 .addRelation(new Relation("on")
                              .setNodeB(node("1"))
                              .setPlacement(Placement.EDGE_LEFT_MIDDLE)
                              .setRigid(true))
);

addTransition("rotate", {
    
    node("1").fx().setRotateBy(90)
                  .setPosition(100, 200);
});