initialize(480, 200);
addNodes(
  new Node("loc:1").set(fx("rectangle")
                        .setSize(160, 200).setPosition(0, 0)
                        .setFill("radial-gradient(center  80px 100px, "
                                               + "radius 150px, white, red)")),
  new Node("loc:2").set(fx("rectangle")
                        .setSize(160, 200).setPosition(320, 0)
                        .setFill("radial-gradient(center 400px 100px, "
                                               + "radius 150px, white, red)")),
  new Node("obj")  .set(fx("circle")
                        .setRadius(20)
                        .setFill("linear-gradient(to bottom, limegreen, black)"))
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