initialize(500, 300, 1000);

addNodes(
  // Background.
  new Node("bank:left")
        .set(fx("rectangle").setSize(150, 300).setPosition(0, 0)
                            .setFill("linear-gradient(to right, darkgreen 0%, limegreen 92.5%, #00F0F0 100%)")),
  new Node("river")
        .set(fx("rectangle").setSize(200, 300).setPosition(150, 0)
                            .setFill("linear-gradient(to right, #00F0F0 0%, #00DEDE 50%, #00F0F0 100%)")),
  new Node("bank:right")
        .set(fx("rectangle").setSize(150, 300).setPosition(350, 0)
                            .setFill("linear-gradient(to left, darkgreen 0%, limegreen 92.5%, #00F0F0 100%)")),
  // Ferry.
  new Node("ferry")
        .set(fx("image").setImageFromFile("testcases/img/boat.png")
                        .setFitWidth(100).setPreserveRatio(true)),
  // Cargo.
  new Node("cargo:goat")
        .set(fx("image").setImageFromFile("testcases/img/goat.png")
                       .setFitWidth(50).setPreserveRatio(true)),
  new Node("cargo:wolf")
        .set(fx("image").setImageFromFile("testcases/img/wolf.png")
                        .setFitWidth(50).setPreserveRatio(true)),
  new Node("cargo:cabb")
        .set(fx("image").setImageFromFile("testcases/img/cabbage.png")
                        .setFitWidth(50).setPreserveRatio(true)),
);

// Relations.
Relation onRelation = new Relation("on").setNodeB(node("bank:left"))
                                        .setPlacement(Placement.RANDOM);
addRelations(
  new Relation().setNodeA(node("ferry"))
                .setName("moored_to")
                .setNodeB(node("bank:left")).setPlacement(Placement.EDGE_RIGHT),
  onRelation.clone().setNodeA(node("cargo:goat")),
  onRelation.clone().setNodeA(node("cargo:wolf")),
  onRelation.clone().setNodeA(node("cargo:cabb")),
  new Relation().setNodeA(node("cargo:wolf"))
                .setName("likes")
                .setNodeB(node("cargo:goat")),
  new Relation().setNodeA(node("cargo:goat"))
                .setName("likes")
                .setNodeB(node("cargo:cabb"))
);

// Transition: load.
addTransition("load_(goat|wolf|cabb)", { String cargo ->
  if (node("ferry").getRelatedNodes(-1, "on").ofType("cargo").size() > 0) {
      fail("The ferry can only hold one cargo object.");
  }
  switchPlacementRelation(
    new Relation("on").setNodeA(node("cargo:" + cargo))
                      .setNodeB(node("ferry"))
                      .setPlacement(Placement.RANDOM).setRigid(true)
  );
});

// Transition: cross.
addTransition("cross", {
  switchPlacementRelation(
    node("ferry").getRelation(1, "moored_to")
      .clone()
      .setNextNodeB(nodes().ofType("bank"))
      .setNextPlacement(Placement.EDGE_RIGHT, Placement.EDGE_LEFT)
  );
});

// Transition: unload.
addTransition("unload", {
  for (Node cargo : node("ferry").getRelatedNodes(-1, "on").ofType("cargo")) {
    switchPlacementRelation(
      new Relation().setNodeA(cargo)
                    .setName("on")
                    .setNodeB(node("ferry").getRelatedNode(1, "moored_to"))
                    .setPlacement(Placement.RANDOM)
    );
  }
});