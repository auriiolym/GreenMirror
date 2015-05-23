// Ferryman model
initialize(1000, 600, 2000);

// background
addNode(new Node("bank:left").setAppearance(new Rectangle().withSize(300, 600).withPosition(0, 0).withFill("green")));
addNode(new Node("bank:right").setAppearance(new Rectangle().withSize(300, 600).withPosition(700, 0).withFill("green")));

// boat with ferryman
addNode(new Node("boat").setAppearance(new Rectangle().withSize(200, 50).withFill("brown")));
addNode(new Node("ferryman").setAppearance(new Circle().withRadius(20).withFill("black")));
node("boat").addRelation(new Relation("moored_to").setNodeB(node("bank:left")).setPlacement(Placement.EDGE_RIGHT_MIDDLE));
node("ferryman").addRelation(new Relation("on").setNodeB(node("boat")).setPlacement(Placement.MIDDLE).setRigid(true));
