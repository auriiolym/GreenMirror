initialize(1000, 500);


// Background
addNode(
    new Node("bank:left").fx()
                         .select("rectangle")
                         .setWidth(300)
                         .setHeight(600)
                         .setX(0)
                         .setY(0)
                         .setFill(Color.GREEN)
);
addNode(
    node("bank:left").clone()
            .setName("right").fx().setPosition(700, 0)
);

// Boat
addNodes(
    new Node("boat").fx("rectangle")
                    .setSize(150, 50)
                    .setFill(Color.BROWN),
    new Node("ferryman").fx()
                    .select("circle")
                    .setRadius(20)
                    .setFill(Color.BLACK)
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
Relation onRelation = new Relation("on")
                                .setNodeB(node("boat"))
                                .setPlacement(Placement.RANDOM);
addNodes(
    new Node("cargo:goat")
                    .addRelation(onRelation.clone())
                    .fx("rectangle")
                    .setSize(30, 20)
                    .setFill(Color.GRAY),
    new Node("cargo:wolf")
                    .addRelation(onRelation.clone())
                    .fx("rectangle")
                    .setSize(30, 25)
                    .setFill(Color.BLACK),
    new Node("cargo:cabb")
                    .addRelation(onRelation.clone())
                    .fx("rectangle")
                    .setSize(20, 20)
                    .setFill(Color.DARKGREEN)
);



addTransition("")





