initialize(800, 500);


// Board
addNodes(
    new GridBuilder("tictactoeGrid")
        .setCellCount(3, 3)
        .setCellSize(100, 100)
        .setCellSpacing(10)
        .setBorderSize(30)
        .setBackgroundFill(Color.RED)
        .setCellFill("linear-gradient(to bottom, red 0%, blue 20%, blue 100%)")
        .setBackgroundArcs(50)
        .setCellArcs(20)
        .build(80, 20)
        .getNodes()
);


// Node that determines the turn
addNode(new Node("turn"));

// Players
addNodes(
    new Node("player:1").set(fx("rectangle")
                        .setSize(30, 30)
                        .setFill(Color.BROWN)
                        .setArcs(30)
                        .setPosition(30, 200)).addLabel("turn")
                        .addRelation(new Relation("has")
                                        .setNodeB(node("turn"))),
    new Node("player:2").set(fx("rectangle")
                        .setSize(30, 30)
                        .setFill(Color.YELLOW)
                        .setArcs(30)
                        .setPosition(500, 200))
);

/*
addTransition("move(\\d+)", 1000, { int cell ->
    Node currentPlayer = nodes("player:").withLabel("turn").getFirst();
    Node otherPlayer = nodes("player:").getCircularNext(currentPlayer);
    
    Node newNode = currentPlayer.clone().setType("mark");
    addNode(newNode);
    
    flush();
    
    addRelation(
        new Relation("on").setNodeA(newNode)
                          .setNodeB(node("tictactoeGrid:" + cell))
                          .setPlacement(Placement.MIDDLE)
    );
    
    currentPlayer.removeLabel("turn");
    otherPlayer.addLabel("turn");
});
*/

addTransition("move(\\d+)", 1000, {int cell -> 
    Relation turnRelation = node("turn").getRelation(-1, "has");
    Node currentPlayer = turnRelation.getNodeA();
    Node otherPlayer = nodes("player:").getCircularNext(currentPlayer);
    
    Node newNode = currentPlayer.clone().setType("mark");
    addNode(newNode);
    
    flush();
    
    addRelations(
        new Relation("on").setNodeA(newNode)
                          .setNodeB(node("tictactoeGrid:" + cell))
                          .setPlacement(Placement.MIDDLE),
        turnRelation.clone().setNodeA(otherPlayer)
    );
    
    turnRelation.remove();
    
});