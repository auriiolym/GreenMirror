// ConnectFour
initialize(600, 630);

// Create the board
addNodes(
    new GridBuilder("cf:cell_")
        .setCellCount(7, 6)
        .setCellSize(60, 60)
        .setCellArcs(10)
        .setCellFill("linear-gradient(to bottom, white 0%, #DBFFDB 80%, limegreen 100%)")
        .setCellSpacing(10)
        .setBorderSize(3, 20, 20, 20)
        .setBackgroundFill("linear-gradient(to bottom, #5252FF, #2626FF)")
        .setBackgroundArcs(8)
        .build(50, 160)
        .getNodes()
);

// Create the texts indicating whose turn it is and the players.
addNodes(
    new Node("turn").set(fx("text")
                            .setPosition(100, 40)
                            .setText("Has the turn:")
                            .setStyle("-fx-font-size: 13pt;")),
    new Node("next").set(fx("text")
                            .setPosition(100, 100)
                            .setText("Up next:")),
    new Node("player:1").set(fx("circle")
                            .setRadius(20)
                            .setFill("linear-gradient(to bottom, red, #FF4D4D)")),
    new Node("player:2").set(fx("circle")
                            .setRadius(20)
                            .setFill("linear-gradient(to bottom, #EBEB00, yellow)")),
);

// Relations
addRelations(
    new Relation("has").setNodeA(node("player:1"))
                       .setNodeB(node("turn"))
                       .setPlacement(new CustomPlacement(150, 10)),
    new Relation("is") .setNodeA(node("player:2"))
                       .setNodeB(node("next"))
                       .setPlacement(new CustomPlacement(150, 10)),
);


// Make a move.
addTransition("move(\\d+)", { Integer column ->

    // Get correct players.
    Relation turnRel = node("turn").getRelation(-1, "has");
    Relation nextRel = node("next").getRelation(-1, "is");
    Node turnPlayer = turnRel.getNodeA();
    Node nextPlayer = nextRel.getNodeA();
    
    // Get the correct cell.
    int cell = column - 7;
    for (int i = column; i < 6*7 && node("cf:cell_"+i).getRelation(-1, "inCell") == null; i += 7) {
        cell = i;
    }
    if (cell < 0) {
        fail("invalid move");
    }

    // Make the move.
    Node mark = turnPlayer.clone();
    Relation aboveColumn = new Relation("above_column")
                            .setNodeA(mark)
                            .setNodeB(node("cf:cell_" + column))
                            .setPlacement(Placement.EDGE_TOP);

    Relation inCell =      new Relation("inCell")
                            .setNodeA(mark)
                            .setNodeB(node("cf:cell_" + cell))
                            .setPlacement(Placement.MIDDLE);
    addNode(mark);
    addRelation(aboveColumn);
    flush();
    removeRelation(aboveColumn);
    addRelation(inCell);
    flush();
    
    // Switch turns.
    setAnimationDuration(400);
    switchPlacementRelation(
        turnRel.clone().setName("is").setNodeB(node("next"))
    );
    switchPlacementRelation(
        nextRel.clone().setName("has").setNodeB(node("turn"))
    );
});