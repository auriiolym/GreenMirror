// The dining philosophers
initialize(1000, 700, false);

// Set duration for initialization.
setAnimationDuration(10);

// Amount of philosophers.
int amount = 4;

// Prototype philosopher.
final Node phil_prototype = new Node("phil:").set(fx("image")
                                                  .setImageFromFile("testcases/img/phil_thinking.png")
                                                  .setFitWidth(100)
                                                  .setPreserveRatio(true));

// Add table and the space around the table.
addNodes(
    new Node("at_table").set(fx("circle").setRadius(200).setPosition(500, 350).setFill(Color.BROWN).setOpacity(0.7)),
    new Node("around_table").set(fx("circle").setRadius(300).setPosition(500, 350).setOpacity(0.001)),
);

// Add philosophers and place them, and add forks.
for (int i = 0; i < amount; i++) {
    addNode(new Node("fork:" + i));
    
    double angle = i * 360 / amount;
    addNode(phil_prototype.clone().setName(String.valueOf(i)));
    addRelation(
        new Relation().setNodeA(node("phil:" + i))
                      .setName("thinking")
                      .setNodeB(node("around_table"))
                      .setPlacement(new EdgePlacement(angle))
    );
    node("phil:" + i).fx().setRotate(angle);
}





// Get fork.
addTransition("get-(left|right)-(\\d+)", { String side, int p ->
    Node phil = node("phil:" + p);
    Node fork = node("fork:" + (side.equals("right") ? (p + 3) % amount : p));
    
    // Test if fork is available.
    if (fork.getRelation(-1, "hasleft") != null || fork.getRelation(-1, "hasright") != null) {
        fail("fork " + fork.getName() + " is already in use");
    }
    // Test if philosopher hasn't already got a fork in the relevant hand.
    if (phil.getRelation(1, "has" + side) != null) {
        fail("philosopher " + p + " already has a fork in its " + side + " hand");
    }

    // Add relation with the fork.
    addRelation(
        new Relation().setNodeA(phil)
                      .setName("has" + side)
                      .setNodeB(fork)
    );
    // If both forks are now held, show the philosopher is eating.
    if (phil.getRelation(1, "hasright") != null && phil.getRelation(1, "hasleft") != null) {
        phil.fx().setImageFromFile("testcases/img/phil_eating.png");
        switchPlacementRelation(
            phil.getPlacementRelation().clone()
                                       .setName("eating")
        );
    
    // If just one fork is now held, show which one and that the philosopher is still hungry.
    } else {
        phil.fx().setImageFromFile("testcases/img/phil_hungry_" + side + ".png");
        switchPlacementRelation(
            phil.getPlacementRelation().clone()
                                       .setName("hungry")
        );
    }
});
// Release fork.
addTransition("release-(left|right)-(\\d+)", { String side, int p ->
    Node phil = node("phil:" + p);
    String otherSide = side.equals("left") ? "right" : "left";
    
    // Remove relation with fork.
    removeRelation(
        phil.getRelation(1, "has" + side)
    );
    
    // If the other fork is still being held, change image to the philosopher holding that fork.
    // Also, indicate he's still hungry.
    if (phil.getRelation(1, "has" + otherSide) != null) {
        phil.fx().setImageFromFile("testcases/img/phil_hungry_" + otherSide + ".png");
        switchPlacementRelation(
                phil.getPlacementRelation().clone()
                                           .setName("hungry")
        );
        
    // If no forks are being held anymore, revert to 'thinking' state, away from the table.
    } else {
        phil.fx().setImageFromFile("testcases/img/phil_thinking.png");
        switchPlacementRelation(
                phil.getPlacementRelation().clone()
                                           .setName("thinking")
                                           .setNodeB(node("around_table"))
        );
    }
});

// Get hungry (go to the table)
addTransition("go-hungry-(\\d+)", { int p ->
    Node phil = node("phil:" + p);
    // Check if the philosopher is in the right state.
    if (phil.getRelation(1, "thinking") == null) {
        fail("philosopher " + p + " wasn't thinking");
    }
    // Switch to "at the table".
    switchPlacementRelation(
            node("phil:" + p).getPlacementRelation().clone()
                                                    .setName("hungry")
                                                    .setNodeB(node("at_table"))
    );
});
addTransition("go-hungry-all", {
    // Loop through all philosophes that are in the 'thinking' state.
    for (Node phil : nodes("phil:").withRelation(1, "thinking")) {
        // Switch their placement relation (and thus state) to 'hungry'.
        switchPlacementRelation(
            phil.getPlacementRelation().clone()
                                       .setName("hungry")
                                       .setNodeB(node("at_table"))
        );
    }
});