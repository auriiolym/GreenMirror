initialize(800, 500, true);

// Description text
addNode(
    new Node("t").set(fx("text")
                     .setText("Hello! This is a showcase of what GreenMirror can do.")
                     .setPosition(10, 10)
                     .setWrappingWidth(750))
);



// Showcase 1: node types
addTransition("transition1", 4000, {
    
    setAnimationDuration(500);
    removeNodes(nodes("c:"));
    node("t").fx().setText("Showcase 1: creating different types of nodes and moving them across the canvas.");
    setAnimationDuration(-1);
    flush(1000);
    
    // Rectangle
    addNodes(
        new Node("c:").set(fx("text").setPosition(10, 40).setText("Rectangle: fill=gradient, width=40, height=10, arcWidth=5, arcHeight=5, rotate=5degr, opacity=0.5")),
        new Node("c:o").set(fx("rectangle")
                            .setPosition(10, 70)
                            .setSize(40, 10)
                            .setRotate(5)
                            .setOpacity(0.5)
                            .setFill("linear-gradient(to right, red, black)")
                            .setArcs(5, 5))
    );
    
    flush();
    // Circle
    addNodes(
        new Node("c:").set(fx("text").setPosition(10, 100).setText("Circle: fill=gradient, radius=30, rotate=-45degr, opacity=0.9")),
        new Node("c:o").set(fx("circle")
                            .setPosition(40, 150)
                            .setRadius(30)
                            .setRotate(-45)
                            .setOpacity(0.9)
                            .setFill("linear-gradient(to right, red, limegreen)"))
    );
    
    flush();
    // Image from url
    addNodes(
        new Node("c:").set(fx("text").setPosition(10, 200).setText("Image: png from URL, original size=278x32px, fit height=60px, preserveRatio=true (defaults to false)")),
        new Node("c:o").set(fx("image")
                            .setPosition(10, 200)
                            .setFitHeight(60)
                            .setPreserveRatio(true)
                            .setImageFromUrl("https://blackboard.utwente.nl/branding/_1_1/UT_Logo_White_NL_2.png"))
    );
    
    flush();
    // Image from file
    addNodes(
        new Node("c:").set(fx("text").setPosition(10, 260).setText("Image: gif from file, no width or height altered")),
        new Node("c:o").set(fx("image")
                            .setPosition(10, 280)
                            .setImageFromFile("testcases/utlogo.229x19.gif"))
    );
    
    flush();
    // Text
    addNodes(
        new Node("c:o").set(fx("text")
                            .setPosition(10, 310)
                            .setText("As you already have seen, text is also supported. Up until now, only the color and CSS styling is supported to style the text (which is also supported on all other JavaFX nodes). You can also set the wrapping width of the text, which in this text is set to 600px.")
                            .setFill(Color.DARKGREEN)
                            .setStyle("-fx-font-size: 15pt;")
                            .setWrappingWidth(600))
    );
    
    flush()
    // Moving nodes
    for (Node node : nodes().ofType("c").withName("o")) {
        node.fx().setX(node.fx().getX() + 40);
    }
    
});


// Showcase 2: relations
addTransition("transition2", 2000, {

    // Clear screen and change the description text.
    setAnimationDuration(500);
    removeNodes(nodes("c:"));
    node("t").fx().setText("Showcase 2: placement relations on different types of nodes.\nThe green nodes are set on a pre-defined placement, the red ones on a random spot on their related nodes, and the blue ones at -10 and 10 degree angles.");
    setAnimationDuration(-1);
    flush(1000);
    
    

    // Base nodes.
    addNodes(
        new Node("c:b").set(fx("rectangle")
                            .setSize(200, 300)
                            .setPosition(30, 100)
                            .setFill("linear-gradient(to bottom, white, gray)")
                            .setArcs(10)),
        new Node("c:b").set(fx("circle")
                            .setRadius(60)
                            .setPosition(340, 220)
                            .setFill("linear-gradient(to bottom, white, gray)")),
        new Node("c:b").set(fx("image")
                            .setPosition(450, 230)
                            .setImageFromFile("testcases/UT_Logo_White_NL_2.png"))
    );
    flush();
    
    // Create the prototype node and the placements array.
    Node prototypeNode = new Node("c:pl").set(fx("circle")
                                              .setRadius(10)
                                              .setFill(Color.GREEN));
    Placement[] placements = [Placement.MIDDLE, 
                              Placement.RANDOM, 
                              new EdgePlacement(-10), 
                              new EdgePlacement(10), 
                              new CustomPlacement(-30, 0), 
                              Placement.EDGE_TOP, 
                              Placement.EDGE_RIGHT, 
                              Placement.EDGE_BOTTOM, 
                              Placement.EDGE_LEFT, 
                              Placement.CORNER_TOP_LEFT, 
                              Placement.CORNER_TOP_RIGHT, 
                              Placement.CORNER_BOTTOM_RIGHT, 
                              Placement.CORNER_BOTTOM_LEFT];
    
    // Place them on all base nodes.
    for (Node baseNode : nodes("c:b")) {
        for (int i = 0; i < placements.length; i++) {
            Placement placement = placements[i].clone();
            Node theNode = prototypeNode.clone();
            theNode.fx().setPosition(400, -200);
            addNode(theNode);
            if (placement instanceof RandomPlacement) {
                theNode.fx().setFill(Color.RED);
            }
            if (placement instanceof EdgePlacement) {
                theNode.fx().setFill(Color.BLUE);
            }
            if (placement instanceof CustomPlacement) {
                theNode.fx().setFill(Color.BLACK);
            }
            addRelation(
                new Relation("on").setNodeA(theNode)
                                  .setNodeB(baseNode)
                                  .setPlacement(placement)
                                  .setRigid(true)
            );
        }
        flush();
    }
    
    // Do a small translation and rotation.
    for (Node baseNode : nodes("c:b")) {
        baseNode.fx().setRotate(20);
        baseNode.fx().setY(baseNode.fx().getY() + 50);
    }
    flush();
    for (Node baseNode : nodes("c:b")) {
        baseNode.fx().setRotate(0);
        baseNode.fx().setY(baseNode.fx().getY() - 50);
    }
});


/*
// Showcase 3: GridBuilder
addTransition("transition3_(\d+)", {Integer i ->

});
*/
