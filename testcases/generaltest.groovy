// General test: initialize, add node, set appearance
initialize(800, 500, 2000);

Rectangle rect = new Rectangle().withSize(100, 100).withFill(Color.BLUE);

addNode(new Node("node1").setAppearance(rect.clone().withPosition(0, 0)));
addNode(new Node("node2").setAppearance(rect.clone().withPosition(110, 0)));
addNode(new Node("node3").setAppearance(new Circle().withCenterPosition(270, 50).withRadius(50).withFill(Color.YELLOW)));
addNode(new Node("rot:node4"));
node("node4").setAppearance(rect.clone().withPosition(330, 0));

node("node1").setType("first");

// Test the following: going to a next state when a Node doesn't have an appearance.
//addNode(new Node()); // Works!

addTransition('transition(\\d*)', 2000, 3000, { Integer i1 -> // document that only int, Integer or String parameter types are allowed.

    node("node2").getAppearance()
                 .adjustPosition(220, 110) // works
                 .adjustRotate(180)  // works
                 .adjustArcs(60, 60) // works
                 //.adjustFill("linear-gradient(to bottom, red, black)") // can't work (can't transition to gradient or anything other than a Color)
                 .adjustFill("red") // works
                ;
    addNode(new Node("rot:node5").setAppearance(rect.clone().withPosition(440, 0))); //works
    
    flushWithDelay(1000); // works
    //flush(); // works
    // This won't work. The transition is created if the old and new values differ. Because the 'old' value on the server only changes when the transition is executed, the following transition won't be created (the value on the server is still 0).
    // Solutions: 1. always create a transition (when the value is changed clientside), but only with an ending value (works!); 2. store the values on the server in a property map.
    node("node2").getAppearance().adjustRotate(0); // works
    node("node2").getAppearance().adjustArcs(0, 0); // jumps
    
    flush(); // works
    
    node("node2").getAppearance().adjustPosition(220, 0); // works
    node("node3").getAppearance().adjustOpacity(0.5);
    
    setAnimationDuration(1000);
    node("node5").setAppearance(new Rectangle().withX(110).withSize(100, 100).withFill("black").withArcs(80, 80));
    
    //nodes("rot:").setAppearance(rect.clone().withRotate(720)); // works (however, all other properties are reset)
    
    
});
