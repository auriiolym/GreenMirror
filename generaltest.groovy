// General test: initialize, add node, set appearance
initialize(800, 500, 3000);

Rectangle rect = new Rectangle().withSize(100, 100);

addNode(new Node("node1").setAppearance(rect.clone().withPosition(0, 0)));
addNode(new Node("node2").setAppearance(rect.clone().withPosition(110, 0)));
addNode(new Node("node3").setAppearance(rect.clone().withPosition(220, 0)));
addNode(new Node("node4").setAppearance(rect.clone().withPosition(330, 0)));

//node("node3").setType("rotationtype");
//node("node4").setType("rotationtype");

// Test the following: going to a next state when a Node doesn't have an appearance.
addNode(new Node());

addTransition('transition1', 4000, 6000, {

    node("node2").getAppearance()
                 .adjustX(220)
                 .adjustY(110)
                 .adjustRotate(90)
                 .adjustArcs(60, 60)
                ;
    addNode(new Node("node5").setAppearance(rect.clone().withPosition(440, 0)));
    
    //flushWithDelay(2000);
    flush();
    node("node2").getAppearance().adjustRotate(0);
    
    //addNode(new Node("node6").setAppearance(rect.clone().withPosition(500, 500)));
    //setAnimationDuration(5000)
    
    //nodes("rotationtype:").setAppearance(rect.clone().withRotate(720));
    
    
});
