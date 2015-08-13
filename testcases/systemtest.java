/////////////////
// This system test has two purposes: showing what the groovy script model initializer can do
// and what you can expect, and showing that the visualizations work properly.
//
// initializing with width = 1000px, height = 700px, default animation duration = 1000ms.
initialize(1000, 700, 1000);


// Default text node for explanation.
addNode(
    new Node("t").set(fx("text")
                      .setPosition(10, 10)
                      .setWrappingWidth(900)
                      .setText("System test 1. This test should be done with the model source "
                             + "file next to it: the visualizations are just a verification, "
                             + "not an explanation."))
);


/* This is the full list of possible transitions. Switch them however you want to see that the 
 * order it won't matter.
durationTest
transitionparameters:int=123;str=string_param
addNodesShowcase
setFxTest
generalNodePropertyTest
shapeNodePropertyTest
rectangleNodePropertyTest
imageNodePropertyTest
textNodePropertyTest
relationShowcase
placementRelationTest
rigidPlacementRelationTest
chainedRigidPlacementRelationTest
removeNodesTest
 */


// This will be executed before every other transition. This will be explained in the section
// about transition regex patterns and parameters.
addTransition(".*", 1, true, {
    // Remove all nodes except for the main text node.
    removeNodes(nodes().not(node("t")));
});

/******************************************************************************
 * Test: animation durations.
 *****************/
addTransition("durationTest", 5 * 1000, {
    
    // Default in this transition: as set while adding the transition: 5 seconds.
    node("t").fx().setText("This took 5 seconds.");
    flush();
    
    // Choose a near-zero duration for instantaneous animation, because zero results in the animation not being played.
    setAnimationDuration(1);
    node("t").fx().setText("Instantaneous!");
    flush();
    
    // Revert back to the default as set by the initializer: 1 second.
    setAnimationDuration(-1);
    node("t").fx().setText("This took 1 second.");
    flush();
    
    // Try negative duration: reverts back to the default as set by the initializer: 1 second.
    setAnimationDuration(-20 * 1000);
    node("t").fx().setText("This didn't took -20 seconds, but just 1.");
    flush();
    
});

/******************************************************************************
 * Test: transition regex patterns and their parameters.
 ******************/
/*// The following tansition could be added without problems.
addTransition("transitionparameters_int=(\\d+)", {});
//*/

/*// However, the following isn't possible because just one parameter is available.
  // Also, we can't catch the exception because the mistake will be noticed when the closure
  // gets executed (which is not during the following addTransition() line.
addTransition("transitionparameters_int=(\\d+)", { Integer i1, Integer i2 -> });
//*/

// The following works. Only integer and string parameters are allowed.
addTransition("transitionparameters:int=(\\d+);str=(\\w+)", { Integer i, String str ->

    node("t").fx().setText("The value of the integer parameter was: " + i
            + "\nAnd of the string parameter: " + str);
});
// The following transition will never be executed, because the regex pattern won't match with any
// transition found in the trace.
addTransition("transitionparameters:(.{1000,})", { throw new Exception(); });


/*// On the other hand: The following transition will be executed together with any other transition.
  // This is because the regex pattern matches all strings and GreenMirror executes all 
  // transitions that match a trace entry. GreenMirror traverses the available transitions
  // in the order of insertion, meaning the transition below will execute AFTER all transitions
  // added above this line, and BEFORE all transitions added below. This can be usefull for 
  // executing general code before or after a transition.  However, every transition
  // by definition leads to another state. If you want to execute code together with every other 
  // transition, this behaviour is unwanted. Therefore, use the addTransition(String, double, 
  // boolean, Closure) signature instead of the shorter version, with the third parameter
  // set to true, to make the "transition" be a supplement on other transitions.
addTransition(".*", 1, true, {});
//*/



/******************************************************************************
 * Show: ways to add nodes
 */
addTransition("addNodesShowcase", {
    
    node("t").fx().setText("This shows that all nodes end up in the visualizer correctly. There should be an "
            + "uninterrupted stream of circles present directly above this text, starting and ending with a red circle.");
    flush();
    
    // This way, the node gets added entirely and in one statement (although internally,
    // the node gets added to the visualizer and then the visualizer receives the visualization data.
    addNode(
        new Node().set(fx("circle")
                        .setRadius(5).setPosition(10, 10).setFill(Color.RED))
    );
    
    // This can also be done with multiple nodes.
    addNodes(
        new Node().set(fx("circle")
                        .setRadius(5).setPosition(20, 10)),
        new Node().set(fx("circle")
                        .setRadius(5).setPosition(30, 10))
    );
    
    // One can also add a node and subsequently alter its properties. For this, the reference to the node 
    // is needed. Note that the addNode(...) methods return the reference to the just added node.
    // A few examples:
    addNode("nodeName1")
        .fx("circle")
        .setRadius(5)
        .setPosition(40, 10);
    
    addNode(new Node("nodeName2"))
        .fx("circle")
        .setRadius(5)
        .setPosition(50, 10);
    
    Node n = new Node("nodeName3");
    addNode(n);
    n.fx("circle")
     .setRadius(5)
     .setPosition(60, 10);
    
    addNode("nodeName4");
    node("nodeName4").fx("circle").setRadius(5).setPosition(70, 10);
    
    // This will not work, because fx() and Node#fx() always return an FxWrapper instance (and its methods
    // return the same "this" instance.
    try {
        addNode(
            new Node().fx("circle").setRadius(5).setPosition(80, 10).setFill(Color.GREEN)
        );
        fail("passing an FxWrapper instance to the addNode(Nod) method didn't throw an exception");
    } catch (MissingMethodException e) {}
    
    
    // And show the node ending the "stream of circles" to make the visualization complete.
    addNode(new Node().set(fx("circle").setRadius(5).setPosition(80, 10).setFill(Color.RED)));
});


/******************************************************************************
 * Show: ways to set the node's FX
 */
addTransition("setFxTest", {
    
    node("t").fx().setText("This shows the possibilities and constraints on setting the node's FX."
            + "No visualizations are necessary.");
    flush();
    
    // Try setting a null FX.
    try {
        new Node().set(null);
        new Node().set(fx());
        fail("a null FX type was set");
    } catch (NullPointerException e) {}
    
    // Try setting an invalid FX type.
    try {
        new Node().set(fx("invalid fx type"));
        new Node().fx("invalid fx type");
        fail("an unknown FX type was set")
    } catch (IllegalArgumentException e) {}
    
    // Try getting the node's FX without it being set.
    try {
        new Node().fx();
        fail("nonexistent FX retrieved");
    } catch (IllegalStateException e) {}
    
    // Create a new node with a circle FX.
    Node n = new Node();
    n.fx("circle");
    
    // Test creating and retrieving a new, different FX type (whether it exists or not).
    try {
        n.fx("invalid fx type");
        n.fx("rectangle");
        fail("new fx created, even though the node already had one");
    } catch (IllegalArgumentException e) {}
    
    // Test re-setting the FX with a new instance, but of the same type. This works, but
    // completely replaces the previously set FX.
    n.set(fx("circle").setRadius(20));
    
    // The two ways of adding FX to a node (using node.fx("type") and node.set(fx("type"))) are
    // available because of what they return: the first one returns the FxWrapper instance,
    // the latter returns the Node instance.
});


/******************************************************************************
 * Test: properties that apply to all nodes
 */
addTransition("generalNodePropertyTest", {
    
    node("t").fx().setText("These animations work for every type of node and work exactly the same.");
    flush();
    
    addNodes(
        new Node("r").set(fx("rectangle")
                           .setSize(200, 100)),
        new Node("c").set(fx("circle")
                           .setRadius(30)
                           .setStyle("-fx-fill: red;")
                           .setPosition(100, 100))
    );
    flush();
    
    // The circle is now added with a fade in. The rectangle hasn't, yet, because it has no position.
    // Let's give it a position.
    node("r").fx().setPosition(100, 100);
    flush();
    
    // Now test the properties.
    
    // Rotate.
    node("r").fx().setRotate(90);
    flush();
    node("r").fx().setRotate(0);
    flush();
    node("r").fx().setRotate(-180);
    flush();
    node("r").fx().setRotateBy(90);
    flush();
    node("r").fx().setRotateBy(90); // Total: 0
    flush();
    node("r").fx().setRotate(0); // Nothing happens
    flush();
    node("r").fx().setRotate(360 * 10); // Rotate 10 times very fast.
    flush();
    
    // Opacity
    node("c").fx().setOpacity(0.1);
    flush();
    node("c").fx().setOpacity(0.5);
    flush();
    node("c").fx().setOpacity(1.0);
    flush();
    try {
        node("c").fx().setOpacity(-1);
        fail("setting of invalid opacity didn't throw an exception");
    } catch (IllegalArgumentException e) {}
    try {
        node("c").fx().setOpacity(2.0);
        fail("setting of invalid opacity didn't throw an exception");
    } catch (IllegalArgumentException e) {}
    
    
    // (CSS) style
    // This won't work. The client won't give an exception, although the server will. Check the log.
    // This is because the style property is not animatable, which is a problem when going from
    // state to state (although the fill property is animatable).
    // Future suggestions: one could animate it by using a fade out, then changing the style and
    // then using a fade in. This is also done with text and image nodes to animate the change
    // in their respective text and image properties. If one choses not to implement some kind of
    // animation, at least a warning could be given when changing the style if it has already
    // been added to the visualizer.
    node("c").fx().setStyle("-fx-fill: green");
    
    // The only way to set the style is to set the style during the initial setting of the FX. Examples:
    // This works:
    addNode(
        new Node().set(fx("circle")
                        .setRadius(5).setPosition(300, 40)
                        .setStyle("-fx-fill:blue"))
    );
    // As will this:
    addNode("name").set(fx("circle")
                        .setRadius(5).setPosition(300, 50)
                        .setStyle("-fx-fill:red"));
    // But these won't (check the server's log for the exceptions):
    addNode(new Node()).fx("circle")
                        .setRadius(5).setPosition(300, 60)
                        .setStyle("-fx-fill:orange");
    addNode("name").fx("circle")
                        .setRadius(5).setPosition(300, 70)
                        .setStyle("-fx-fill:purple");
    // This is because the Node#set(FxWrapper) method wraps the FX updates in one "set" command, while chaining
    // FX method results in one "set" command adding the node to the visualizer, and multiple "change" commands
    // changing the visual properties.
    // Non-animatable properties can not be changed after the FX has been added to the visualizer.
});


/******************************************************************************
 * Test: properties that apply to javafx.scene.shape.Shape nodes
 */
addTransition("shapeNodePropertyTest", {
    
    node("t").fx().setText("These animations only work for shape nodes. In GreenMirror this means any "
            + "FxWrapper extension that is a subclass of FxShapeWrapper.");
    flush();
    
    addNode(
        new Node("r").set(fx("rectangle")
                          .setSize(400, 300)
                          .setPosition(200, 200))
    );
    flush();
    
    // The last one wins, although it won't be a nice transition: the starting value is wrong.
    node("r").fx().setFill(Color.GREEN);
    node("r").fx().setFill(Color.RED);
    node("r").fx().setFill(Color.YELLOW);
    flush();
    
    // Succesful transition:
    node("r").fx().setFill(Color.GREEN);
    flush();
    
    // An impossible one: JavaFX can't animate into a gradient.
    // See your serverside logs for the "Animating of JavaFX node property (...) failed" message.
    // It's not a fatal exception, so GreenMirror continues with nothing more than a log entry. The fill is
    // still green.
    node("r").fx().setFill("linear-gradient(white, black)");
    flush();
    
    // Another impossible one, or rather an invalid one.
    try {
        node("r").fx().setFill("invalid fill value");
        fail("setting an invalid fill value didn't throw an exception");
    } catch (IllegalArgumentException e) {}
    flush();
});


/******************************************************************************
 * Test: properties that apply to javafx.scene.shape.Rectangle nodes
 * 
 * Note: the circle's radius property works the same as the rectangle's width
 *       and height properties, so there would be no point in testing it 
 *       separately.
 */
addTransition("rectangleNodePropertyTest", 2000, {
    
    node("t").fx().setText("This tests the supported properties specifically of a rectangle");
    flush();
    
    // Add it first.
    addNode(
        new Node("r").set(fx("rectangle")
                         .setSize(400, 200)
                         .setPosition(200, 200)
                         .setFill("linear-gradient(to right, limegreen, darkgreen)"))
    );
    RectangleFxWrapper fx = node("r").fx();
    flush();

    // x property (y works the same)
    // x: other positive value
    fx.setX(100);
    flush();
    // x: explicit double value
    fx.setX(0.5);
    flush();
    // x: zero value
    fx.setX(0);
    flush();
    // x: negative value
    fx.setX(-50);
    flush();
    // x: original value
    fx.setX(200);
    flush();
    
    // Width property (height works the same)
    // width: positive value
    fx.setWidth(200);
    flush();
    // width: zero value
    fx.setWidth(0);
    flush();
    // width: negative value. JavaFX sees this as a zero value.
    fx.setWidth(-50);
    flush();
    // width: original
    fx.setWidth(400);
    flush();
    
    // Arc width and height properties (both work the same)
    // arcs: positive, small value 
    fx.setArcs(20);
    flush();
    // arcs: positive, larger value
    fx.setArcs(200);
    flush();
    // arcs: positive, very large value. This turns it into an ellipse.
    fx.setArcs(800);
    flush();
    // arcs: negative, small value. JavaFX sees this as a zero value.
    fx.setArcs(-20);
    flush();
});



/******************************************************************************
 * Test: properties that apply to javafx.scene.image.ImageView nodes
 */
addTransition("imageNodePropertyTest", 2000, {
    
    node("t").fx().setText("This tests the supported properties of images");
    flush();
    
    // First the image.
    // Try to add an image from an invalid url.
    try {
        new Node().set(fx("image").setImageFromUrl("http://invalid url"));
        fail("loading an image from an invalid url didn't throw an exception");
    } catch (IllegalArgumentException e) {}

    /*// JavaFX doesn't throw an exception if the request doesn't return a valid image, it just tries
      // to set the http response data as the image. The following line would print the utwente.nl
      // main page's html source to the log.
    Log.add(new String(fx("image").setImageFromUrl("http://www.utwente.nl/").getImage().getBytes()));
    //*/
    
    // Now a succesful add from an url.
    addNode(
        new Node("img1").set(fx("image")
                             .setImageFromUrl("http://www.utwente.nl/repository/utwente/ws2013/img/nl/inv-utlogo.png")
                             .setPosition(10, 30)
                             .setFitWidth(260))
    );
    flush();
    
    // Try to add an image from an invalid file path.
    try {
        fx("image").setImageFromFile("invalid file");
        fail("loading an image from an invalid file path didn't throw an exception");
    } catch (IllegalArgumentException e) {}
    
    // Again, JavaFX won't throw an exception, but just silently continues.
    fx("image").setImageFromFile("testcases/systemtest1.java");
    
    // Now the succesful add. One with preserveRatio=true and one with preserveratio=false will be added.
    // You can see in the visualization that both the fitWidth and the fitHeight are applied with the
    // first image. This is due to the fact that preserveRatio is set to false.
    // On the second image, the smallest value of the two gets applied while honoring the preserveRatio
    // setting.
    addNodes(
        new Node("img2").set(fx("image")
                            .setImageFromFile("testcases/img/wolf.png")
                            .setPosition(300, 30)
                            .setFitWidth(200)
                            .setFitHeight(50)
                            .setPreserveRatio(false)),
        new Node("img3").set(fx("image")
                            .setImageFromFile("testcases/img/wolf.png")
                            .setPosition(550, 30)
                            .setFitHeight(200)
                            .setFitWidth(50)
                            .setPreserveRatio(true)),
        new Node("img4").set(fx("image")
                            .setImageFromFile("testcases/img/wolf.png")
                            .setPosition(700, 30))
     );
     flush();
     
     
     // Change the fitWidth property of images with different preserveRatio values.
     node("img2").fx().setFitWidth(100);
     node("img3").fx().setFitWidth(100);
     flush();
     
     // And the fitHeight. This works fine.
     node("img2").fx().setFitHeight(300);
     node("img3").fx().setFitHeight(300);
     flush();
     
     // However, when the fitWidth or fitHeight property weren't initially set, they start at a
     // zero value.
     node("img4").fx().setFitWidth(219); // This is the original width.
     flush();
     
     // Setting either of these two values to zero or a negative value works the same as the width
     // and height properties of a rectangle. As can be seen, the dependence of these values upon
     // each other is present. Therefore, it is recommended to always set the fitWidth or fitHeight,
     // whichever one wants to alter later.
     
     // Changing the image property.
     node("img1").fx().setImageFromFile("testcases/img/goat.png");
    
});



/******************************************************************************
 * Test: properties that apply to javafx.scene.text.Text nodes
 */
addTransition("textNodePropertyTest", 2000, {
    
    node("t").fx().setText("This tests the supported properties of texts");
    flush();
    
    // Add sample text.
    addNode(new Node("txt").set(fx("text").setText("Lorem ipsum dolor sit amet, consectetur adipiscing elit. Ut lobortis ornare tincidunt. Fusce fringilla ligula quis quam vulputate tempus. Phasellus lobortis nunc sit amet leo malesuada iaculis ac vitae est. Donec vitae pulvinar arcu, cursus euismod lacus. Cras sit amet semper nisl. Integer eget finibus nunc. Integer placerat arcu id congue accumsan. Curabitur quis justo ipsum. Sed auctor arcu eu purus accumsan, eu scelerisque risus varius. Quisque ut ipsum in mi ullamcorper mollis quis a massa. In consectetur urna quis leo faucibus bibendum. Integer sit amet feugiat nisl. Nullam a orci eget mauris finibus luctus. Fusce tempor elit eros, eget pulvinar risus eleifend quis. Cras in libero sed lorem ullamcorper aliquet ut at lacus. Aliquam molestie leo sed elit dictum, non luctus purus blandit.\n\nNulla faucibus rutrum dui nec hendrerit. Nam auctor interdum vestibulum. Aenean commodo nisi vitae leo imperdiet, id finibus lectus pharetra. Sed molestie arcu a ante rutrum fermentum. Donec at arcu vehicula, aliquet nulla nec, venenatis odio. Mauris eu magna molestie, laoreet erat a, mollis est. Ut non justo ac ante ornare egestas. Nullam vestibulum libero in leo accumsan, quis egestas tellus vestibulum. Praesent convallis augue id lorem sollicitudin euismod. Morbi quis lectus eu augue tincidunt porttitor. Donec sit amet est egestas, efficitur mauris non, placerat magna. Aliquam quis enim sed lorem dictum bibendum vitae id risus. Aenean sed purus dictum, sagittis felis sed, malesuada lacus. Nulla ornare dictum libero, in sollicitudin turpis vestibulum non.\n\nNulla aliquam vitae dui a dignissim. Sed sollicitudin tellus ut justo cursus sagittis. Cras consectetur fermentum aliquet. Sed sit amet finibus nunc. In sem neque, maximus a gravida eu, tempus ut mi. Cras sit amet blandit nisl. Pellentesque pretium quis nisi vel viverra. Suspendisse aliquam dolor sit amet vulputate blandit. Praesent elementum, est vel efficitur tempus, arcu est aliquet sapien, vel egestas tellus magna at urna. Aenean placerat egestas nunc in imperdiet.\n\nCurabitur finibus sem ut aliquet posuere. Nunc mauris libero, tincidunt a tortor sit amet, venenatis ullamcorper eros. Nullam at elit pellentesque, dictum ex vel, sodales urna. Curabitur eget velit magna. Duis viverra urna porta dignissim auctor. Mauris tincidunt lectus a faucibus consequat. Proin eget ornare ante. Pellentesque sed ultrices nunc, ut varius libero. Integer sit amet orci mauris. Vestibulum congue urna quis ullamcorper tempor. Praesent tincidunt orci ac ante dictum rhoncus. Suspendisse sed lorem nisi. Sed tincidunt dolor ut libero laoreet, sed viverra nisl congue. Vestibulum ante ipsum primis in.")
                                          .setPosition(10, 30).setFill(Color.GREEN)));
    flush();
    
    // Wrapping width.
    node("txt").fx().setWrappingWidth(900);
    flush(1000);
    
    // As is seen in the visualization, the wrapping width should always be set when dealing
    // with large pieces of text.
    node("txt").fx().setWrappingWidth(800);
    flush();
    
    // As can be seen from setting the wrappingWidth to zero, this results in no wrapping at all.
    // The same goes for a negative value.
    node("txt").fx().setWrappingWidth(0);
    flush();
    node("txt").fx().setWrappingWidth(-200);
    flush();
    
    // Text property.
    node("txt").fx().setText("This is newly set text.");
    
});


/******************************************************************************
 * Test: different way of adding and removing relations
 * Note: this doesn't actually have to happen in a state-transition, because 
 *       nothing in the visualizer has to change.
 */
addTransition("relationShowcase", 2000, {
    
    node("t").fx().setText("This shows how to add and remove relations.");

    // Adding relations.
    addNodes(
        new Node("female"),
        new Node("male1"),
        new Node("male2"),
    );
    
    // Add relation, method 1: add one relation to the controller.
    addRelation(
        new Relation("likes").setNodeA(node("male1"))
                             .setNodeB(node("female"))
    );
    
    // Add relation, method 2: add multiple relations to the controller.
    addRelations(
        new Relation().setNodeA(node("male2"))
                      .setName("also likes")
                      .setNodeB(node("female")),
        new Relation().setNodeA(node("male2"))
                      .setName("envies")
                      .setNodeB(node("male1"))
    );
    
    // Add relation, method 3: add relation simultaneously when adding the node.
    addNode(
        new Node("male0").addRelation(
                            new Relation("loves").setNodeB(node("female")))
    );
    
    // Now do the check:
    if (node("female").getRelatedNode(-1, "likes") != node("male1")
     || node("female").getRelatedNode(-1, "also likes") != node("male2")
     || node("female").getRelatedNode(-1, "loves") != node("male0")
     || node("male2") .getRelatedNode( 1, "envies") != node("male1")) {
        fail("adding relations failed");
    }
    
    // And check the same using different methods.
    if ( node("male0").getRelatedNodes(1, "loves").size() != 1
     ||  node("male0").getRelatedNodes(1).size() != 1
     || !node("male0").getRelatedNodes().contains(node("female"))
     || !node("male0").hasRelationWith(node("female"))
     || !node("male0").hasRelationWith(nodes("female"))
     || !node("male0").hasRelation(node("female").getRelation(-1, "loves"))) {
        fail("adding relations failed");
    }
    
    // Add a relation in which one of the nodes is null.
    try {
        addRelation(new Relation().setNodeA(node("female")));
        fail("relation added with just one node");
    } catch (IllegalArgumentException e) {}
    
    // Add a relation with a node that isn't added to the controller.
    try {
        addRelation(new Relation().setNodeA(node("female")).setNodeB(new Node()));
        fail("relation with unknown node added")
    } catch (IllegalArgumentException e) {}
    // Which might happen in this scenario (because node n1 isn't added yet):
    try {
        addNodes(
            new Node("n1"),
            new Node("n2").addRelation(new Relation("hates").setNodeB(node("n1")))
        );
        fail("relation with unknown node added")
    } catch (IllegalArgumentException e) {}
    
    
    // Remove relation.
    removeRelation(
        node("male2").getRelation(1, "envies")
    );
    if (node("male2").getRelatedNode(1, "envies") != null) {
        fail("relation not removed");
    }
    
    // Remove multiple relations.
    removeRelations(
        node("female").getRelations()
    );
    if (node("male0").getRelation(1, "loves") != null) {
        fail("relation not removed");
    }
    
    // Relation#removeFromNodes() and Node#getRelations().removeAll() can be used, but will only 
    // remove the relations at the client, not on the server. This is because these changes in the
    // relations won't be passed on to the controller.
    
    // Show how a temporary FX's can be applied and removed.
    addNodes(
        new Node("c:1").set(fx("circle").setRadius(30).setPosition(100, 100).setFill(Color.RED)),
        new Node("c:2").set(fx("circle").setRadius(50).setPosition(200, 100).setFill(Color.BLUE))
    );
    flush();
    addRelation(
        new Relation("on").setNodeA(node("c:2")).setNodeB(node("c:1"))
                          .setPlacement(Placement.MIDDLE)
                          .setTemporaryFxOfNodeA(node("c:2").fx().clone().setRadius(10))
    );
    flush();
    removeRelation(node("c:1").getRelations().get(0));
    // As you can see, after removal of the relation, the location of node A remains the same.
    
});



/******************************************************************************
 * Test: adding placement relations (only one simultaneous placement relation is possible)
 */
addTransition("placementRelationTest", 2000, {
    
    node("t").fx().setText("This tests adding placement relations. ");
    flush();
    
    // Add two base nodes and a node that will be placed.
    addNodes(
        new Node("b1").set(fx("rectangle")
                            .setPosition(30, 50)
                            .setSize(200, 100)
                            .setFill("linear-gradient(to right, green, black)")),
        new Node("b2").set(fx("rectangle")
                            .setPosition(260, 50)
                            .setSize(200, 100)
                            .setFill("linear-gradient(to left, green, black)")),
        new Node("c").set(fx("circle")
                            .setRadius(10)
                            .setFill(Color.RED))
    );
    flush();
    
    // Show node c on the visualizer in the middle of node b1.
    addRelation(
        new Relation("on").setNodeA(node("c"))
                          .setNodeB(node("b1"))
                          .setPlacement(Placement.MIDDLE)
    );
    flush();
    
    // Move node c to the middle of node b2.
    addRelation(
        new Relation("on").setNodeA(node("c"))
                          .setNodeB(node("b2"))
                          .setPlacement(Placement.MIDDLE)
    );
    flush();
    
    // Verify that the first placement relation has been replaced with the second.
    if (node("c").getRelations().withPlacement().size() > 1) {
        fail("node has more than one placement relations");
    }
    if (node("c").getRelatedNode(1, "on") != node("b2")) {
        fail("node has the wrong placement relation");
    }
    
    // The above can also be done in a more explicit way.
    switchPlacementRelation(
        node("c").getRelation(1, "on").clone()
                                      .setPlacement(Placement.EDGE_BOTTOM)
    );
    if (node("c").getRelations().size() != 1 || node("b2").getRelations().size() != 1
     || node("c").getRelations().get(0) != node("b2").getRelations().get(0)
     || !node("c").getRelations().get(0).getName().equals("on")
     || !node("c").getRelations().get(0).getPlacement().equals(Placement.EDGE_BOTTOM)
     || !node("c").hasPlacementRelation()
     || node("c").getRelations().get(0) != node("c").getPlacementRelation()) {
        fail("switching placement relations went wrong");
    }
    
    // And add a non-placement relation.
    addRelation(
        new Relation().setNodeA(node("c"))
                      .setName("wants to be on")
                      .setNodeB(node("b2"))
    );
    if (node("c").getRelations().size() != 2 
     || !node("c").getRelation(1, "wants to be on").getPlacement().equals(Placement.NONE)
     || node("c").getRelation(1, "on") != node("c").getPlacementRelation()) {
        sendStateToLog();
        fail("adding regular relation went wrong");
    }
});

/******************************************************************************
 * Test: rigid placement relations
 */
addTransition("rigidPlacementRelationTest", 2000, {
    
    node("t").fx().setText("This tests adding rigid placement relations and verifies that "
            + "specific placements work. ");
    flush();
    

    addNodes(
        new Node("b:1").set(fx("rectangle")
                            .setPosition(30, 100)
                            .setSize(200, 300)
                            .setFill("linear-gradient(to bottom, white, gray)")
                            .setArcs(10)),
        new Node("b:2").set(fx("circle")
                            .setPosition(340, 220)
                            .setRadius(60)
                            .setFill("linear-gradient(to bottom, white, gray)")),
        new Node("b:3").set(fx("image")
                            .setPosition(450, 210)
                            .setImageFromFile("testcases/img/UT_Logo_White_NL_2.png")),
        new Node("b:4").set(fx("text")
                .setPosition(800, 215)
                .setText("text node")
                .setStyle("-fx-fill: green; -fx-font-size: 16pt; -fx-font-weight: bold;")),
        new Node("b:5").set(fx("text")
                .setPosition(800, 415)
                .setText("text node")
                .setStyle("-fx-fill: green; -fx-font-size: 16pt; -fx-font-weight: bold;"))
    );
    flush();
    
    // Test all placements.
    // Create the prototype node.
    Node prototypeNode = new Node("c:pl").set(fx("circle")
                                              .setRadius(10)
                                              .setFill("linear-gradient(to bottom, darkgreen, limegreen)"));
    // Create the testable placements.
    Placement[] testPlacements = [Placement.MIDDLE, 
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
    // Place nodes on all base nodes.
    for (Node baseNode : nodes("b:")) {
        for (int i = 0; i < testPlacements.length; i++) {
            Placement placement = testPlacements[i].clone();
            Node theNode = prototypeNode.clone();
            theNode.fx().setPosition(400, -200);
            if (placement instanceof RandomPlacement) {
                theNode.fx().setFill("linear-gradient(to bottom, red, #FF7A7A)");
            }
            if (placement instanceof EdgePlacement) {
                theNode.fx().setFill("linear-gradient(to bottom, blue, #7373FF)");
            }
            if (placement instanceof CustomPlacement) {
                theNode.fx().setFill(Color.BLACK);
            }
            addNode(theNode);
            addRelation(
                new Relation("on").setNodeA(theNode)
                                  .setNodeB(baseNode)
                                  .setPlacement(placement)
                                  .setRigid(true)
            );
        }
        flush();
    }
    
    // Do a small translation and rotation of all base nodes and thus also the rigidly related nodes.
    for (Node baseNode : nodes("b:")) {
        baseNode.fx().setRotate(20);
        baseNode.fx().setY(baseNode.fx().getY() + 50);
    }
    flush();
    for (Node baseNode : nodes("b:")) {
        baseNode.fx().setRotate(0);
        baseNode.fx().setY(baseNode.fx().getY() - 50);
    }
    
    // As is clearly seen on the visualizer, a text node has no pre-defined height, so a height value of 0 is assumed.
    // Also, the width is only taken into account if the wrapping width is set.
    
});

/******************************************************************************
 * Test: chained rigid placement relations
 */
addTransition("chainedRigidPlacementRelationTest", 2000, {
    
    node("t").fx().setText("This tests chaining rigid placement relations.");
    flush();
    
    Placement[] pl = [new CornerBottomRightPlacement().withRelativePosition(25, 25),
                      new CornerTopRightPlacement()];

    addNodes(
        new Node("b:r1").set(fx("rectangle")
                            .setPosition(200, 200)
                            .setSize(200, 100)),
        new Node("b:c1").set(fx("circle")
                            .setRadius(50)
                            .setFill(Color.RED)
                            .setOpacity(0.5)),
        new Node("r2").set(fx("rectangle")
                            .setSize(100, 50)
                            .setFill(Color.YELLOW))
    );
    
    addRelations(
        new Relation().setNodeA(node("c1"))
                      .setName("on")
                      .setNodeB(node("r1"))
                      .setPlacement(pl[0])
                      .setRigid(true),
        new Relation().setNodeA(node("r2"))
                      .setName("on")
                      .setNodeB(node("c1"))
                      .setPlacement(new MiddlePlacement().withRelativePosition(75, 50))
                      .setRigid(true)
    );
    flush();
    
    // Test moving the first node in the chain.
    node("r1").fx().setX(node("r1").fx().getX() + 50);
    flush();
    
    // Test rotation the first node in the chain.
    node("r1").fx().setRotateBy(45);
    flush();
    
    // Test moving the second node in the chain.
    // What happens here: the FX of node c1 are sent to the server with x value 200.
    // This also means its original rotation of 0 is sent to the server, so node c1
    // and the chained node r2 are rotated and moved.
    node("c1").fx().setX(200);
    flush();
    
    // Now node r1 gets moved back to x value 200 and its FX gets applied (server side)
    // to all chained nodes (i.e. nodes c1 and r2). 
    node("r1").fx().setX(node("r1").fx().getX() - 50);
    flush();
    
    
    // Test switching placement to next in line.
    for (int i = 0; i < pl.length; i++) {
        switchPlacementRelation(
            node("c1").getRelation(1, "on").clone()
                                           .setNextPlacement(pl)
        );
        flush();
    }
    
    // Test switching node B of relation to next node B in line (with a node A 
    // it works exactly the same).
    for (int i = 0; i < nodes("b:").size(); i++) {
        switchPlacementRelation(
            node("r2").getRelation(1, "on").clone()
                                           .setNextNodeB(nodes("b:"))
        );
        flush();
    }
});

/******************************************************************************
 * Test: removing nodes
 */
addTransition("removeNodesTest", 2000, {
    
    node("t").fx().setText("This tests removing nodes.");
    flush();
    
    Node prototypeCircle = new Node("c:").set(fx("circle").setRadius(20).setFill(Color.BLUE));
    
    addNodes(
        new Node("r").set(fx("rectangle")
                            .setPosition(200, 200)
                            .setSize(200, 100)
                            .setFill(Color.RED)),
        prototypeCircle.setName("1").clone(),
        prototypeCircle.setName("2").clone()
    );
    addRelations(
        new Relation().setNodeA(nodes("c:1")).setName("on").setNodeB(node("r"))
                      .setPlacement(Placement.CORNER_TOP_LEFT),
        new Relation().setNodeA(nodes("c:2")).setName("on").setNodeB(node("r"))
                      .setPlacement(Placement.CORNER_TOP_RIGHT)
    );
    flush();
    
    // Save reference for later.
    Node nodec1 = node("c:1");
    
    // Remove circles.
    removeNodes(nodes("c:"));
    
    // Verify node and relation inexistence.
    if (nodes("c:").size() != 0
     || node("r").getRelations().size() != 0) {
        sendStateToLog();
        fail("removing nodes didn't work properly");
    }
    
    // Node doens't exist anymore, so an IllegalArgumentException will be thrown.
    try {
        node("c:1");
        fail("node c:1 wasn't removed");
    } catch (IllegalArgumentException e) {}
    
    // Try removing again. Nothing happens.
    removeNodes(nodec1);
    
    // Try to create a relation with a removed node.
    try {
        addRelation(new Relation().setNodeB(node("r")).setNodeA(nodec1));
        fail("node c:1 wasn't removed from the controller");
    } catch (IllegalArgumentException e) {}
});