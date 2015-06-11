/////////////////
// This system test has two purposes: showing what the groovy script model initializer can do
// and what you can expect, and showing that the visualizations work properly.
//
// initializing with width = 1000px, height = 700px, default animation duration = 1000ms.
initialize(1000, 700, 1000);


// Default text node for explanation.
addNode(
    new Node("t").set(fx("text").setPosition(10, 10).setWrappingWidth(900).setText("System test 1"))
);


/* This is the full list of possible transitions. Switch them however you want to see that it won't matter.
durationtest
transitionparameters:int=123;str=string_param
addNodesShowcase
generalNodePropertyTest
shapeNodePropertyTest
rectangleNodePropertyTest
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
addTransition("durationtest", 5 * 1000, {
    
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
    } catch (MissingMethodException e) {}
    
    
    // And show the node ending the "stream of circles" to make the visualization complete.
    addNode(new Node().set(fx("circle").setRadius(5).setPosition(80, 10).setFill(Color.RED)));
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
        fail("invalid opacity set");
    } catch (IllegalArgumentException e) {}
    try {
        node("c").fx().setOpacity(2.0);
        fail("invalid opacity set");
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
    
    // An impossible one: JavaFX can't animate into a gradient (probably because there are so many options).
    // See your serverside logs for the "Animating of JavaFX node property (...) failed" message.
    // It's not a fatal exception, so GreenMirror continues with nothing more than a log entry. The fill is
    // still green.
    node("r").fx().setFill("linear-gradient(white, black)");
    flush();
    
    // Another impossible one, or rather an invalid one.
    try {
        node("r").fx().setFill("invalid fill value");
        fail("invalid fill value");
    } catch (IllegalArgumentException e) {}
    flush();
});

/******************************************************************************
 * Test: properties that apply to javafx.scene.shape.Shape nodes
 */
addTransition("rectangleNodePropertyTest", 2000, {
    
    node("t").fx().setText("This tests all the properties of a rectangle");
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






// Relations
// Test adding a relation with placement when it already has it (should remove the previous placement relation)
// Test setNextNodeA(NodeList) and setNextPlacement(Placement...)
// Test the existence of relations of a removed node.
// Test negative width with placement relation

// Node#set(FxWrapper)
// Test setting it twice with the same type (and with different type)
// Test getting fx("invalid")

