// An initializer to test the looks of the stage.
initialize(600, 400, 3000);

addNode(new Node()).fx("rectangle").setPosition(0, 0).setSize(100, 100);


addTransition("tr1", {
    addNode(new Node()).fx("rectangle").setPosition(100, 100).setSize(10, 10);
});
