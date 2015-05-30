initialize(700, 500, 2000);

addNodes(
    new Node("pngimg").set(fx("image")
                   .setImageFromUrl("https://a.gfx.ms/ic/bluemanm.png")
                   .setPosition(10, 10)),
                   
    new Node("jpgimg").set(fx("image")
                   .setImageFromFile("testcases/img.jpg")
                   .setPosition(100, 100)),
                   
    new Node("goat").set(fx("image")
                   .setImageFromFile("testcases/goat.png")
                   .setPosition(200, 100)
                   .setFitWidth(70)
                   .setPreserveRatio(true))
                   
);


flush(1000);

node("goat").fx().setY(300);

flush();

node("goat").fx().setImageFromFile("testcases/cabbage.png");