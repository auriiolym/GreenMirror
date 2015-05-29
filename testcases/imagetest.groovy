initialize(700, 500);

addNodes(
    new Node("pngimg").set(fx("image")
                   .setImage("testcases/img.png")
                   .setPosition(10, 10)),
                   
    new Node("jpgimg").set(fx("image")
                   .setImage("testcases/img.jpg")
                   .setPosition(100, 100)
                   .setFitWidth(96)
                   .setFitHeight(96)
                   .setPreserveRatio(true))
                   
);