initialize(700, 500, 2000);

addNodes(
    new Node("pngimg").set(fx("image")
                   .setImageFromUrl("https://a.gfx.ms/ic/bluemanm.png")
                   .setPosition(10, 10)), // doesn't work
                   
    new Node("jpgimg").set(fx("image")
                   .setImageFromFile("testcases/img.jpg")
                   .setPosition(100, 100)),
                   
    new Node("goat").set(fx("image")
                   .setImageFromFile("testcases/goat.png")
                   .setPosition(200, 100)
                   .setFitWidth(70)
                   .setPreserveRatio(true))
                   
);

//fx("image").setImage(new javafx.scene.image.Image("https://dyn.web.whatsapp.com/pp?t=s&u=31619588756%40c.us&i=1385299866"));
//new greenmirror.fxwrappers.MyImage("https://dyn.web.whatsapp.com/pp?t=s&u=31619588756%40c.us&i=1385299866");
//fx("image").setImage("https://dyn.web.whatsapp.com/pp?t=s&u=31619588756%40c.us&i=1385299866");

flush(1000);

node("goat").fx().setY(300);

flush();

node("goat").fx().setImageFromFile("testcases/cabbage.png");