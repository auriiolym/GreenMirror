initialize(700, 500, true);


Node n = new Node("pl:").set(fx("circle").setRadius(10));
addNodes(
    new Node("c1").set(fx("circle")
                        .setFill("linear-gradient(red, blue)")
                        .setPosition(150, 150)
                        .setRadius(100)),
    new Node("r1").set(fx("rectangle")
                        .setFill("brown")
                        .setPosition(300, 300)
                        .setSize(40, 40)),
    n.clone(),
    n.clone(),
    n.clone(),
    n.clone(),
    n.clone(),
    n.clone(),
    n.clone().set(fx("circle").setRadius(10).setFill("yellow")),
    n.clone().set(fx("circle").setRadius(10).setFill("orange")),
    n.clone(),
    n.clone(),
    n.clone().set(fx("circle").setRadius(10).setFill("green")),
    n.clone().set(fx("circle").setRadius(10).setFill("darkgreen")),
    n.clone().set(fx("circle").setRadius(10).setFill("limegreen")), //12
    n.clone().setName("c"),
    n.clone(),
    n.clone(),
    n.clone(),
);

Relation r = new Relation().setNodeB(node("c1")).setPlacement(Placement.MIDDLE).setRigid(true);
Relation r2 = new Relation().setNodeB(node("r1")).setPlacement(Placement.MIDDLE).setRigid(true);
addRelations(
    r.clone().setNodeA(nodes("pl:").get(0)).setPlacement(Placement.MIDDLE),
    r.clone().setNodeA(nodes("pl:").get(1)).setPlacement(new Placement.Custom(-20, 0)),
    r.clone().setNodeA(nodes("pl:").get(2)).setPlacement(Placement.EDGE_TOP),
    r.clone().setNodeA(nodes("pl:").get(3)).setPlacement(Placement.EDGE_RIGHT),
    r.clone().setNodeA(nodes("pl:").get(4)).setPlacement(Placement.EDGE_BOTTOM),
    r.clone().setNodeA(nodes("pl:").get(5)).setPlacement(Placement.EDGE_LEFT),
    r.clone().setNodeA(nodes("pl:").get(6)).setPlacement(Placement.CORNER_TOP_LEFT),
    r.clone().setNodeA(nodes("pl:").get(7)).setPlacement(Placement.CORNER_BOTTOM_LEFT),
    r.clone().setNodeA(nodes("pl:").get(8)).setPlacement(Placement.CORNER_TOP_RIGHT),
    r.clone().setNodeA(nodes("pl:").get(9)).setPlacement(Placement.CORNER_BOTTOM_RIGHT),
    r.clone().setNodeA(nodes("pl:").get(10)).setPlacement(Placement.RANDOM),
    r.clone().setNodeA(nodes("pl:").get(11)).setPlacement(Placement.RANDOM),
    r.clone().setNodeA(nodes("pl:").get(12)).setPlacement(Placement.RANDOM),
    r2.clone().setNodeA(nodes("pl:c").get(0)).setPlacement(new Placement.Edge(360*80+90)),
);


addTransition("transition1", {
    node("c1").fx().setRotate(10);
    flush(200);
    node("c1").fx().setCenterX(200);
});
