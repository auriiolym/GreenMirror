package greenmirror.tests;

import static org.hamcrest.CoreMatchers.allOf;
import static org.hamcrest.CoreMatchers.equalTo;
import static org.hamcrest.CoreMatchers.instanceOf;
import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.CoreMatchers.not;
import static org.hamcrest.CoreMatchers.nullValue;
import static org.junit.Assert.assertThat;
import static org.junit.Assert.fail;
import greenmirror.FxWrapper;
import greenmirror.Node;
import greenmirror.NodeList;
import greenmirror.Placement;
import greenmirror.Relation;
import greenmirror.RelationList;
import greenmirror.fxwrappers.RectangleFxWrapper;

import org.eclipse.jdt.annotation.NonNull;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

/**
 * Test case for the <code>Node</code> class.
 * @author Karim El Assal
 */
public class NodesRelationsTest {
    
    @Rule
    public ExpectedException exception = ExpectedException.none();

    Node n1;
    Node n2;
    Node n3;
    Node n4;
    Node n5;
    Node n6;
    Node n7;
    Node n8;
    
    Relation r1;
    Relation r2;
    Relation r3;
    
    NodeList list;

    /**
     * @throws java.lang.Exception
     */
    @Before
    public void setUp() throws Exception {
        list = new NodeList();
        
        list.add(n1 = new Node("type1:name1"));
        list.add(n2 = new Node("type1:name2"));
        list.add(n3 = new Node("type1:name1"));
        list.add(n4 = new Node("type2:name1"));
        list.add(n5 = new Node("name3"));
        list.add(n6 = new Node("type3:"));
        list.add(n7 = new Node(":name4"));
        list.add(n8 = new Node("type3:2"));
        
        n1.setId(1);        
        n2.setId(2);        
        n3.setId(3);        
        n4.setId(4);        
        n5.setId(5);        
        n6.setId(6);        
        n7.setId(7);        
        n8.setId(8);
        
        n1.addLabel("label1");
        n1.addLabel("label2");
        n2.addLabel("label1");
        
        r1 = new Relation("on").setNodeB(n2).setPlacement(Placement.MIDDLE).setRigid(true);
        r2 = new Relation("likes").setNodeB(n3);
        r3 = new Relation("hates").setNodeB(n4);
        
        n1.addRelation(r1);
        n1.addRelation(r2);
        n1.addRelation(r3);
    }
    
    @Test
    public void testConstructor() {
        assertThat(n1.getType(), is(equalTo("type1")));
        assertThat(n1.getType(), is(equalTo("type1")));
        assertThat(n2.getType(), is(equalTo("type1")));
        assertThat(n5.getType(), is(nullValue()));
        assertThat(n7.getType(), is(nullValue()));
        
        assertThat(n1.getName(), is(equalTo("name1")));
        assertThat(n2.getName(), is(equalTo("name2")));
        assertThat(n6.getName(), is(nullValue()));
        assertThat(n8.getName(), is(equalTo("2")));
        assertThat(n8.getName(), is(not(equalTo(2))));
        
        assertThat(n1.getType(), is(equalTo(n2.getType())));
        assertThat(n1.getName(), is(equalTo(n3.getName())));
        
    }

    @Test
    public void testSetName() {
        n1.setName("name");
        assertThat(n1.getName(), is(equalTo("name")));
        n1.setName("subname:subname");
        assertThat(n1.getName(), is(equalTo("subname:subname")));
        n1.setName(null);
        assertThat(n1.getName(), is(nullValue()));
    }
    
    @Test
    public void testSetType() {
        n1.setType("type");
        assertThat(n1.getType(), is(equalTo("type")));
        n1.setType("typepart:typepart");
        assertThat(n1.getType(), is(equalTo("typepart:typepart")));
        n1.setType(null);
        assertThat(n1.getType(), is(nullValue()));
    }
    
    @Test
    public void testLabels() {
        assertThat(n1.hasLabel("label1"), is(true));
        assertThat(n1.hasLabel("label0"), is(false));
        
        assertThat(n1.addLabel(null).hasLabel(null), is(false));
        
        assertThat(n1.removeLabel("label2").hasLabel("label2"), is(false));
        assertThat(n1.removeLabel(null).hasLabel(null), is(false));
    }
    
    @Test
    public void testNodeListConstructors() {
        assertThat(new NodeList().isEmpty(), is(true));
        
        assertThat(list, equalTo(new NodeList(list)));
        assertThat(list, equalTo(new NodeList(n1, n2, n3, n4, n5, n6, n7, n8)));
    }
    
    @Test
    @SuppressWarnings("null")
    public void testNodeList() {
        
        // withName(String)
        assertThat(list.withName("name1"), equalTo(new NodeList(n1, n3, n4)));
        
        // withIdentifier(String)
        assertThat(list.withIdentifier(":name3"), equalTo(new NodeList(n5)));
        assertThat(list.withIdentifier("name3"),  equalTo(new NodeList(n5)));
        assertThat(list.withIdentifier("type1:"), equalTo(new NodeList(n1, n2, n3)));
        
        // ofType(String)
        assertThat(list.ofType("type1"), equalTo(new NodeList(n1, n2, n3)));
        
        // one()
        assertThat(list.one().size(), is(1));
        assertThat(list.one().getFirst(), is(n1));
        assertThat(new NodeList().one().size(), is(0));
        
        // getCircularNext(Node)
        assertThat(list.getCircularNext(n1), is(n2));
        assertThat(list.getCircularNext(n8), is(n1));
        assertThat(list.one().getCircularNext(n1), is(n1));
        assertThat(list.getCircularNext(null), is(n1));
        try {
            new NodeList().getCircularNext(null);
            fail();
        } catch (IndexOutOfBoundsException e) {}

        // withLabel(String)
        assertThat(list.withLabel("label1"), equalTo(new NodeList(n1, n2)));
        assertThat(list.withLabel("unknown label").isEmpty(), is(true));
        
        // without(Node...)
        assertThat(new NodeList(n1, n2, n3).without(n1), equalTo(new NodeList(n2, n3)));
        assertThat(new NodeList(n1, n2, n3).without(), equalTo(new NodeList(n1, n2, n3)));
    }
    
    
    @Test
    public void testFxWrapper() {
        // Test retrieving non-existent FxWrapper. 
        try {
            n1.fx();
            fail();
        } catch (IllegalStateException e) {}

        // Test creation of unknown FxWrapper type.
        try {
            n1.fx("unknown FxWrapper type");
            fail();
        } catch (IllegalArgumentException e) {}
        
        // Test creation of FxWrapper with wrong capitalization.
        try {
            n1.fx("rectANGLE");
            fail();
        } catch (IllegalArgumentException e) {}
        
        // Test creation of FxWrapper.
        assertThat(n1.fx("rectangle"), is(instanceOf(RectangleFxWrapper.class)));
        assertThat(n1.fx(), is(equalTo(n1.fx("Rectangle"))));
        
        // Test re-creation of different FxWrapper.
        try {
            n1.fx("circle");
            fail();
        } catch (IllegalArgumentException e) {}
        
        // Test different way of creation.
        FxWrapper fxWrapper = new RectangleFxWrapper();
        n2.set(fxWrapper);
        assertThat(fxWrapper, allOf(equalTo(n2.fx()), 
                                    equalTo(n2.fx("rectangle")),
                                    equalTo(n2.getFxWrapper())));
    }
    
    @Test
    public void testRelationListConstructors() {
        final RelationList rlist = new RelationList();
        assertThat(rlist.isEmpty(), is(true));
        
        rlist.add(r1);
        rlist.add(r2);
        rlist.add(r3);
        assertThat(rlist, equalTo(new RelationList(r1, r2, r3)));
        assertThat(rlist, equalTo(new RelationList(rlist)));
        
    }
    
    @Test
    public void testRelationList() {
        final RelationList rl = n1.getRelations();
        final RelationList rl2 = n2.getRelations();
        final RelationList rl3 = n8.getRelations(); // empty
        
        // withId(String)
        assertThat(rl.withId("1|on|2|Middle|true"), equalTo(new RelationList(r1)));
        assertThat(rl.withId("").isEmpty(), is(true));
        
        // getNodesA()
        assertThat(rl.getNodesA(), equalTo(new NodeList(n1)));
        
        // withName(String)
        assertThat(rl.withName("hates"), equalTo(new RelationList(r3)));
        
        // withIsRigid(boolean)
        assertThat(rl.withIsRigid(true), equalTo(new RelationList(r1)));
        assertThat(rl.withIsRigid(false), equalTo(new RelationList(r2, r3)));
        assertThat(rl2.withIsRigid(false).isEmpty(), is(true));
        
        // withPlacement(Placement)
        assertThat(rl.withPlacement(Placement.MIDDLE), equalTo(new RelationList(r1)));
        assertThat(rl.withPlacement(Placement.NONE), equalTo(new RelationList(r2, r3)));
        assertThat(rl.withPlacement(Placement.RANDOM).isEmpty(), is(true));
        
        // withPlacement()
        assertThat(rl.withPlacement(), equalTo(new RelationList(r1)));
        assertThat(rl2.withPlacement(), equalTo(new RelationList(r1)));
        assertThat(rl3.withPlacement().isEmpty(), is(true));
        
        // withNoPlacement()
        assertThat(rl.withNoPlacement(), equalTo(new RelationList(r2, r3)));
        assertThat(rl2.withNoPlacement().isEmpty(), is(true));
        
        // withNodes(NodeList)
        assertThat(rl.withNodes(list.ofType("type1")), equalTo(rl));
        assertThat(rl.withNodes(new NodeList()).isEmpty(), is(true));
        
        // withNode(Node)
        assertThat(rl.withNode(n1), equalTo(rl));
        assertThat(rl.withNode(n8).isEmpty(), is(true));
        
        // withNodeA(Node)
        assertThat(rl.withNodeA(n1), equalTo(rl));
        assertThat(rl.withNodeA(n2).isEmpty(), is(true));
        
        // removeAll()
        rl.removeAll();
        assertThat(rl.isEmpty(), is(true));
        assertThat(n2.getRelations().isEmpty(), is(true));
    }
    
    @Test
    public void testRelation() {
        // getOtherNode(Node)
        assertThat(r1.getOtherNode(n2), equalTo(n1));
        assertThat(r1.getOtherNode(n8), is(nullValue()));
        
        // isRigid() (default value)
        assertThat(r2.isRigid(), is(false));
        
        // getPlacement()
        assertThat(r1.getPlacement(), equalTo(Placement.MIDDLE));
        assertThat(r2.getPlacement(), equalTo(Placement.NONE));
        
        // setRigid(boolean)
        try {
            r2.setRigid(true);
            fail();
        } catch (IllegalStateException e) {}
        
        // fromRelation(Relation)
        assertThat(new Relation("foo").fromRelation(r1).toString(), equalTo(r1.toString()));
        
        // clone()
        assertThat(r1.clone().toString(), equalTo(r1.toString()));
        
        // passToNextNodeA()
        assertThat(r1.passToNextNodeA(list).getNodeA(), equalTo(n2));
        for (int i = 0; i < list.size() - 1; i++) {
            r1.passToNextNodeA(list);
        }
        assertThat(r1.getNodeA(), equalTo(n1));
        // passToNextNodeB() works exactly the same.
        
        // removeFromNodes()
        r1.removeFromNodes();
        assertThat(n1.getRelations().contains(r1), is(false));
        assertThat(n2.getRelations().contains(r1), is(false));
        assertThat(r1.getNodeA(), equalTo(n1));
        assertThat(r1.getNodeB(), equalTo(n2));
        
        // addToNodes()
        r1.addToNodes();
        assertThat(n1.getRelations().contains(r1), is(true));
        assertThat(n2.getRelations().contains(r1), is(true));
    }

    
    
    
    
    
    
    
    
}
