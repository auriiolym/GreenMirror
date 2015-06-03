package greenmirror.tests;

import static org.hamcrest.CoreMatchers.allOf;
import static org.hamcrest.CoreMatchers.equalTo;
import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.CoreMatchers.not;
import static org.hamcrest.CoreMatchers.nullValue;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertThat;
import static org.junit.Assert.fail;
import greenmirror.Node;
import greenmirror.NodeList;
import greenmirror.Placement;
import greenmirror.Relation;

import org.junit.Before;
import org.junit.Test;

/**
 * Test case for the <code>Node</code> class.
 * @author Karim El Assal
 */
public class NodeTest {

    Node n1;
    Node n2;
    Node n3;
    Node n4;
    Node n5;
    Node n6;
    Node n7;
    Node n8;
    
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
        
        n1.addRelation(new Relation("on").setNodeB(n2).setPlacement(Placement.MIDDLE));
        n1.addRelation(new Relation("likes").setNodeB(n3));
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
        
        assertThat(n1.addLabel(null), is(equalTo(n1)));
        assertThat(n1.hasLabel(null), is(false));
        
        assertThat(n1.removeLabel("label2"), is(equalTo(n1)));
        assertThat(n1.hasLabel("label2"), is(false));
        assertThat(n1.removeLabel(null), is(equalTo(n1)));
        assertThat(n1.hasLabel(null), is(false));
    }
    
    @Test
    public void testNodeListConstructors() {
        NodeList emptyList = new NodeList();
        assertThat(emptyList.isEmpty(), is(true));
        
        NodeList newList = new NodeList(list);
        assertThat(newList, is(equalTo(list)));
        
        NodeList newList1 = new NodeList(n1, n2, n3, n4, n5, n6, n7, n8);
        assertThat(newList1, is(equalTo(list)));
    }
    
    @Test
    public void testIdentifierFilters() {
        NodeList filteredList1 = list.withName("name1");
        assertThat(true, allOf(
                            is(filteredList1.contains(n1)), 
                            is(filteredList1.contains(n3)), 
                            is(filteredList1.contains(n4)), 
                            is(filteredList1.size() == 3)));
        
        NodeList filteredList2 = list.withIdentifier(":name3");
        assertThat(true, allOf(
                            is(filteredList2.contains(n5)),
                            is(filteredList2.size() == 1)));
        
        NodeList filteredList3 = list.ofType("type1");
        assertThat(true, allOf(
                            is(filteredList3.contains(n1)), 
                            is(filteredList3.contains(n2)), 
                            is(filteredList3.contains(n3)), 
                            is(filteredList3.size() == 3)));

        assertFalse(list == filteredList1);
        assertFalse(list == filteredList2);
        assertFalse(list == filteredList3);
    }
    
    @Test
    public void testOneSizeNodeList() {
        assertThat(list.one().size(), is(1));
        assertThat(list.one().getFirst(), is(n1));
    }
    
    @Test
    public void testCircularNextNode() {
        // Test simple scenario.
        assertThat(list.getCircularNext(n1), is(n2));
        // Test circular scenario.
        assertThat(list.getCircularNext(n8), is(n1));
        // Test list with one node.
        assertThat(list.one().getCircularNext(n1), is(n1));
        // Test when current node is null.
        assertThat(list.getCircularNext(null), is(n1));
        
        // Test IndexOutOfBounds exception.
        try {
            new NodeList().getCircularNext(null);
            fail();
        } catch (IndexOutOfBoundsException e) {
            // Do nothing, just get rid of a checkstyle warning.
            return;
        }
    }
    
    @Test
    public void testLabelfilter() {
        NodeList filteredList1 = list.withLabel("label1");
        assertThat(true, allOf(
                            is(filteredList1.contains(n1)), 
                            is(filteredList1.contains(n2)), 
                            is(filteredList1.size() == 2)));
        
        NodeList filteredList2 = list.withLabel("unknown label");
        assertThat(filteredList2.isEmpty(), is(true));
    }
    
    @Test
    public void testRemoveNodes() {
        //TODO: test removed nodes and the getCircularNext() method.        
    }
    
    @Test
    public void testNodeToString() {
        assertThat(n1.toString(), is("Node id=1 | type=type1 | name=name1 | labels=[label1, "
                + "label2] | relations=[Relation name=on|fromNodeId=1|toNodeId=2|placement="
                + "MIDDLE|rigid=false|temporaryAppearanceofNodeA=not_set, Relation name=likes"
                + "|fromNodeId=1|toNodeId=3|placement=NONE|rigid=false|temporaryAppearanceof"
                + "NodeA=not_set]"));
    }

}
