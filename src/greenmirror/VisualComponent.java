package greenmirror;

public interface VisualComponent {

    /**
     * 
     * @param type
     */
    VisualComponent instantiate(String type);

    JSONObject toJSON();

    /**
     * 
     * @param of
     */
    AbsolutePosition calculatePosition(Placement of);

    /**
     * 
     * @param node
     */
    void setGMNode(Node node);

    Node getGMNode();

    /**
     * 
     * @param position
     */
    void setPositionWithMiddle(AbsolutePosition position);

    void appearanceUpdated();

    VisualComponent clone();

}