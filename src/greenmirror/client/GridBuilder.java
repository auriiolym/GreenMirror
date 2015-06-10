package greenmirror.client;

import greenmirror.Node;
import greenmirror.fxwrappers.RectangleFxWrapper;

import org.eclipse.jdt.annotation.NonNull;

import java.util.ArrayList;
import java.util.List;

import javafx.scene.paint.Color;
import javafx.scene.paint.Paint;

/**
 * An auxiliary class that makes building grids on the visualizer significantly less tedious. It
 * uses the builder design pattern, so use it like this:
 * <code>new GridBuilder("nodes_type:nodes_nameprefix")
 *                      .setOPTION()
 *                      .build(xCoordinate, yCoordinate)
 *                      .getNodes();</code>
 * This retrieves the nodes that the grid consists of: one node for each cell and one extra for the
 * background. The cell nodes will get a name consisting of the specified prefix, followed by
 * the cell number (starting with the number zero). The background node will get a name consisting 
 * of the specified prefix followed by "background". 
 * <p>
 * The only properties that are required are the cell count and the cell width and height. All
 * other properties have a default value of zero or null. It is highly recommended to set the fill
 * property of either the cells or the background, because those default to a black color.  
 * 
 * @author Karim El Assal
 */
public class GridBuilder {
    
    
    // -- Instance variables -----------------------------------------------------------------

    private String nodeType = null;
    private String nodeNamePrefix = null;
    private int cellCountHorizontal;
    private int cellCountVertical;
    private double cellWidth;
    private double cellHeight;
    private double cellArcWidth = 0;
    private double cellArcHeight = 0;
    private Paint cellFill = Color.BLACK;
    private double cellSpacing = 0;
    private double borderSizeTop = 0;
    private double borderSizeRight = 0;
    private double borderSizeBottom = 0;
    private double borderSizeLeft = 0;
    private Paint backgroundFill = Color.BLACK;
    private double backgroundArcWidth = 0;
    private double backgroundArcHeight = 0;
    
    private List<Node> nodes;
    

    // -- Constructors -----------------------------------------------------------------------

    /**
     * Starts the gruid builder, directly setting the type property of the nodes and the name 
     * prefix. Both are optional: an empty string or <code>null</code> value is allowed.
     * 
     * @param gridIdentifier the identifier consisting of the type property and the name prefix 
     *                       the nodes should receive. Optional. See {@link Node.Identifier}
     */
    public GridBuilder(String gridIdentifier) {
        Node.Identifier identifier = new Node.Identifier(gridIdentifier);
        setNodeType(identifier.getType());
        setNodeNamePrefix(identifier.getName());
    }


    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @return the type property the nodes will receive
     */
    public String getNodeType() {
        return nodeType;
    }
    
    /**
     * @return the name prefix the nodes will receive
     */
    public String getNodeNamePrefix() {
        return nodeNamePrefix;
    }

    /**
     * @return the horizontal cell count
     */
    public int getCellCountHorizontal() {
        return cellCountHorizontal;
    }

    /**
     * @return the vertical cell count
     */
    public int getCellCountVertical() {
        return cellCountVertical;
    }

    /**
     * @return the cell width
     */
    public double getCellWidth() {
        return cellWidth;
    }

    /**
     * @return the cell height
     */
    public double getCellHeight() {
        return cellHeight;
    }

    /**
     * @return the cell's fill property
     */
    public Paint getCellFill() {
        return cellFill;
    }

    /**
     * @return the cell's arc width.
     */
    public double getCellArcWidth() {
        return cellArcWidth;
    }

    /**
     * @return the cell's arc height.
     */
    public double getCellArcHeight() {
        return cellArcHeight;
    }

    /**
     * @return the cell spacing.
     */
    public double getCellSpacing() {
        return cellSpacing;
    }

    /**
     * @return the top border size
     */
    public double getBorderSizeTop() {
        return borderSizeTop;
    }

    /**
     * @return the right border size
     */
    public double getBorderSizeRight() {
        return borderSizeRight;
    }

    /**
     * @return the bottom border size
     */
    public double getBorderSizeBottom() {
        return borderSizeBottom;
    }

    /**
     * @return the left border size
     */
    public double getBorderSizeLeft() {
        return borderSizeLeft;
    }

    /**
     * @return the background's fill
     */
    public Paint getBackgroundFill() {
        return backgroundFill;
    }
    
    /**
     * @return the background's arc width.
     */
    public double getBackgroundArcWidth() {
        return backgroundArcWidth;
    }

    /**
     * @return the background's arc height.
     */
    public double getBackgroundArcHeight() {
        return backgroundArcHeight;
    }

    /**
     * @return the nodes built by this <code>GridBuilder</code>.
     * @throws IllegalStateException if the grid hasn't been built yet
     */
    public Node[] getNodes() {
        if (nodes == null) {
            throw new IllegalStateException("build the grid before retrieving the nodes");
        }
        return nodes.toArray(new Node[]{});
    }


    // -- Setters ----------------------------------------------------------------------------

    /**
     * @param nodeType the nodeType to set
     */
    private void setNodeType(String nodeType) {
        this.nodeType = nodeType;
    }

    /**
     * @param nodeNamePrefix the nodeNamePrefix to set
     */
    private void setNodeNamePrefix(String nodeNamePrefix) {
        this.nodeNamePrefix = nodeNamePrefix;
    }

    /**
     * @param horizontal the cellCountHorizontal to set. Required for building the grid
     * @param vertical   the cellCountVertical to set.  Required for building the grid
     * @return           <code>this</code>
     */
    @NonNull public GridBuilder setCellCount(int horizontal, int vertical) {
        setCellCountHorizontal(horizontal);
        setCellCountVertical(vertical);
        return this;
    }
    
    /**
     * @param cellCountHorizontal the cellCountHorizontal to set. Required for building the grid
     * @return                    <code>this</code>
     */
    @NonNull public GridBuilder setCellCountHorizontal(int cellCountHorizontal) {
        this.cellCountHorizontal = cellCountHorizontal;
        return this;
    }

    /**
     * @param cellCountVertical the cellCountVertical to set. Required for building the grid
     * @return                  <code>this</code>
     */
    @NonNull public GridBuilder setCellCountVertical(int cellCountVertical) {
        this.cellCountVertical = cellCountVertical;
        return this;
    }
    
    /**
     * @param width  the cellWidth to set. Required for building the grid
     * @param height the cellHeight to set. Required for building the grid
     * @return       <code>this</code>
     */
    @NonNull public GridBuilder setCellSize(double width, double height) {
        setCellWidth(width);
        setCellHeight(height);
        return this;
    }

    /**
     * @param cellWidth the cellWidth to set. Required for building the grid
     * @return          <code>this</code>
     */
    @NonNull public GridBuilder setCellWidth(double cellWidth) {
        this.cellWidth = cellWidth;
        return this;
    }

    /**
     * @param cellHeight the cellHeight to set. Required for building the grid
     * @return           <code>this</code>
     */
    @NonNull public GridBuilder setCellHeight(double cellHeight) {
        this.cellHeight = cellHeight;
        return this;
    }

    /**
     * @param cellFill the cellFill to set
     * @return         <code>this</code>
     */
    @NonNull public GridBuilder setCellFill(String cellFill) {
        return setCellFill(Paint.valueOf(cellFill));
    }

    /**
     * @param cellFill the cellFill to set
     * @return         <code>this</code>
     */
    @NonNull public GridBuilder setCellFill(Paint cellFill) {
        this.cellFill = cellFill;
        return this;
    }

    /**
     * @param cellArc the cellArcWidth and cellArcHeight to set
     * @return        <code>this</code>
     */
    @NonNull public GridBuilder setCellArcs(double cellArc) {
        return setCellArcs(cellArc, cellArc);
    }

    /**
     * @param cellArcWidth  the cellArcWidth to set
     * @param cellArcHeight the cellArcHeight to set
     * @return              <code>this</code>
     */
    @NonNull public GridBuilder setCellArcs(double cellArcWidth, double cellArcHeight) {
        this.cellArcWidth = cellArcWidth;
        this.cellArcHeight = cellArcHeight;
        return this;
    }
    
    /**
     * @param cellSpacing the cellSpacing to set
     * @return            <code>this</code>
     */
    @NonNull public GridBuilder setCellSpacing(double cellSpacing) {
        this.cellSpacing = cellSpacing;
        return this;
    }
    
    /**
     * @param size The borderSize to set for all sides.
     * @return     <code>this</code>
     */
    @NonNull public GridBuilder setBorderSize(double size) {
        setBorderSizeTop(size);
        setBorderSizeRight(size);
        setBorderSizeBottom(size);
        setBorderSizeLeft(size);
        return this;
    }
    
    /**
     * @param topBottomSize The borderSize to set for the top and the bottom sides.
     * @param rightLeftSize The borderSize to set for the right and left sides.
     * @return              <code>this</code>
     */
    @NonNull public GridBuilder setBorderSize(double topBottomSize, double rightLeftSize) {
        setBorderSizeTop(topBottomSize);
        setBorderSizeBottom(topBottomSize);
        setBorderSizeRight(rightLeftSize);
        setBorderSizeLeft(rightLeftSize);
        return this;
    }
    
    /**
     * @param topSize    The borderSize to set for the top side.
     * @param rightSize  The borderSize to set for the right side.
     * @param bottomSize The borderSize to set for the bottom side.
     * @param leftSize   The borderSize to set for the left side.
     * @return              <code>this</code>
     */
    @NonNull public GridBuilder setBorderSize(double topSize, double rightSize, double bottomSize, 
            double leftSize) {
        setBorderSizeTop(topSize);
        setBorderSizeBottom(bottomSize);
        setBorderSizeRight(rightSize);
        setBorderSizeLeft(leftSize);
        return this;
    }

    /**
     * @param borderSizeTop the borderSizeTop to set
     * @return              <code>this</code>
     */
    @NonNull public GridBuilder setBorderSizeTop(double borderSizeTop) {
        this.borderSizeTop = borderSizeTop;
        return this;
    }

    /**
     * @param borderSizeRight the borderSizeRight to set
     * @return                <code>this</code>
     */
    @NonNull public GridBuilder setBorderSizeRight(double borderSizeRight) {
        this.borderSizeRight = borderSizeRight;
        return this;
    }

    /**
     * @param borderSizeBottom the borderSizeBottom to set
     * @return                 <code>this</code>
     */
    @NonNull public GridBuilder setBorderSizeBottom(double borderSizeBottom) {
        this.borderSizeBottom = borderSizeBottom;
        return this;
    }

    /**
     * @param borderSizeLeft the borderSizeLeft to set
     * @return               <code>this</code>
     */
    @NonNull public GridBuilder setBorderSizeLeft(double borderSizeLeft) {
        this.borderSizeLeft = borderSizeLeft;
        return this;
    }

    /**
     * @param backgroundFill the backgroundFill to set
     * @return               <code>this</code>
     */
    @NonNull public GridBuilder setBackgroundFill(Paint backgroundFill) {
        this.backgroundFill = backgroundFill;
        return this;
    }

    /**
     * @param backgroundFill the backgroundFill to set
     * @return               <code>this</code>
     */
    @NonNull public GridBuilder setBackgroundFill(String backgroundFill) {
        return setBackgroundFill(Paint.valueOf(backgroundFill));
    }

    /**
     * @param backgroundArc the backgroundArcWidth and backgroundArcHeight to set
     * @return              <code>this</code>
     */
    @NonNull public GridBuilder setBackgroundArcs(double backgroundArc) {
        return setBackgroundArcs(backgroundArc, backgroundArc);
    }

    /**
     * @param backgroundArcWidth  the backgroundArcWidth to set
     * @param backgroundArcHeight the backgroundArcHeight to set
     * @return                    <code>this</code>
     */
    @NonNull public GridBuilder setBackgroundArcs(double backgroundArcWidth, 
                                                  double backgroundArcHeight) {
        this.backgroundArcWidth = backgroundArcWidth;
        this.backgroundArcHeight = backgroundArcHeight;
        return this;
    }


    // -- Commands ---------------------------------------------------------------------------

    /**
     * Builds the grid. All properties should have a valid value by the time this method is 
     * called. Call {@link #getNodes()} to get the created nodes.
     * 
     * @param posX the x coordinate where the top left corner of the grid should be placed
     * @param posY the y coordinate where the top left corner of the grid should be placed
     * @return     <code>this</code>
     * @throws IllegalArgumentException if a property has an invalid value 
     */
    @NonNull public GridBuilder build(double posX, double posY) {
        
        // First check if all values are valid.
        if (getCellCountHorizontal() <= 0 
         || getCellCountVertical() <= 0 || getCellWidth() <= 0 || getCellHeight() <= 0 
         || getBorderSizeTop() < 0 || getBorderSizeRight() < 0 || getBorderSizeBottom() < 0 
         || getBorderSizeLeft() < 0 || getCellSpacing() < 0 || getCellArcWidth() < 0 
         || getCellArcHeight() < 0 || getBackgroundArcWidth() < 0 || getBackgroundArcHeight() < 0
         || posX < 0 || posY < 0) {
            throw new IllegalArgumentException("One or more values of the GridBuilder are "
                    + "invalid.");
        }
        
        nodes = new ArrayList<Node>();
        
        final String namePrefix = getNodeNamePrefix() == null ? "" : getNodeNamePrefix();
        
        // Build the background.
        final double totalWidth = getBorderSizeLeft() 
                          + getBorderSizeRight() 
                          + getCellCountHorizontal() * getCellWidth() 
                          + (getCellCountHorizontal() - 1) * getCellSpacing(); 
        final double totalHeight = getBorderSizeTop() 
                          + getBorderSizeBottom() 
                          + getCellCountVertical() * getCellHeight() 
                          + (getCellCountVertical() - 1) * getCellSpacing();
        final Node bg = new Node().setType(getNodeType()).setName(namePrefix + "background").set(
                                new RectangleFxWrapper()
                                    .setPosition(posX, posY)
                                    .setSize(totalWidth, totalHeight)
                                    .setArcWidth(getBackgroundArcWidth())
                                    .setArcHeight(getBackgroundArcHeight())
                                    .setFill(getBackgroundFill()));
        nodes.add(bg);
        
        // Build the cells
        int cellI = 0; // Cell index (and name).
        double currPosX;
        double currPosY;
        final RectangleFxWrapper fxPrototype = ((RectangleFxWrapper) new RectangleFxWrapper()
                                                        .setSize(getCellWidth(), getCellHeight())
                                                        .setArcWidth(getCellArcWidth())
                                                        .setArcHeight(getCellArcHeight())
                                                        .setFill(getCellFill()));
        // Loop through every row.
        for (int gridY = 0; gridY < getCellCountVertical(); gridY++) {
            // Determine y coordinate for the whole row.
            currPosY = posY + getBorderSizeTop() + gridY * (getCellHeight() + getCellSpacing());
            
            // Loop through every column.
            for (int gridX = 0; gridX < getCellCountHorizontal(); gridX++) {
                // Determine the x coordinate for the column.
                currPosX = posX + getBorderSizeLeft() + gridX * (getCellWidth() + getCellSpacing());
                
                // Create the node and add it to the collection.
                nodes.add(new Node()
                           .setType(getNodeType())
                           .setName(namePrefix + String.valueOf(cellI))
                           .set(fxPrototype.clone().setPosition(currPosX, currPosY)));
                cellI++;
            }
        }
        
        return this;
    }
}
