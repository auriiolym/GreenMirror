package greenmirror.client;

import greenmirror.Node;
import greenmirror.fxcontainers.RectangleFxContainer;

import java.util.ArrayList;
import java.util.List;

import javafx.scene.paint.Paint;

/**
 * 
 * 
 * @author Karim El Assal
 */
public class GridBuilder {
    
    
    // -- Instance variables -----------------------------------------------------------------

    private String gridName;
    private int cellCountHorizontal;
    private int cellCountVertical;
    private double cellWidth;
    private double cellHeight;
    private double cellArcWidth = 0;
    private double cellArcHeight = 0;
    private Paint cellFill;
    private double cellSpacing = 0;
    private double borderSizeTop = 0;
    private double borderSizeRight = 0;
    private double borderSizeBottom = 0;
    private double borderSizeLeft = 0;
    private Paint backgroundFill;
    private double backgroundArcWidth = 0;
    private double backgroundArcHeight = 0;
    
    private List<Node> nodes;
    

    // -- Constructors -----------------------------------------------------------------------

    public GridBuilder(String gridName) {
        setGridName(gridName);
    }


    // -- Queries ----------------------------------------------------------------------------
    
    /**
     * @return The gridName.
     */
    public String getGridName() {
        return gridName;
    }

    /**
     * @return The cellCountHorizontal.
     */
    public int getCellCountHorizontal() {
        return cellCountHorizontal;
    }

    /**
     * @return The cellCountVertical.
     */
    public int getCellCountVertical() {
        return cellCountVertical;
    }

    /**
     * @return The cellWidth.
     */
    public double getCellWidth() {
        return cellWidth;
    }

    /**
     * @return The cellHeight.
     */
    public double getCellHeight() {
        return cellHeight;
    }

    /**
     * @return The cellFill.
     */
    public Paint getCellFill() {
        return cellFill;
    }

    /**
     * @return The cellArcWidth.
     */
    public double getCellArcWidth() {
        return cellArcWidth;
    }

    /**
     * @return The cellArcHeight.
     */
    public double getCellArcHeight() {
        return cellArcHeight;
    }

    /**
     * @return The cellSpacing.
     */
    public double getCellSpacing() {
        return cellSpacing;
    }

    /**
     * @return The borderSizeTop.
     */
    public double getBorderSizeTop() {
        return borderSizeTop;
    }

    /**
     * @return The borderSizeRight.
     */
    public double getBorderSizeRight() {
        return borderSizeRight;
    }

    /**
     * @return The borderSizeBottom.
     */
    public double getBorderSizeBottom() {
        return borderSizeBottom;
    }

    /**
     * @return The borderSizeLeft.
     */
    public double getBorderSizeLeft() {
        return borderSizeLeft;
    }

    /**
     * @return The backgroundFill.
     */
    public Paint getBackgroundFill() {
        return backgroundFill;
    }
    
    /**
     * @return The backgroundArcWidth.
     */
    public double getBackgroundArcWidth() {
        return backgroundArcWidth;
    }

    /**
     * @return The backgroundArcHeight.
     */
    public double getBackgroundArcHeight() {
        return backgroundArcHeight;
    }

    /**
     * @return The nodes built by this <tt>GridBuilder</tt>.
     * @throws IllegalStateException If the grid hasn't been built yet.
     */
    public Node[] getNodes() {
        if (nodes == null) {
            throw new IllegalStateException("Build the grid before retrieving the nodes.");
        }
        return nodes.toArray(new Node[]{});
    }


    // -- Setters ----------------------------------------------------------------------------

    /**
     * @param gridName The gridName to set.
     */
    private void setGridName(String gridName) {
        this.gridName = gridName;
    }

    /**
     * @param horizontal The cellCountHorizontal to set.
     * @param vertical   The cellCountVertical to set.
     * @return           <tt>this</tt>
     */
    public GridBuilder setCellCount(int horizontal, int vertical) {
        setCellCountHorizontal(horizontal);
        setCellCountVertical(vertical);
        return this;
    }
    
    /**
     * @param cellCountHorizontal The cellCountHorizontal to set.
     * @return                    <tt>this</tt>
     */
    public GridBuilder setCellCountHorizontal(int cellCountHorizontal) {
        this.cellCountHorizontal = cellCountHorizontal;
        return this;
    }

    /**
     * @param cellCountVertical The cellCountVertical to set.
     * @return                  <tt>this</tt>
     */
    public GridBuilder setCellCountVertical(int cellCountVertical) {
        this.cellCountVertical = cellCountVertical;
        return this;
    }
    
    /**
     * @param width  The cellWidth to set.
     * @param height The cellHeight to set.
     * @return       <tt>this</tt>
     */
    public GridBuilder setCellSize(double width, double height) {
        setCellWidth(width);
        setCellHeight(height);
        return this;
    }

    /**
     * @param cellWidth The cellWidth to set.
     * @return          <tt>this</tt>
     */
    public GridBuilder setCellWidth(double cellWidth) {
        this.cellWidth = cellWidth;
        return this;
    }

    /**
     * @param cellHeight The cellHeight to set.
     * @return           <tt>this</tt>
     */
    public GridBuilder setCellHeight(double cellHeight) {
        this.cellHeight = cellHeight;
        return this;
    }

    /**
     * @param cellFill The cellFill to set.
     * @return         <tt>this</tt>
     */
    public GridBuilder setCellFill(String cellFill) {
        return setCellFill(Paint.valueOf(cellFill));
    }

    /**
     * @param cellFill The cellFill to set.
     * @return         <tt>this</tt>
     */
    public GridBuilder setCellFill(Paint cellFill) {
        this.cellFill = cellFill;
        return this;
    }

    /**
     * @param cellArc The cellArcWidth and cellArcHeight to set.
     * @return        <tt>this</tt>
     */
    public GridBuilder setCellArcs(double cellArc) {
        return setCellArcs(cellArc, cellArc);
    }

    /**
     * @param cellArcWidth  The cellArcWidth to set.
     * @param cellArcHeight The cellArcHeight to set.
     * @return              <tt>this</tt>
     */
    public GridBuilder setCellArcs(double cellArcWidth, double cellArcHeight) {
        this.cellArcWidth = cellArcWidth;
        this.cellArcHeight = cellArcHeight;
        return this;
    }
    
    /**
     * @param cellSpacing The cellSpacing to set.
     * @return            <tt>this</tt>
     */
    public GridBuilder setCellSpacing(double cellSpacing) {
        this.cellSpacing = cellSpacing;
        return this;
    }
    
    /**
     * @param size The borderSize to set for all sides.
     * @return     <tt>this</tt>
     */
    public GridBuilder setBorderSize(double size) {
        setBorderSizeTop(size);
        setBorderSizeRight(size);
        setBorderSizeBottom(size);
        setBorderSizeLeft(size);
        return this;
    }
    
    /**
     * @param topBottomSize The borderSize to set for the top and the bottom sides.
     * @param rightLeftSize The borderSize to set for the right and left sides.
     * @return              <tt>this</tt>
     */
    public GridBuilder setBorderSize(double topBottomSize, double rightLeftSize) {
        setBorderSizeTop(topBottomSize);
        setBorderSizeBottom(topBottomSize);
        setBorderSizeRight(rightLeftSize);
        setBorderSizeLeft(rightLeftSize);
        return this;
    }

    /**
     * @param borderSizeTop The borderSizeTop to set.
     * @return              <tt>this</tt>
     */
    public GridBuilder setBorderSizeTop(double borderSizeTop) {
        this.borderSizeTop = borderSizeTop;
        return this;
    }

    /**
     * @param borderSizeRight The borderSizeRight to set.
     * @return                <tt>this</tt>
     */
    public GridBuilder setBorderSizeRight(double borderSizeRight) {
        this.borderSizeRight = borderSizeRight;
        return this;
    }

    /**
     * @param borderSizeBottom The borderSizeBottom to set.
     * @return                 <tt>this</tt>
     */
    public GridBuilder setBorderSizeBottom(double borderSizeBottom) {
        this.borderSizeBottom = borderSizeBottom;
        return this;
    }

    /**
     * @param borderSizeLeft The borderSizeLeft to set.
     * @return               <tt>this</tt>
     */
    public GridBuilder setBorderSizeLeft(double borderSizeLeft) {
        this.borderSizeLeft = borderSizeLeft;
        return this;
    }

    /**
     * @param backgroundFill The backgroundFill to set.
     * @return               <tt>this</tt>
     */
    public GridBuilder setBackgroundFill(Paint backgroundFill) {
        this.backgroundFill = backgroundFill;
        return this;
    }

    /**
     * @param backgroundFill The backgroundFill to set.
     * @return               <tt>this</tt>
     */
    public GridBuilder setBackgroundFill(String backgroundFill) {
        return setBackgroundFill(Paint.valueOf(backgroundFill));
    }

    /**
     * @param backgroundArc The backgroundArcWidth and backgroundArcHeight to set.
     * @return              <tt>this</tt>
     */
    public GridBuilder setBackgroundArcs(double backgroundArc) {
        return setBackgroundArcs(backgroundArc, backgroundArc);
    }

    /**
     * @param backgroundArcWidth  The backgroundArcWidth to set.
     * @param backgroundArcHeight The backgroundArcHeight to set.
     * @return                    <tt>this</tt>
     */
    public GridBuilder setBackgroundArcs(double backgroundArcWidth, double backgroundArcHeight) {
        this.backgroundArcWidth = backgroundArcWidth;
        this.backgroundArcHeight = backgroundArcHeight;
        return this;
    }


    // -- Commands ---------------------------------------------------------------------------


    public GridBuilder build(double posX, double posY) {
        
        // First check if all values are valid.
        if (getGridName() == null || getGridName().length() == 0 || getCellCountHorizontal() <= 0 
         || getCellCountVertical() <= 0 || getCellWidth() <= 0 || getCellHeight() <= 0 
         || getBorderSizeTop() < 0 || getBorderSizeRight() < 0 || getBorderSizeBottom() < 0 
         || getBorderSizeLeft() < 0 || getCellSpacing() < 0 || getCellArcWidth() < 0 
         || getCellArcHeight() < 0 || getBackgroundArcWidth() < 0 || getBackgroundArcHeight() < 0
         || posX < 0 || posY < 0) {
            throw new IllegalArgumentException("One or more values of the GridBuilder are "
                    + "invalid.");
        }
        
        nodes = new ArrayList<Node>();
        
        // Build the background.
        double totalWidth = getBorderSizeLeft() + getBorderSizeRight() + getCellCountHorizontal() 
                          * getCellWidth() + (getCellCountHorizontal() - 1) * getCellSpacing(); 
        double totalHeight = getBorderSizeTop() + getBorderSizeBottom() + getCellCountVertical()
                          * getCellHeight() + (getCellCountVertical() - 1) * getCellSpacing();
        Node bg = new Node().setType(getGridName()).setName("background").set(
                new RectangleFxContainer()
                    .setPosition(posX, posY)
                    .setSize(totalWidth, totalHeight)
                    .setFill(getBackgroundFill())
                    .setArcWidth(getBackgroundArcWidth())
                    .setArcHeight(getBackgroundArcHeight()));
        nodes.add(bg);
        
        // Build the cells
        int cellI = 0; // Cell index (and name).
        double currPosX;
        double currPosY;
        RectangleFxContainer fxPrototype = new RectangleFxContainer()
                                                .setSize(getCellWidth(), getCellHeight())
                                                .setFill(getCellFill())
                                                .setArcWidth(getCellArcWidth())
                                                .setArcHeight(getCellArcHeight());
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
                            .setType(getGridName())
                            .setName(String.valueOf(cellI))
                            .set(fxPrototype.clone().setPosition(currPosX, currPosY)));
                cellI++;
            }
        }
        
        return this;
    }
}
