package greenmirror.server;

import javafx.animation.Transition;
import javafx.scene.shape.Rectangle;
import javafx.util.Duration;

/**
 * A <tt>Transition</tt> class that animates the change of the arc width and/or height.
 * 
 * @author Karim El Assal
 */
public class ArcTransition extends Transition {

    // --- Instance variables ----------------------------------------------------------------

    private double fromWidth;
    
    private double toWidth;
    
    private double fromHeight;
    
    private double toHeight;
    
    private Rectangle node;
    
    // --- Constructors ----------------------------------------------------------------------
    
    public ArcTransition() {
        super();
    }
    
    public ArcTransition(Duration duration) {
        setDuration(duration);
    }
    
    public ArcTransition(Duration duration, Rectangle node) {
        this(duration);
        setNode(node);
    }
    
    // --- Queries ---------------------------------------------------------------------------
    
    /**
     * @return The fromWidth.
     */
    /*@ pure */ public double getFromWidth() {
        return fromWidth;
    }

    /**
     * @return The toWidth.
     */
    /*@ pure */ public double getToWidth() {
        return toWidth;
    }

    /**
     * @return The fromHeight.
     */
    /*@ pure */ public double getFromHeight() {
        return fromHeight;
    }

    /**
     * @return The toHeight.
     */
    /*@ pure */ public double getToHeight() {
        return toHeight;
    }

    /**
     * @return The node.
     */
    /*@ pure */  public Rectangle getNode() {
        return node;
    }

    /**
     * @return The duration.
     */
    /*@ pure */ public Duration getDuration() {
        return this.getCycleDuration();
    }
    
    // --- Setters ---------------------------------------------------------------------------

    /**
     * @param fromWidth The fromWidth to set.
     */
    public void setFromWidth(double fromWidth) {
        this.fromWidth = fromWidth;
    }

    /**
     * @param toWidth The toWidth to set.
     */
    public void setToWidth(double toWidth) {
        this.toWidth = toWidth;
    }

    /**
     * @param fromHeight The fromHeight to set.
     */
    public void setFromHeight(double fromHeight) {
        this.fromHeight = fromHeight;
    }

    /**
     * @param toHeight The toHeight to set.
     */
    public void setToHeight(double toHeight) {
        this.toHeight = toHeight;
    }

    /**
     * @param node The node to set.
     */
    public void setNode(Rectangle node) {
        this.node = node;
    }

    /**
     * @param duration The duration to set.
     */
    public void setDuration(Duration duration) {
        this.setCycleDuration(duration);
    }
    
    // --- Commands --------------------------------------------------------------------------
    
    /* (non-Javadoc)
     * @see javafx.animation.Transition#interpolate(double)
     */
    @Override
    //@ requires getNode() != null;
    protected void interpolate(double frac) {
        final double widthDiff = getToWidth() - getFromWidth();
        getNode().setArcWidth(getFromWidth() + widthDiff * frac);
        
        final double heightDiff = getToHeight() - getFromHeight();
        getNode().setArcHeight(getFromHeight() + heightDiff * frac);
    }
}
