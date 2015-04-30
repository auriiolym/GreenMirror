package greenmirror.server;

import javafx.animation.Transition;
import javafx.scene.shape.Rectangle;
import javafx.util.Duration;

/**
 * A <tt>Transition</tt> class that animates the change of the position.
 * 
 * @author Karim El Assal
 */
public class PositionTransition extends Transition {

    // --- Instance variables ----------------------------------------------------------------

    private double fromX;
    
    private double toX;
    
    private double fromY;
    
    private double toY;
    
    private Rectangle node;
    
    // --- Constructors ----------------------------------------------------------------------
    
    public PositionTransition() {
        super();
    }
    
    public PositionTransition(Duration duration) {
        setDuration(duration);
    }
    
    public PositionTransition(Duration duration, Rectangle node) {
        this(duration);
        setNode(node);
    }
    
    // --- Queries ---------------------------------------------------------------------------
    
    /**
     * @return The fromX.
     */
    /*@ pure */ public double getFromX() {
        return fromX;
    }

    /**
     * @return The toX.
     */
    /*@ pure */ public double getToX() {
        return toX;
    }

    /**
     * @return The fromY.
     */
    /*@ pure */ public double getFromY() {
        return fromY;
    }

    /**
     * @return The toY.
     */
    /*@ pure */ public double getToY() {
        return toY;
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
     * @param fromX The fromX to set.
     */
    public void setFromX(double fromX) {
        this.fromX = fromX;
    }

    /**
     * @param toX The toX to set.
     */
    public void setToX(double toX) {
        this.toX = toX;
    }

    /**
     * @param fromY The fromY to set.
     */
    public void setFromY(double fromY) {
        this.fromY = fromY;
    }

    /**
     * @param toY The toY to set.
     */
    public void setToY(double toY) {
        this.toY = toY;
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
        if (getToX() != getFromX()) {
            final double XDiff = getToX() - getFromX();
            getNode().setX(getFromX() + XDiff * frac);
        }
        if (getToY() != getFromY()) {
            final double YDiff = getToY() - getFromY();
            getNode().setY(getFromY() + YDiff * frac);
        }
    }
}
