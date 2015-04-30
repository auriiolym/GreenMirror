package greenmirror.visualcomponents;

import greenmirror.Node;
import greenmirror.Placement;
import greenmirror.VisualComponent;
import greenmirror.server.ArcTransition;
import greenmirror.server.PositionTransition;

import java.util.HashMap;
import java.util.Map;

import javafx.animation.FadeTransition;
import javafx.animation.ParallelTransition;
import javafx.animation.RotateTransition;
import javafx.animation.Transition;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.geometry.Point3D;
import javafx.util.Duration;

// Extends javafx.scene.shape.Rectangle.
/**
 * The extension of JavaFX's <tt>Rectangle</tt>. It adds features needed by the visualizer.
 * 
 * @author Karim El Assal
 */
public class Rectangle extends javafx.scene.shape.Rectangle implements VisualComponent {

    // -- Instance variables -----------------------------------------------------------------

    // -- Constructors -----------------------------------------------------------------------

    // -- Queries ----------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see greenmirror.VisualComponent#getGreenMirrorNode()
     */
    @Override
    /*@ pure */ public Node getGreenMirrorNode() {
        return (Node) getProperties().get("GreenMirrorNode");
    }

    /* (non-Javadoc)
     * @see greenmirror.VisualComponent#calculatePosition(greenmirror.Placement)
     */
    @Override
    //@ requires placement != null;
    /*@ pure */ public Point3D calculatePosition(Placement placement) {
        // TODO Auto-generated method stub
        return null;
    }
    
    /* (non-Javadoc)
     * @see greenmirror.VisualComponent#toMap()
     */
    @Override
    /*@ pure */ public Map<String, Object> toMap() {
        Map<String, Object> map = new HashMap<>();
        map.put("type", "rectangle");
        map.put("x", this.getX());
        map.put("y", this.getY());
        map.put("width", this.getWidth());
        map.put("height", this.getHeight());
        map.put("arcWidth", this.getArcWidth());
        map.put("arcHeight", this.getArcHeight());
        map.put("style", this.getStyle());
        map.put("opacity", this.getOpacity());
        map.put("rotate", this.getRotate());
        return map;
    }

    /* (non-Javadoc)
     * @see greenmirror.VisualComponent#getChangableProperties()
     */
    @Override
    public Map<String, Class<?>> getChangableProperties() {
        return new HashMap<String, Class<?>>() {
            {
                put("x", double.class);
                put("y", double.class);
                put("width", double.class);
                put("height", double.class);
                put("arcWidth", double.class);
                put("arcHeight", double.class);
                put("style", String.class);
                put("opacity", double.class);
                put("rotate", double.class);
            }
        };
    }
    
    
    // -- Setters ----------------------------------------------------------------------------
    
    /* (non-Javadoc)
     * @see greenmirror.VisualComponent#setPositionWithMiddlePosition(greenmirror.Position)
     */
    @Override
    public void setGreenMirrorNode(Node node) {
        getProperties().put("GreenMirrorNode", node);
    }

    /* (non-Javadoc)
     * @see greenmirror.VisualComponent#setPositionWithMiddlePosition(javafx.geometry.Point3D)
     */
    @Override
    public void setPositionWithMiddlePoint(Point3D point) {
        // TODO Auto-generated method stub
    }
    
    
    public Rectangle withWidth(double value) {
        setWidth(value);
        return this;
    }
    
    public Rectangle withHeight(double value) {
        setHeight(value);
        return this;
    }
    
    public Rectangle withSize(double width, double height) {
        setWidth(width);
        setHeight(height);
        return this;
    }
    
    public Rectangle withX(double value) {
        setX(value);
        return this;
    }
    
    public Rectangle adjustX(double value) {
        setX(value);
        appearanceUpdated("x", value);
        return this;
    }
    
    public Rectangle withY(double value) {
        setY(value);
        return this;
    }
    
    public Rectangle adjustY(double value) {
        setY(value);
        appearanceUpdated("y", value);
        return this;
    }
    
    public Rectangle withPosition(double posX, double posY) {
        setX(posX);
        setY(posY);
        return this;
    }
    
    public Rectangle adjustPosition(double posX, double posY) {
        adjustX(posX);
        adjustY(posY);
        return this;
    }
    
    public Rectangle withRotate(double value) {
        setRotate(value);
        return this;
    }
    
    public Rectangle adjustRotate(double value) {
        setRotate(value);
        appearanceUpdated("rotate", value);
        return this;
    }
    
    public Rectangle withArcHeight(double value) {
        setArcHeight(value);
        return this;
    }
    
    public Rectangle adjustArcHeight(double value) {
        setArcHeight(value);
        appearanceUpdated("arcHeight", value);
        return this;
    }
    
    public Rectangle withArcWidth(double value) {
        setArcWidth(value);
        return this;
    }
    
    public Rectangle adjustArcWidth(double value) {
        setArcWidth(value);
        appearanceUpdated("arcWidth", value);
        return this;
    }
    
    public Rectangle withArcs(double width, double height) {
        setArcWidth(width);
        setArcHeight(height);
        return this;
    }
    
    public Rectangle adjustArcs(double width, double height) {
        adjustArcWidth(width);
        adjustArcHeight(height); 
        return this;
    }

    
    // -- Commands ---------------------------------------------------------------------------

    public Transition animateFromMap(Map<String, Object> map, ChangeType change,
                                double animationDuration) {
        Duration duration = Duration.millis(animationDuration);
        switch (change) {
        default: case ADD_NODE:
            
            // Set all values except opacity.
            final double opacity = Double.valueOf(String.valueOf(map.get("opacity")));
            map.remove("opacity");
            VisualComponent.setFromMap(this, map);
            
            // Make FX node 'appear'.
            this.setOpacity(0);
            this.setMouseTransparent(true);
            FadeTransition transition = new FadeTransition(duration);
            transition.setNode(this);
            transition.setFromValue(0);
            transition.setToValue(opacity);
            transition.setOnFinished(new EventHandler<ActionEvent>() {
                @Override
                public void handle(ActionEvent event) {
                    transition.getNode().setMouseTransparent(false);
                }
            });
            
            return transition;
            
        case NORMAL:
            ParallelTransition transitions = new ParallelTransition();
            
            // Check every value and if it has changed. If so, animate the change.
            // It's easier to do it like this, so we do it like this.
            Rectangle newValues = this.clone();
            VisualComponent.setFromMap(newValues, map);
            
            if (newValues.getX() != this.getX()) {
                PositionTransition poTr = new PositionTransition(duration);
                poTr.setNode(this);
                poTr.setFromX(this.getX());
                poTr.setToX(newValues.getX());
                transitions.getChildren().add(poTr);
            }
            if (newValues.getY() != this.getY()) {
                PositionTransition poTr = new PositionTransition(duration);
                poTr.setNode(this);
                poTr.setFromY(this.getY());
                poTr.setToY(newValues.getY());
                transitions.getChildren().add(poTr);
            }
            
            // A change in rotation.
            if (newValues.getRotate() != this.getRotate()) {
                RotateTransition roTr = new RotateTransition(duration);
                roTr.setNode(this);
                roTr.setFromAngle(this.getRotate());
                roTr.setToAngle(newValues.getRotate());
                transitions.getChildren().add(roTr);
            }
            // A change in arcs.
            if (newValues.getArcHeight() != this.getArcHeight()
              || newValues.getArcWidth() != this.getArcWidth()) {
                ArcTransition arTr = new ArcTransition(duration);
                arTr.setNode(this);
                arTr.setFromHeight(this.getArcHeight());
                arTr.setToHeight(newValues.getArcHeight());
                arTr.setFromWidth(this.getArcWidth());
                arTr.setToWidth(newValues.getArcWidth());
                transitions.getChildren().add(arTr);
            }
            return transitions;
        }
    }

    /* (non-Javadoc)
     * @see greenmirror.VisualComponent#clone()
     */
    @Override
    public Rectangle clone() {
        Rectangle cloned = new Rectangle();
        VisualComponent.setFromMap(cloned, this.toMap());
        return cloned;
    }
}