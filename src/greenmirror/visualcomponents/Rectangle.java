package greenmirror.visualcomponents;

import greenmirror.Node;
import greenmirror.Placement;
import greenmirror.VisualComponent;
import greenmirror.server.DoublePropertyTransition;

import java.util.HashMap;
import java.util.Map;
import java.util.Random;

import javafx.animation.FadeTransition;
import javafx.animation.FillTransition;
import javafx.animation.ParallelTransition;
import javafx.animation.RotateTransition;
import javafx.animation.Transition;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.geometry.Point3D;
import javafx.scene.paint.Color;
import javafx.scene.paint.Paint;
import javafx.util.Duration;

// Extends javafx.scene.shape.Rectangle implements VisualComponent.
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
                put("fill", String.class);
            }
        };
    }

    /* (non-Javadoc)
     * @see greenmirror.VisualComponent#calculatePosition(greenmirror.Placement)
     */
    @Override
    //@ requires placement != null;
    /*@ pure */ public Point3D calculatePosition(Placement placement) {
        double posX;
        double posY;
        
        switch (placement) {
        case MIDDLE:
            posX = getX() + getWidth() / 2;
            posY = getY() + getHeight() / 2;
            break;
        case CUSTOM:
            posX = getX() + getWidth() / 2 + placement.getRelativePosition().getX();
            posY = getY() + getHeight() / 2 + placement.getRelativePosition().getY();
            break;
        case EDGE_LEFT_MIDDLE:
            posX = getX();
            posY = getY() + getHeight() / 2;
            break;
        case EDGE_RIGHT_MIDDLE:
            posX = getX() + getWidth();
            posY = getY() + getHeight() / 2;
            break;
        case RANDOM:
            Random random = new Random();
            double minX = getX();
            double maxX = getX() + getWidth();
            double minY = getY();
            double maxY = getY() + getHeight();

            posX = minX + random.nextDouble() * (maxX - minX);
            posY = minY + random.nextDouble() * (maxY - minY);
            break;
        case NONE: default:
            return null;
        }
        return new Point3D(posX, posY, 0);
    }

    /* (non-Javadoc)
     * @see greenmirror.VisualComponent#clone()
     */
    @Override
    /*@ pure */ public Rectangle clone() {
        Rectangle cloned = new Rectangle();
        VisualComponent.setFromMap(cloned, this.toMap());
        return cloned;
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
        setX(posX);
        setY(posY);
        appearanceUpdated("x", posX, "y", posY);
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
        setArcWidth(width);
        setArcHeight(height);
        appearanceUpdated("arcWidth", width, "arcHeight", height); 
        return this;
    }
    
    public void setFill(String value) {
        setFill(Paint.valueOf(value));
    }
    
    public Rectangle withFill(Paint value) {
        setFill(value);
        return this;
    }
    
    public Rectangle withFill(String value) {
        setFill(value);
        return this;
    }
    
    public Rectangle adjustFill(Paint value) {
        setFill(value);
        appearanceUpdated("fill", String.valueOf(value));
        return this;
    }
    
    public Rectangle adjustFill(String value) {
        setFill(value);
        appearanceUpdated("fill", value);
        return this;
    }

    
    // -- Commands ---------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see greenmirror.VisualComponent#animateFromMap(java.util.Map, 
     *                              greenmirror.VisualComponent.ChangeType, double)
     */
    @Override
    public Transition animateFromMap(Map<String, Object> map, ChangeType changeType,
                                double animationDuration) {
        Duration duration = Duration.millis(animationDuration);
        switch (changeType) {
        default: case ADD_NODE:
            
            // Set all values except opacity.
            final double opacity = Double.valueOf(String.valueOf(map.get("opacity")));
            map.remove("opacity");
            VisualComponent.setFromMap(this, map);
            
            // Make FX node 'appear'.
            this.setOpacity(0);
            this.setMouseTransparent(true);
            FadeTransition transition = new FadeTransition(duration, this);
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
            
            // Check per property if we received a change.
            // The newValues variable is used so the properties are already parsed.
            Rectangle newValues = this.clone();
            VisualComponent.setFromMap(newValues, map);

            // A change in x position (Rectangle specific).
            if (map.containsKey("x")) {
                transitions.getChildren().add(
                        new XTransition(duration, this, newValues.getX()));
            }
            // A change in y position (Rectangle specific).
            if (map.containsKey("y")) {
                transitions.getChildren().add(
                        new YTransition(duration, this, newValues.getY()));
            }
            // A change in arc width (Rectangle specific).
            if (map.containsKey("arcWidth")) {
                transitions.getChildren().add(
                        new ArcWidthTransition(duration, this, newValues.getArcWidth()));
            }
            // A change in arc height (Rectangle specific).
            if (map.containsKey("arcHeight")) {
                transitions.getChildren().add(
                        new ArcHeightTransition(duration, this, newValues.getArcHeight()));
            }
            // A change in rotation (applies to all JavaFX Nodes).
            if (map.containsKey("rotate")) {
                RotateTransition roTr = new RotateTransition(duration, this);
                roTr.setToAngle(newValues.getRotate());
                transitions.getChildren().add(roTr);
            }
            // A change in the fill (applies to Shape JavaFX nodes).
            if (map.containsKey("fill")) {
                FillTransition fiTr = new FillTransition(duration, this);
                fiTr.setToValue(Color.valueOf(newValues.getFill().toString()));
                transitions.getChildren().add(fiTr);
            }
            
            //TODO: add opacity, width and height transition.
            return transitions;
        }
    }
    
    /**
     * A <tt>Transition</tt> class that animates the x value of a <tt>Rectangle</tt>.
     * 
     * @author Karim El Assal
     */
    public static class XTransition extends DoublePropertyTransition<Rectangle> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected XTransition(Duration duration, Rectangle node, Double toValue) {
            super(duration, node, toValue);
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#getPropertyValue()
         */
        @Override
        protected Double getPropertyValue() {
            return getNode().getX();
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#setPropertyValue(java.lang.Double)
         */
        @Override
        protected void setPropertyValue(Double value) {
            getNode().setX(value);
        }
    }
    
    /**
     * A <tt>Transition</tt> class that animates the y value of a <tt>Rectangle</tt>.
     * 
     * @author Karim El Assal
     */
    public static class YTransition extends DoublePropertyTransition<Rectangle> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected YTransition(Duration duration, Rectangle node, Double toValue) {
            super(duration, node, toValue);
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#getPropertyValue()
         */
        @Override
        protected Double getPropertyValue() {
            return getNode().getY();
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#setPropertyValue(java.lang.Double)
         */
        @Override
        protected void setPropertyValue(Double value) {
            getNode().setY(value);
        }
    }
    
    /**
     * A <tt>Transition</tt> class that animates the change of the arc height.
     * 
     * @author Karim El Assal
     */
    public static class ArcHeightTransition extends DoublePropertyTransition<Rectangle> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected ArcHeightTransition(Duration duration, Rectangle node, Double toValue) {
            super(duration, node, toValue);
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#getPropertyValue()
         */
        @Override
        protected Double getPropertyValue() {
            return getNode().getArcHeight();
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#setPropertyValue(java.lang.Double)
         */
        @Override
        protected void setPropertyValue(Double value) {
            getNode().setArcHeight(value);
        }
    }
    
    /**
     * A <tt>Transition</tt> class that animates the change of the arc width.
     * 
     * @author Karim El Assal
     */
    public static class ArcWidthTransition extends DoublePropertyTransition<Rectangle> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected ArcWidthTransition(Duration duration, Rectangle node, Double toValue) {
            super(duration, node, toValue);
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#getPropertyValue()
         */
        @Override
        protected Double getPropertyValue() {
            return getNode().getArcWidth();
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#setPropertyValue(java.lang.Double)
         */
        @Override
        protected void setPropertyValue(Double value) {
            getNode().setArcWidth(value);
        }
    }
}