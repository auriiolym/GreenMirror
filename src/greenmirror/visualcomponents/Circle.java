package greenmirror.visualcomponents;

import greenmirror.Node;
import greenmirror.Placement;
import greenmirror.VisualComponent;
import greenmirror.server.DoublePropertyTransition;

import java.util.HashMap;
import java.util.Map;

import javafx.animation.FadeTransition;
import javafx.animation.FillTransition;
import javafx.animation.ParallelTransition;
import javafx.animation.Transition;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.geometry.Point3D;
import javafx.scene.paint.Color;
import javafx.scene.paint.Paint;
import javafx.util.Duration;

/**
 * Extends javafx.scene.shape.Circle.
 */
public class Circle extends javafx.scene.shape.Circle implements VisualComponent {
    
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
                put("centerX", double.class);
                put("centerY", double.class);
                put("radius", double.class);
                put("style", String.class);
                put("opacity", double.class);
                put("fill", String.class);
            }
        };
    }

    /* (non-Javadoc)
     * @see greenmirror.VisualComponent#calculatePosition(greenmirror.Placement)
     */
    @Override
    public Point3D calculatePosition(Placement placement) {
        // TODO Auto-generated method stub
        return null;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#clone()
     */
    @Override
    /*@ pure */ public Circle clone() {
        // TODO Auto-generated method stub
        return null;
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
     * @see greenmirror.VisualComponent#setPositionWithMiddlePoint(javafx.geometry.Point3D)
     */
    @Override
    public void setPositionWithMiddlePoint(Point3D position) {
        // TODO Auto-generated method stub
        
    }
    

    public Circle withRadius(double value) {
        setRadius(value);
        return this;
    }
    
    public Circle withCenterX(double value) {
        setCenterX(value);
        return this;
    }
    
    public Circle adjustCenterX(double value) {
        setCenterX(value);
        appearanceUpdated("centerX", value);
        return this;
    }
    
    public Circle withCenterY(double value) {
        setCenterY(value);
        return this;
    }
    
    public Circle adjustCenterY(double value) {
        setCenterY(value);
        appearanceUpdated("centerY", value);
        return this;
    }
    
    public Circle withCenterPosition(double posX, double posY) {
        setCenterX(posX);
        setCenterY(posY);
        return this;
    }
    
    public Circle adjustCenterPosition(double posX, double posY) {
        setCenterX(posX);
        setCenterY(posY);
        appearanceUpdated("centerX", posX, "centerY", posY);
        return this;
    }
    
    public void setFill(String value) {
        setFill(Paint.valueOf(value));
    }
    
    public Circle withFill(Paint value) {
        setFill(value);
        return this;
    }
    
    public Circle withFill(String value) {
        setFill(value);
        return this;
    }
    
    public Circle adjustFill(Paint value) {
        setFill(value);
        appearanceUpdated("fill", String.valueOf(value));
        return this;
    }
    
    public Circle adjustFill(String value) {
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
    public Transition animateFromMap(Map<String, Object> map,
            ChangeType changeType, double animationDuration) {
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
            Circle newValues = this.clone();
            VisualComponent.setFromMap(newValues, map);

            // A change in centerX position (Circle specific).
            if (map.containsKey("centerX")) {
                transitions.getChildren().add(
                        new CenterXTransition(duration, this, newValues.getCenterX()));
            }
            // A change in centerY position (Rectangle specific).
            if (map.containsKey("centerY")) {
                transitions.getChildren().add(
                        new CenterYTransition(duration, this, newValues.getCenterY()));
            }
            // A change in the fill (applies to Shape JavaFX nodes).
            if (map.containsKey("fill")) {
                FillTransition fiTr = new FillTransition(duration, this);
                fiTr.setToValue(Color.valueOf(newValues.getFill().toString()));
                transitions.getChildren().add(fiTr);
            }
        }
        return null;
    }
    
    /**
     * A <tt>Transition</tt> class that animates the x value of a <tt>Rectangle</tt>.
     * 
     * @author Karim El Assal
     */
    public static class CenterXTransition extends DoublePropertyTransition<Circle> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected CenterXTransition(Duration duration, Circle node, Double toValue) {
            super(duration, node, toValue);
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#getPropertyValue()
         */
        @Override
        protected Double getPropertyValue() {
            return getNode().getCenterX();
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#setPropertyValue(java.lang.Double)
         */
        @Override
        protected void setPropertyValue(Double value) {
            getNode().setCenterX(value);
        }
    }
    
    /**
     * A <tt>Transition</tt> class that animates the x value of a <tt>Rectangle</tt>.
     * 
     * @author Karim El Assal
     */
    public static class CenterYTransition extends DoublePropertyTransition<Circle> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected CenterYTransition(Duration duration, Circle node, Double toValue) {
            super(duration, node, toValue);
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#getPropertyValue()
         */
        @Override
        protected Double getPropertyValue() {
            return getNode().getCenterY();
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#setPropertyValue(java.lang.Double)
         */
        @Override
        protected void setPropertyValue(Double value) {
            getNode().setCenterY(value);
        }
    }
}