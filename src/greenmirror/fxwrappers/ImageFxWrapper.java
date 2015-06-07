package greenmirror.fxwrappers;

import greenmirror.FxPropertyWrapper;
import greenmirror.FxWrapper;
import greenmirror.Placement;
import greenmirror.fxpropertywrappers.BooleanFxProperty;
import greenmirror.fxpropertywrappers.DoubleFxProperty;
import greenmirror.fxpropertywrappers.ImageFxProperty;
import greenmirror.server.AbstractTransition;
import greenmirror.server.DoublePropertyTransition;

import java.io.BufferedInputStream;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLConnection;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.annotation.NonNull;

import javafx.animation.ParallelTransition;
import javafx.animation.Transition;
import javafx.geometry.Point3D;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.util.Duration;

/**
 * 
 * @author Karim El Assal
 */
public class ImageFxWrapper extends FxWrapper {

    // -- Instance variables -----------------------------------------------------------------
    
    private Double posX;
    private Double posY;
    private Double fitWidth;
    private Double fitHeight;
    private Image image;
    private Boolean preserveRatio = false;
    

    // -- Constructors -----------------------------------------------------------------------

    // -- Queries ----------------------------------------------------------------------------

    
    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#getChangableProperties()
     */
    @Override
    protected List<FxPropertyWrapper> getAnimatableProperties() {
        final List<FxPropertyWrapper> supersAnimatableProperties = super.getAnimatableProperties();
        return new ArrayList<FxPropertyWrapper>() {
            {
                addAll(supersAnimatableProperties);
                add(new DoubleFxProperty("x"));
                add(new DoubleFxProperty("y"));
                add(new DoubleFxProperty("fitWidth"));
                add(new DoubleFxProperty("fitHeight"));
                add(new ImageFxProperty("image"));
            }
        };
    }
    
    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#getChangableProperties()
     */
    @Override
    protected List<FxPropertyWrapper> getChangableProperties() {
        final List<FxPropertyWrapper> supersChangableProperties = super.getChangableProperties();
        return new ArrayList<FxPropertyWrapper>() {
            {
                addAll(supersChangableProperties);
                addAll(getAnimatableProperties());
                add(new BooleanFxProperty("preserveRatio"));
            }
        };
    }
    
    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#getFxNode()
     */
    @Override
    /*@ pure */ public javafx.scene.image.ImageView getFxNode() {
        return (javafx.scene.image.ImageView) super.getFxNode();
    }
    
    

    /**
     * @return The x coordinate.
     */
    /*@ pure */ public Double getX() {
        return posX;
    }

    /**
     * @return The y coordinate.
     */
    /*@ pure */ public Double getY() {
        return posY;
    }

    /**
     * @return The fitWidth.
     */
    /*@ pure */ public Double getFitWidth() {
        return fitWidth;
    }

    /**
     * @return The fitHeight.
     */
    /*@ pure */ public Double getFitHeight() {
        return fitHeight;
    }

    /**
     * @return The image.
     */
    /*@ pure */ public Image getImage() {
        return image;
    }

    /**
     * @return The preserveRatio.
     */
    /*@ pure */ public Boolean isPreserveRatio() {
        return preserveRatio;
    }

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#isPositionSet()
     */
    @Override
    /*@ pure */ public boolean isPositionSet() {
        return getX() != null && getY() != null;
    }
    
    
    // -- Setters ----------------------------------------------------------------------------

    /**
     * @param value The posX to set.
     */
    //@ ensures getX().doubleValue() == value;
    //@ ensures \result == this;
    public ImageFxWrapper setX(double value) {
        this.posX = value;
        setChanged();
        notifyObservers();
        return this;
    }

    /**
     * @param value The posY to set.
     */
    //@ ensures getY().doubleValue() == value;
    //@ ensures \result == this;
    public ImageFxWrapper setY(double value) {
        this.posY = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    /**
     * @param posX The posX to set.
     * @param posY The posY to set.
     * @return     <code>this</code>
     */
    //@ ensures getX().doubleValue() == posX && getY().doubleValue() == posY;
    //@ ensures \result == this;
    public ImageFxWrapper setPosition(double posX, double posY) {
        this.posX = posX;
        this.posY = posY;
        setChanged();
        notifyObservers();
        return this;
    }

    /**
     * @param fitWidth The fitWidth to set.
     */
    //@ ensures getFitWidth().doubleValue() == value;
    //@ ensures \result == this;
    public ImageFxWrapper setFitWidth(double fitWidth) {
        this.fitWidth = fitWidth;
        setChanged();
        notifyObservers();
        return this;
    }

    /**
     * @param value The fitHeight to set.
     */
    //@ ensures getFitHeight().doubleValue() == value;
    //@ ensures \result == this;
    public ImageFxWrapper setFitHeight(double value) {
        this.fitHeight = value;
        setChanged();
        notifyObservers();
        return this;
    }

    /**
     * @param value The image to set.
     */
    //@ ensures getImage() == value;
    //@ ensures \result == this;
    public ImageFxWrapper setImage(Image value) {
        if (!(value instanceof MyImage) && value != null) {
            throw new IllegalArgumentException("Image has to be of type StoredBytesImage.");
        }
        this.image = value;
        setChanged();
        notifyObservers();
        return this;
    }

    /**
     * @param filePath The image to set.
     */
    //@ ensures \result == this;
    public ImageFxWrapper setImageFromFile(String filePath) {
        
        // Get InputStream of the file.
        InputStream inputStream;
        if ((inputStream = ImageFxWrapper.class.getResourceAsStream(filePath)) == null) {
            try {
                inputStream = new FileInputStream(filePath);
            } catch (FileNotFoundException e) {
                throw new IllegalArgumentException("File " + filePath + " could not be found.");
            }
        }
        final byte[] bytes = MyImage.readBytes(inputStream);
        final MyImage img = new MyImage(new BufferedInputStream(inputStream));
        img.setBytes(bytes);
        return setImage(img);
    }
    
    public ImageFxWrapper setImageFromUrl(@NonNull String url) {
        try {
            final URLConnection connection = new URL(url).openConnection();
            connection.connect();
            final InputStream inputStream = connection.getInputStream();
            final byte[] bytes = MyImage.readBytes(inputStream);
            final MyImage image = new MyImage(inputStream);
            image.setBytes(bytes);
            setImage(image);
            
            if (bytes == null || bytes.length == 0) {
                throw new IllegalArgumentException("Unable to retrieve image from " + url);
            }
            
        } catch (MalformedURLException e) {
            throw new IllegalArgumentException("The following URL is malformed: " + url);
        } catch (IOException e) {
            throw new IllegalArgumentException("This went wrong with opening url " + url 
                    + ": " + e.getMessage());
        }
        return this;
    }

    /**
     * @param value The preserveRatio to set.
     */
    //@ ensures isPreserveRatio() == value;
    //@ ensures \result == this;
    public ImageFxWrapper setPreserveRatio(boolean value) {
        this.preserveRatio = value;
        setChanged();
        notifyObservers();
        return this;
    }    
    public Transition animateX(double value, Duration duration) {
        return new XTransition(duration, getFxNode(), value);
    }
    
    public Transition animateY(double value, Duration duration) {
        return new YTransition(duration, getFxNode(), value);
    }
    
    public Transition animateFitWidth(double value, Duration duration) {
        return new FitWidthTransition(duration, getFxNode(), value);
    }
    
    public Transition animateFitHeight(double value, Duration duration) {
        return new FitHeightTransition(duration, getFxNode(), value);
    }
    
    public Transition animateImage(Image value, Duration duration) {
        return new ImageTransition(duration, getFxNode(), value);
    }
    

    // -- Class usage ------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#clone()
     */
    @Override @NonNull
    public ImageFxWrapper clone() {
        ImageFxWrapper rect = new ImageFxWrapper();
        rect.setFromMap(this.toMap());
        return rect;
    }
    
    /**
     * Determines the size of the node for use with the calculations of placements.
     * If the fitWidth is set, that value will be returned as the width. The height is determined
     * on the basis of the value of {@link #isPreserveRatio()}. If fitWidth is not set, it tries
     * the same with fitHeight. If both aren't set, the width and height of the set image are
     * returned.
     * 
     * @return an array with the width on the first index and the height on the second
     */
    //@ requires getImage() != null;
    //@ ensures \result.length == 2;
    @NonNull
    private double[] determineSize() {
        final double[] size = new double[2];
        final Double fitWidth = getFitWidth();
        final Double fitHeight = getFitHeight();
        final double imageWidth = getImage().getWidth();
        final double imageHeight = getImage().getHeight();
        final double ratio = imageWidth / imageHeight;
        
        if (fitWidth != null) {
            size[0] = fitWidth;
            if (isPreserveRatio()) {
                size[1] = fitWidth / ratio;
            } else {
                size[1] = imageHeight;
            }
        } else if (fitHeight != null) {
            size[1] = fitHeight;
            if (isPreserveRatio()) {
                size[0] = fitHeight * ratio;
            } else {
                size[0] = imageWidth;
            }
        } else {
            size[0] = imageWidth;
            size[1] = imageHeight;
        }
        
        return size;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#calculatePoint(greenmirror.Placement)
     */
    @Override
    /*@ pure */ public Point3D calculatePoint(Placement placement) {
        final double[] size = determineSize();
        
        return new Point3D(getX(), getY(), 0)
            .add(FxWrapper.calculatePointOnRectangle(size[0], size[1], placement));
    }

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#createFxNode()
     */
    @Override
    public void createFxNode() {
        setFxNode(new ImageView(getImage()));
    }

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#animateToMiddlePoint(javafx.geometry.Point3D, 
     *                                          javafx.util.Duration)
     */
    @Override
    public Transition animateToMiddlePoint(Point3D middlePoint, Duration duration) {
        Point3D coord = calculateOriginCoordinates(middlePoint);
        return new ParallelTransition(
                new XTransition(duration, getFxNode(), coord.getX()),
                new YTransition(duration, getFxNode(), coord.getY()));
    }

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#calculateCoordinates(javafx.geometry.Point3D)
     */
    @Override
    protected Point3D calculateOriginCoordinates(Point3D middlePoint) {
        final double[] size = determineSize();
        
        return new Point3D(middlePoint.getX() - size[0] / 2, 
                           middlePoint.getY() - size[1] / 2, 0);
    }

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#setToPositionWithMiddlePoint(javafx.geometry.Point3D)
     */
    @Override
    public void setToPositionWithMiddlePoint(Point3D middlePoint) {
        final Point3D coord = calculateOriginCoordinates(middlePoint);
        setX(coord.getX());
        setY(coord.getY());
    }

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#setFxToPositionWithMiddlePoint(javafx.geometry.Point3D)
     */
    @Override
    public void setFxToPositionWithMiddlePoint(Point3D middlePoint) {
        Point3D coord = calculateOriginCoordinates(middlePoint);
        getFxNode().setX(coord.getX());
        getFxNode().setY(coord.getY());
    }

    

    /**
     * A <code>Transition</code> class that animates the x value of an <code>ImageView</code>.
     * 
     * @author Karim El Assal
     */
    public static class XTransition extends DoublePropertyTransition<ImageView> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoublePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected XTransition(Duration duration, ImageView node, Double toValue) {
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
     * A <code>Transition</code> class that animates the y value of an <code>ImageView</code>.
     * 
     * @author Karim El Assal
     */
    public static class YTransition extends DoublePropertyTransition<ImageView> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoublePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected YTransition(Duration duration, ImageView node, Double toValue) {
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
     * A <code>Transition</code> class that animates the change of the width.
     * 
     * @author Karim El Assal
     */
    public static class FitWidthTransition extends DoublePropertyTransition<ImageView> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoublePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected FitWidthTransition(Duration duration, ImageView node, Double toValue) {
            super(duration, node, toValue);
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#getPropertyValue()
         */
        @Override
        protected Double getPropertyValue() {
            return getNode().getFitWidth();
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#setPropertyValue(java.lang.Double)
         */
        @Override
        protected void setPropertyValue(Double value) {
            getNode().setFitWidth(value);
        }
    }
    
    /**
     * A <code>Transition</code> class that animates the change of the height.
     * 
     * @author Karim El Assal
     */
    public static class FitHeightTransition extends DoublePropertyTransition<ImageView> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoublePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
         */
        protected FitHeightTransition(Duration duration, ImageView node, Double toValue) {
            super(duration, node, toValue);
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#getPropertyValue()
         */
        @Override
        protected Double getPropertyValue() {
            return getNode().getFitHeight();
        }

        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#setPropertyValue(java.lang.Double)
         */
        @Override
        protected void setPropertyValue(Double value) {
            getNode().setFitHeight(value);
        }
    }
    
    
    public static class ImageTransition extends AbstractTransition<ImageView, Image> {
        
        // --- Constructors -------------------------------
        
        public ImageTransition(Duration duration, ImageView node, Image toValue) {
            super(duration, node, toValue);
        }
        
        
        // --- Setters ---------------------------------------------------------------------------
        
        // --- Commands --------------------------------------------------------------------------
        
        /* (non-Javadoc)
         * @see javafx.animation.Transition#interpolate(double)
         */
        @Override
        //@ requires getNode() != null;
        protected void interpolate(final double frac) {
            if (getFromValue() == null) {
                setFromValue(getNode().getImage());
            }

            final double part1Frac = frac * 2;
            final double part2Frac = (frac - 0.5) * 2;
            // First half: only change the opacity to 0.
            if (frac <= 0.5) {
                if (getNode().getImage() != getFromValue()) {
                    getNode().setImage(getFromValue());
                }
                final double valueDiff = 0 - getOriginalOpacity();
                getNode().setOpacity(getOriginalOpacity() + valueDiff * part1Frac);
             
            // Second half: change the opacity back to the original and set the new image.
            } else {
                if (getNode().getImage() != getToValue()) {
                    getNode().setImage(getToValue());
                }
                final Double valueDiff = getOriginalOpacity() - 0;
                getNode().setOpacity(0 + valueDiff * part2Frac);
            }
        }
    }
}
