package greenmirror.fxwrappers;

import greenmirror.FxWrapper;
import greenmirror.Placement;
import greenmirror.fxpropertytypes.BooleanFxProperty;
import greenmirror.fxpropertytypes.DoubleFxProperty;
import greenmirror.fxpropertytypes.FxPropertyWrapper;
import greenmirror.fxpropertytypes.ImageFxProperty;
import greenmirror.server.AbstractTransition;
import greenmirror.server.DoublePropertyTransition;

import java.io.BufferedInputStream;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;

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
     * @return     <tt>this</tt>
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
        if (!(value instanceof MyImage)) {
            throw new IllegalArgumentException("Image has to be of type MyImage.");
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
    
    public ImageFxWrapper setImageFromUrl(String url) {
        try {
            final InputStream inputStream = new URL(url).openConnection().getInputStream();
            final byte[] bytes = MyImage.readBytes(inputStream);
            final MyImage image = new MyImage(inputStream);
            image.setBytes(bytes);
            setImage(image);
            
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

    public static void main(String[] args) {
        String[] urls = new String[]{
                "img.png",
                "/img.png",
                "testcases/img.png",
                "/testcases/img.png",
        };
        for (String url : urls) {
            try {
                new FileInputStream(url);
                System.out.println("FileInputStream success: " + url);
            } catch (Exception e) {
                System.out.println("fail");
            }
            
            try {
                new Image(url);
                System.out.println("Image success: " + url);
            } catch (Exception e) {
                System.out.println("fail");
            }
            
            try {
                if (ImageFxWrapper.class.getResourceAsStream(url) == null) {
                    throw new NullPointerException();
                }
                System.out.println("class.getResourceAsStream success: " + url);
            } catch (Exception e) {
                System.out.println("fail");
            }
            
            try {
                if (ImageFxWrapper.class.getResourceAsStream(url) == null) {
                    throw new NullPointerException();
                }
                ImageFxWrapper.class.getClassLoader().getResourceAsStream(url);
                System.out.println("class.getClassLoader().getResourceAsStream success: " + url);
            } catch (Exception e) {
                System.out.println("fail");
            }
            System.out.println();
        }
        
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
    @Override
    public ImageFxWrapper clone() {
        ImageFxWrapper rect = new ImageFxWrapper();
        rect.setFromMap(this.toMap());
        return rect;
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#calculatePoint(greenmirror.Placement)
     */
    @Override
    /*@ pure */ public Point3D calculatePoint(Placement placement) {
        return new Point3D(getX(), getY(), 0)
            .add(FxWrapper.calculatePointOnRectangle(getFitWidth(), getFitHeight(), placement));
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
        Point3D coord = calculateCoordinates(middlePoint);
        return new ParallelTransition(
                new XTransition(duration, getFxNode(), coord.getX()),
                new YTransition(duration, getFxNode(), coord.getY()));
    }

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#calculateCoordinates(javafx.geometry.Point3D)
     */
    @Override
    protected Point3D calculateCoordinates(Point3D middlePoint) {
        return new Point3D(middlePoint.getX() - getFitWidth() / 2, 
                           middlePoint.getY() - getFitHeight() / 2, 0);
    }

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#setToPositionWithMiddlePoint(javafx.geometry.Point3D)
     */
    @Override
    public void setToPositionWithMiddlePoint(Point3D middlePoint) {
        Point3D coord = calculateCoordinates(middlePoint);
        setX(coord.getX());
        setY(coord.getY());
    }

    /* (non-Javadoc)
     * @see greenmirror.FxWrapper#setFxToPositionWithMiddlePoint(javafx.geometry.Point3D)
     */
    @Override
    public void setFxToPositionWithMiddlePoint(Point3D middlePoint) {
        Point3D coord = calculateCoordinates(middlePoint);
        getFxNode().setX(coord.getX());
        getFxNode().setY(coord.getY());
    }

    

    /**
     * A <tt>Transition</tt> class that animates the x value of an <tt>ImageView</tt>.
     * 
     * @author Karim El Assal
     */
    public static class XTransition extends DoublePropertyTransition<ImageView> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
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
     * A <tt>Transition</tt> class that animates the y value of an <tt>ImageView</tt>.
     * 
     * @author Karim El Assal
     */
    public static class YTransition extends DoublePropertyTransition<ImageView> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
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
     * A <tt>Transition</tt> class that animates the change of the width.
     * 
     * @author Karim El Assal
     */
    public static class FitWidthTransition extends DoublePropertyTransition<ImageView> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
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
     * A <tt>Transition</tt> class that animates the change of the height.
     * 
     * @author Karim El Assal
     */
    public static class FitHeightTransition extends DoublePropertyTransition<ImageView> {
        
        /* (non-Javadoc)
         * @see greenmirror.server.DoublePropertyTransition#
         *     DoubleePropertyTransition(javafx.util.Duration, javafx.scene.Node, java.lang.Double)s
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

        // --- Instance variables -------------------------

        private Double originalOpacity;
        
        
        // --- Constructors -------------------------------
        
        public ImageTransition(Duration duration, ImageView node, Image toValue) {
            super(duration, node, toValue);
        }
        
        
        // --- Queries ------------------------------------
        
        /**
         * @return The node's originalOpacity.
         */
        public double getOriginalOpacity() {
            if (originalOpacity == null) {
                originalOpacity = getNode().getOpacity();
            }
            return originalOpacity;
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
