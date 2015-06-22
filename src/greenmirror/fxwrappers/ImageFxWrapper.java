package greenmirror.fxwrappers;

import greenmirror.FxPropertyWrapper;
import greenmirror.FxWrapper;
import greenmirror.GreenMirrorUtils;
import greenmirror.Placement;
import greenmirror.StoredBytesImage;
import greenmirror.fxpropertywrappers.BooleanFxProperty;
import greenmirror.fxpropertywrappers.DoubleFxProperty;
import greenmirror.fxpropertywrappers.ImageFxProperty;
import greenmirror.server.AbstractTransition;
import greenmirror.server.DoublePropertyTransition;
import org.eclipse.jdt.annotation.NonNull;

import java.io.BufferedInputStream;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLConnection;
import java.util.ArrayList;
import java.util.List;

import javafx.animation.ParallelTransition;
import javafx.animation.Transition;
import javafx.geometry.Point3D;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.util.Duration;

/**
 * The {@link FxWrapper} for image FX nodes. The JavaFX type is {@link ImageView} and its 
 * image content type is {@link Image}. 
 * 
 * @author Karim El Assal
 */
public class ImageFxWrapper extends FxWrapper {

    // -- Instance variables -----------------------------------------------------------------

    /** the virtual x value of the FX node */
    private Double posX;
    /** the virtual y value of the FX node */
    private Double posY;
    /** the virtual fitWidth value of the FX node */
    private Double fitWidth;
    /** the virtual fitHeight value of the FX node */
    private Double fitHeight;
    /** the virtual image value of the FX node */
    private Image image;
    /** the virtual preserveRatio value of the FX node */
    private Boolean preserveRatio = true;
    

    // -- Constructors -----------------------------------------------------------------------

    // -- Queries ----------------------------------------------------------------------------

    @Override @NonNull 
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
    
    @Override @NonNull 
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
    
    @Override
    /*@ pure */ public javafx.scene.image.ImageView getFxNode() {
        return (javafx.scene.image.ImageView) super.getFxNode();
    }
    

    @Override
    /*@ pure */ public Double getX() {
        return this.posX;
    }
    
    @Override
    /*@ pure */ public Double getY() {
        return this.posY;
    }

    /** @return the virtual fitWidth value of the FX node */
    /*@ pure */ public Double getFitWidth() {
        return fitWidth;
    }

    /** @return the virtual fitHeight value of the FX node */
    /*@ pure */ public Double getFitHeight() {
        return fitHeight;
    }

    /** @return the virtual image value of the FX node */
    /*@ pure */ public Image getImage() {
        return image;
    }

    /** @return the virtual preserveRatio value of the FX node */
    /*@ pure */ public Boolean isPreserveRatio() {
        return preserveRatio;
    }

    
    // -- Setters ----------------------------------------------------------------------------

    /**
     * Sets the virtual x property and notifies the observers.
     * 
     * @param value the new value
     * @return      <code>this</code>
     */
    //@ ensures getX() == value;
    @Override @NonNull public ImageFxWrapper setX(double value) {
        this.posX = value;
        setChanged();
        notifyObservers();
        return this;
    }

    /**
     * Sets the virtual y property and notifies the observers.
     * 
     * @param value the new value
     * @return      <code>this</code>
     */
    //@ ensures getY() == value;
    @Override @NonNull public ImageFxWrapper setY(double value) {
        this.posY = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    /**
     * Sets the virtual x and y properties and notifies the observers.
     * 
     * @param posX the x coordinate
     * @param posY the y coordinate
     * @return      <code>this</code>
     */
    //@ ensures getX() == posX && getY() == posY;
    @Override @NonNull public ImageFxWrapper setPosition(double posX, double posY) {
        this.posX = posX;
        this.posY = posY;
        setChanged();
        notifyObservers();
        return this;
    }
    
    /**
     * Sets the virtual fitWidth property and notifies the observers.
     * 
     * @param value the new value
     * @return      <code>this</code>
     */
    //@ ensures getFitWidth() == value;
    @NonNull public ImageFxWrapper setFitWidth(double value) {
        this.fitWidth = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    /**
     * Sets the virtual fitHeight property and notifies the observers.
     * 
     * @param value the new value
     * @return      <code>this</code>
     */
    //@ ensures getFitHeight() == value;
    @NonNull public ImageFxWrapper setFitHeight(double value) {
        this.fitHeight = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    /**
     * Sets the virtual image property and notifies the observers.
     * 
     * @param value the new value; should be an instance of {@link StoredBytesImage}
     * @return      <code>this</code>
     * @throws IllegalArgumentException if <code>value</code> is not an instance of 
     *                                  <code>StoredBytesImage</code>
     */
    //@ requires value instanceof StoredBytesImage;
    //@ ensures getImage() == value;
    @NonNull public ImageFxWrapper setImage(Image value) {
        if (!(value instanceof StoredBytesImage) && value != null) {
            throw new IllegalArgumentException("Image has to be of type StoredBytesImage.");
        }
        this.image = value;
        setChanged();
        notifyObservers();
        return this;
    }

    /**
     * Sets the image from a file path. This method first tries to find the file with
     * <code>ImageFxWrapper.class.getResourceAsStream(filePath)</code> and if that does not
     * work, it tries it again with <code>new FileInputStream(filePath)</code>. If both won't
     * work, an exception is thrown.
     * The stored image is of type {@link StoredBytesImage} and the image's bytes are stored
     * with it.
     * 
     * @param filePath the path to the image file
     * @return         <code>this</code>
     * @throws IllegalArgumentException if the file could not be found
     */
    //@ ensures \result == this;
    @NonNull public ImageFxWrapper setImageFromFile(String filePath) {
        
        // Get InputStream of the file.
        InputStream inputStream;
        if ((inputStream = ImageFxWrapper.class.getResourceAsStream(filePath)) == null) {
            try {
                inputStream = new FileInputStream(filePath);
            } catch (FileNotFoundException e) {
                throw new IllegalArgumentException("file " + filePath + " could not be found");
            }
        }
        final byte[] bytes = StoredBytesImage.readBytes(inputStream);
        final StoredBytesImage img = new StoredBytesImage(new BufferedInputStream(inputStream));
        img.setBytes(bytes);
        return setImage(img);
    }

    /**
     * Sets the image from an URL. This method uses <code>new URL(url).openConnection()</code>
     * for the URL connection.
     * The stored image is of type {@link StoredBytesImage} and the image's bytes are stored
     * with it.
     * 
     * @param url the url to the image file
     * @return    <code>this</code>
     * @throws IllegalArgumentException if the file could not be found
     * @throws NullPointerException     if <code>inputStream</code> is <code>null</code>
     */
    //@ ensures \result == this;
    @NonNull public ImageFxWrapper setImageFromUrl(@NonNull String url) {
        try {
            final URLConnection connection = new URL(url).openConnection();
            connection.connect();
            final InputStream inputStream = connection.getInputStream();
            if (inputStream == null) {
                throw new IllegalArgumentException("unable to retrieve image from " + url);
            }
            final byte[] bytes = StoredBytesImage.readBytes(inputStream);
            final StoredBytesImage image = new StoredBytesImage(inputStream);
            image.setBytes(bytes);
            setImage(image);
            
            if (bytes == null || bytes.length == 0) {
                throw new IllegalArgumentException("unable to retrieve image from " + url);
            }
            
        } catch (MalformedURLException e) {
            throw new IllegalArgumentException("the following URL is malformed: " + url);
        } catch (IOException e) {
            throw new IllegalArgumentException("this went wrong with opening url " + url 
                    + ": " + e.getMessage());
        }
        return this;
    }
    
    /**
     * Sets the virtual preserveRatio property and notifies the observers.
     * 
     * @param value the new value
     * @return      <code>this</code>
     */
    //@ ensures isPreserveRatio() == value;
    @NonNull public ImageFxWrapper setPreserveRatio(boolean value) {
        this.preserveRatio = value;
        setChanged();
        notifyObservers();
        return this;
    }
    
    
    
    /**
     * Creates the animation that changes the x property of the JavaFX node to
     * <code>value</code>.
     * 
     * @param value    the new value
     * @param duration the duration of the animation
     * @return         the JavaFX <code>Animation</code> that animates the change
     * @throws         IllegalStateException if <code>getFxNode()</code> is <code>null</code>
     * @see            XTransition
     */
    //@ requires getFxNode() != null;
    //@ ensures \result.getToValue() == value && \result.getDuration() == duration;
    //@ ensures \result.getNode() == getFxNode();
    /*@ pure */ @NonNull public Transition animateX(double value, @NonNull Duration duration) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        return new XTransition(duration, getFxNode(), value);
    }
    
    /**
     * Creates the animation that changes the y property of the JavaFX node to
     * <code>value</code>.
     * 
     * @param value    the new value
     * @param duration the duration of the animation
     * @return         the JavaFX <code>Animation</code> that animates the change
     * @throws         IllegalStateException    if <code>getFxNode()</code> is <code>null</code>
     * @see            YTransition
     */
    //@ requires getFxNode() != null;
    //@ ensures \result.getToValue() == value && \result.getDuration() == duration;
    //@ ensures \result.getNode() == getFxNode();
    /*@ pure */ @NonNull public Transition animateY(double value, @NonNull Duration duration) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        return new YTransition(duration, getFxNode(), value);
    }
    
    /**
     * Creates the animation that changes the fitWidth property of the JavaFX node to
     * <code>value</code>.
     * 
     * @param value    the new value
     * @param duration the duration of the animation
     * @return         the JavaFX <code>Animation</code> that animates the change
     * @throws         IllegalStateException    if <code>getFxNode()</code> is <code>null</code>
     * @see            FitWidthTransition
     */
    //@ requires getFxNode() != null;
    //@ ensures \result.getToValue() == value && \result.getDuration() == duration;
    //@ ensures \result.getNode() == getFxNode();
    /*@ pure */ @NonNull public Transition animateFitWidth(double value, 
                                                           @NonNull Duration duration) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        return new FitWidthTransition(duration, getFxNode(), value);
    }
    
    /**
     * Creates the animation that changes the fitHeight property of the JavaFX node to
     * <code>value</code>.
     * 
     * @param value    the new value
     * @param duration the duration of the animation
     * @return         the JavaFX <code>Animation</code> that animates the change
     * @throws         IllegalStateException    if <code>getFxNode()</code> is <code>null</code>
     * @see            FitHeightTransition
     */
    //@ requires getFxNode() != null;
    //@ ensures \result.getToValue() == value && \result.getDuration() == duration;
    //@ ensures \result.getNode() == getFxNode();
    /*@ pure */ @NonNull public Transition animateFitHeight(double value, 
                                                            @NonNull Duration duration) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        return new FitHeightTransition(duration, getFxNode(), value);
    }

    /**
     * Creates the animation that changes the image property of the JavaFX node to
     * <code>value</code>.
     * 
     * @param value    the new value
     * @param duration the duration of the animation
     * @return         the JavaFX <code>Animation</code> that animates the change
     * @throws         IllegalStateException    if <code>getFxNode()</code> is <code>null</code>
     * @see            ImageTransition
     */
    //@ requires getFxNode() != null;
    //@ ensures \result.getToValue() == value && \result.getDuration() == duration;
    //@ ensures \result.getNode() == getFxNode();
    /*@ pure */ @NonNull public Transition animateImage(Image value, @NonNull Duration duration) {
        if (getFxNode() == null) {
            throw new IllegalStateException(GreenMirrorUtils.MSG_NO_FXNODE);
        }
        return new ImageTransition(duration, getFxNode(), value);
    }
    

    // -- Class usage ------------------------------------------------------------------------

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

    @Override @NonNull 
    /*@ pure */ public Point3D calculatePoint(@NonNull Placement placement) {
        final double[] size = determineSize();
        final Point3D returnPoint
            =  new Point3D(getX(), getY(), 0)
                    .add(FxWrapper.calculatePointOnRectangle(size[0], size[1], placement));
        if (returnPoint == null) {
            throw new RuntimeException("Point3D#add(Point3D) returned null");
        }
        return returnPoint;
    }

    @Override
    public void createFxNode() {
        setFxNode(new ImageView(getImage()));
    }

    @Override @NonNull 
    public Transition animateToMiddlePoint(@NonNull Point3D middlePoint, @
                                           NonNull Duration duration) {
        final Point3D coord = calculateOriginCoordinates(middlePoint);
        return new ParallelTransition(
                new XTransition(duration, getFxNode(), coord.getX()),
                new YTransition(duration, getFxNode(), coord.getY()));
    }

    @Override @NonNull 
    protected Point3D calculateOriginCoordinates(@NonNull Point3D middlePoint) {
        final double[] size = determineSize();
        
        return new Point3D(middlePoint.getX() - size[0] / 2, 
                           middlePoint.getY() - size[1] / 2, 0);
    }

    @Override
    public void setToPositionWithMiddlePoint(@NonNull Point3D middlePoint) {
        final Point3D coord = calculateOriginCoordinates(middlePoint);
        setX(coord.getX());
        setY(coord.getY());
    }

    @Override
    public void setFxToPositionWithMiddlePoint(@NonNull Point3D middlePoint) {
        final Point3D coord = calculateOriginCoordinates(middlePoint);
        getFxNode().setX(coord.getX());
        getFxNode().setY(coord.getY());
    }

    

    /**
     * A <code>Transition</code> class that animates the x value of an <code>ImageView</code>.
     * 
     * @author Karim El Assal
     */
    public static class XTransition extends DoublePropertyTransition<ImageView> {
        
        protected XTransition(@NonNull Duration duration, ImageView node, Double toValue) {
            super(duration, node, toValue);
        }

        @Override
        protected Double getPropertyValue() {
            return getNode().getX();
        }

        @Override
        protected void setPropertyValue(@NonNull Double value) {
            getNode().setX(value);
        }
    }
    
    /**
     * A <code>Transition</code> class that animates the y value of an <code>ImageView</code>.
     * 
     * @author Karim El Assal
     */
    public static class YTransition extends DoublePropertyTransition<ImageView> {
        
        protected YTransition(@NonNull Duration duration, ImageView node, Double toValue) {
            super(duration, node, toValue);
        }

        @Override
        protected Double getPropertyValue() {
            return getNode().getY();
        }

        @Override
        protected void setPropertyValue(@NonNull Double value) {
            getNode().setY(value);
        }
    }
    
    /**
     * A <code>Transition</code> class that animates the change of the width.
     * 
     * @author Karim El Assal
     */
    public static class FitWidthTransition extends DoublePropertyTransition<ImageView> {
        
        protected FitWidthTransition(@NonNull Duration duration, ImageView node, Double toValue) {
            super(duration, node, toValue);
        }

        @Override
        protected Double getPropertyValue() {
            return getNode().getFitWidth();
        }

        @Override
        protected void setPropertyValue(@NonNull Double value) {
            getNode().setFitWidth(value);
        }
    }
    
    /**
     * A <code>Transition</code> class that animates the change of the height.
     * 
     * @author Karim El Assal
     */
    public static class FitHeightTransition extends DoublePropertyTransition<ImageView> {
        
        protected FitHeightTransition(@NonNull Duration duration, ImageView node, Double toValue) {
            super(duration, node, toValue);
        }

        @Override
        protected Double getPropertyValue() {
            return getNode().getFitHeight();
        }

        @Override
        protected void setPropertyValue(@NonNull Double value) {
            getNode().setFitHeight(value);
        }
    }
    
    
    public static class ImageTransition extends AbstractTransition<ImageView, Image> {
        
        public ImageTransition(@NonNull Duration duration, ImageView node, Image toValue) {
            super(duration, node, toValue);
        }
        
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
