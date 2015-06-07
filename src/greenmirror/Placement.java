package greenmirror;

import greenmirror.placements.CornerBottomLeftPlacement;
import greenmirror.placements.CornerBottomRightPlacement;
import greenmirror.placements.CornerTopLeftPlacement;
import greenmirror.placements.CornerTopRightPlacement;
import greenmirror.placements.EdgeBottomPlacement;
import greenmirror.placements.EdgeLeftPlacement;
import greenmirror.placements.EdgeRightPlacement;
import greenmirror.placements.EdgeTopPlacement;
import greenmirror.placements.MiddlePlacement;
import greenmirror.placements.NoPlacement;
import greenmirror.placements.RandomPlacement;
import org.eclipse.jdt.annotation.NonNull;

import java.util.LinkedList;
import java.util.List;
import java.util.ServiceLoader;

import javafx.geometry.Point3D;

/**
 * The <code>Placement</code> abstract class used for indicating where a <code>Node</code> 
 * should be placed relative to another <code>Node</code>.
 * <p>
 * If you want to use just the placement information, use the singleton Placement.SUBCLASS. E.g.:
 * <code>Placement.MIDDLE</code>. If you want to use extra, relative position information, create
 * a new instance of a subclass, like: <code>new Placement.Middle()</code>.
 * The <code>Custom</code> subclass does not have a singleton, because extra, relative position 
 * information must be given.
 * 
 * @author Karim El Assal
 */
public abstract class Placement implements Cloneable {
    
    // -- Class variables --------------------------------------------------------------------

    /** The prototypes of all <code>Placement</code>s. */
    @NonNull private static List<Placement> prototypes = new LinkedList<Placement>();
    
    
    // -- Instance variables -----------------------------------------------------------------

    /**
     * The relative position to the selected <code>Placement</code>. If Placement.CUSTOM is chosen,
     * it should default to Placement.MIDDLE. This means that when choosing Placement.CUSTOM,
     * a relative position should be set.
     */
    @NonNull private Point3D relativePosition = new Point3D(0, 0, 0);
    
    
    // -- Constructors -----------------------------------------------------------------------

    // -- Queries ----------------------------------------------------------------------------
    
    /** @return the relative position */
    /*@ pure */ @NonNull public Point3D getRelativePosition() {
        return this.relativePosition;
    }
    
    /** @return the name of this placement */
    @Override @NonNull 
    /*@ pure */ public String toString() {
        final String str = getClass().getSimpleName().replace("Placement", "");
        return str == null ? "" : str;
    }
    
    /** @return a data representation */
    /*@ pure */ @NonNull public String toData() {
        return toString() + ":" 
                + getRelativePosition().getX() + ":" 
                + getRelativePosition().getY() + ":"
                + getRelativePosition().getZ();
    }
    
    /** @return a copy of this <code>Placement</code> */
    @Override @NonNull 
    /*@ pure */ public abstract Placement clone();
    
    /**
     * Checks if <code>object</code> is the same as <code>this</code> according to the placement 
     * data.
     * 
     * @param object the object to check
     * @return       <code>true</code> if the placement is the same
     */
    @Override
    /*@ pure */ public boolean equals(Object object) {
        if (object == null || !(object instanceof Placement)) {
            return false;
        }
        return toData().equals(((Placement) object).toData());
    }
    

    // -- Setters ----------------------------------------------------------------------------
    
    /**
     * @param relativePosition the relative position to set
     * @return                 <code>this</code>
     */
    //@ ensures getRelativePosition() == relativePosition;
    //@ ensures \result == this;
    @NonNull public Placement withRelativePosition(@NonNull Point3D relativePosition) {
        this.relativePosition = relativePosition;
        return this;
    }
    
    /**
     * Sets the relative position and returns <code>this</code>.
     * 
     * @param posX the relative x coordinate
     * @param posY the relative y coordinate
     * @return     <code>this</code>
     */
    //@ ensures getRelativePosition().equals(new Point3D(posX, posY, 0));
    //@ ensures \result == this;
    @NonNull public Placement withRelativePosition(double posX, double posY) {
        return withRelativePosition(posX, posY, 0);
    }
    
    /**
     * @param posX the relative x coordinate
     * @param posY the relative y coordinate
     * @param posY the relative z coordinate
     * @return     <code>this</code>
     */
    //@ ensures getRelativePosition().equals(new Point3D(posX, posY, posZ));
    //@ ensures \result == this;
    @NonNull public Placement withRelativePosition(double posX, double posY, double posZ) {
        return withRelativePosition(new Point3D(posX, posY, posZ));
    }
    
    /**
     * Sets the settings of the placement according to the passed data.
     * 
     * @param data data that could be returned by {@link #toData()}
     * @return     <code>this</code>
     * @throws IllegalArgumentException if <code>data</code> doesn't consist of at least four
     *                                  parts seperated by colons
     */
    //@ ensures \result == this;
    @NonNull public Placement withData(@NonNull String data) {
        final String[] dataParts = data.split(":");
        if (dataParts.length < 4) {
            throw new IllegalArgumentException("the passed placement data was invalid");
        }
        
        return withRelativePosition(new Point3D(
                Double.valueOf(dataParts[1]), 
                Double.valueOf(dataParts[2]),
                Double.valueOf(dataParts[3])));
    }
    

    // -- Class usage ------------------------------------------------------------------------

    /**
     * Creates a new <code>Placement</code> instance from a data string.
     * 
     * @param data the requested <code>Placement</code>
     * @return     a <code>Placement</code> according to <code>data</code>; <code>null</code> if
     *             none was found
     * @throws IllegalArgumentException if <code>data</code> was invalid
     */
    public static Placement fromData(@NonNull String data) {
        if (!data.contains(":")) {
            throw new IllegalArgumentException("the passed placement data was invalid");
        }
        final String[] dataParts = data.split(":", 2);
        
        retrievePlacements();
        
        for (Placement p : getPrototypes()) {
            if (p.toString().equals(dataParts[0])) {
                return p.clone().withData(data);
            }
        }
        return null;
    }
    
    /** @return the prototypes of all available <code>Placement</code>s */
    @NonNull /*@ pure */ private static List<Placement> getPrototypes() {
        return prototypes;
    }
    
    /** Retrieves all available <code>Placement</code>s and stores them */
    //@ ensures getPrototypes().size() > 0;
    private static void retrievePlacements() {
        if (getPrototypes().size() == 0) {
            for (Placement pm : ServiceLoader.load(Placement.class)) {
                getPrototypes().add(pm);
            };
        }
    }
    
    
    
    @NonNull public static final Placement NONE = new NoPlacement();
    
    @NonNull public static final Placement RANDOM = new RandomPlacement();
    
    @NonNull public static final Placement MIDDLE = new MiddlePlacement();
        
    @NonNull public static final Placement EDGE_TOP = new EdgeTopPlacement();
    
    @NonNull public static final Placement EDGE_RIGHT = new EdgeRightPlacement();
        
    @NonNull public static final Placement EDGE_BOTTOM = new EdgeBottomPlacement();
    
    @NonNull public static final Placement EDGE_LEFT = new EdgeLeftPlacement();
    
    @NonNull public static final Placement CORNER_TOP_LEFT = new CornerTopLeftPlacement();
    
    @NonNull public static final Placement CORNER_TOP_RIGHT = new CornerTopRightPlacement();
    
    @NonNull public static final Placement CORNER_BOTTOM_RIGHT 
                                                = new CornerBottomRightPlacement();    
    
    @NonNull public static final Placement CORNER_BOTTOM_LEFT = new CornerBottomLeftPlacement();
    

}