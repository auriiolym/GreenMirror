package greenmirror.tests;

import static org.hamcrest.CoreMatchers.equalTo;
import static org.junit.Assert.assertThat;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;
import greenmirror.Placement;
import greenmirror.fxwrappers.CircleFxWrapper;
import greenmirror.fxwrappers.RectangleFxWrapper;
import greenmirror.placements.CornerTopLeftPlacement;
import greenmirror.placements.CustomPlacement;
import greenmirror.placements.EdgePlacement;

import java.util.LinkedList;
import java.util.List;

import javafx.geometry.Point3D;

import org.junit.Before;
import org.junit.Test;

public class PlacementTest {
    
    
    RectangleFxWrapper rect;
    CircleFxWrapper circ;
    // The image and text FxWrappers work with the same method as RectangleFxWrapper.
    
    @Before
    public void setUp() {
        rect = new RectangleFxWrapper();
        rect.setPosition(0, 0);
        rect.setSize(100, 100);
        
        circ = new CircleFxWrapper();
        circ.setPosition(50, 50);
        circ.setRadius(50);
    }

    @Test
    public void rectanglePlacementTest() {
        
        Placement[] testPlacement = {
                Placement.NONE,
                Placement.MIDDLE,
                new CustomPlacement(1, 1, 0),
                new CustomPlacement(-1, -1, 0),
                new CustomPlacement(-51, -51, 0),
                new EdgePlacement(0),
                new EdgePlacement(90),
                new EdgePlacement(90 + 360 * 500),
                new EdgePlacement(-90 + 360 * 500),
                new EdgePlacement(45),
                new EdgePlacement(-45),
                new EdgePlacement(135),
                new EdgePlacement(-135),
                new EdgePlacement(180),
                Placement.EDGE_TOP,
                Placement.EDGE_RIGHT,
                Placement.EDGE_BOTTOM,
                Placement.EDGE_LEFT,
                Placement.CORNER_TOP_LEFT,
                Placement.CORNER_TOP_RIGHT,
                Placement.CORNER_BOTTOM_RIGHT,
                Placement.CORNER_BOTTOM_LEFT,
                new CornerTopLeftPlacement().withRelativePosition(-1, -1),
        };
        Point3D[] expectedResult = {
                Point3D.ZERO,
                new Point3D(50, 50, 0),
                new Point3D(51, 51, 0),
                new Point3D(49, 49, 0),
                new Point3D(-1, -1, 0),
                new Point3D(50, 0, 0),
                new Point3D(100, 50, 0),
                new Point3D(100, 50, 0),
                new Point3D(0, 50, 0),
                new Point3D(100, 0, 0),
                Point3D.ZERO,
                new Point3D(100, 100, 0),
                new Point3D(0, 100, 0),
                new Point3D(50, 100, 0),
                new Point3D(50, 0, 0),
                new Point3D(100, 50, 0),
                new Point3D(50, 100, 0),
                new Point3D(0, 50, 0),
                Point3D.ZERO,
                new Point3D(100, 0, 0),
                new Point3D(100, 100, 0),
                new Point3D(0, 100, 0),
                new Point3D(-1, -1, 0),
        };
        
        // Test placements.
        for (int i = 0; i < testPlacement.length; i++) {
            
            Point3D calcPoint = rect.calculatePoint(testPlacement[i]);
            calcPoint = new Point3D(Math.round(calcPoint.getX()), 
                                    Math.round(calcPoint.getY()), 
                                    Math.round(calcPoint.getZ()));
            assertThat("Placement data set: " + testPlacement[i].toData(), 
                        calcPoint, 
                        equalTo(expectedResult[i]));
        }
        
        // Test random placement.
        final List<Double> xvalues = new LinkedList<Double>();
        final List<Double> yvalues = new LinkedList<Double>();
        for (int i = 0; i < 10000; i++) {
            final Point3D calcPoint = rect.calculatePoint(Placement.RANDOM);
            xvalues.add(calcPoint.getX());
            yvalues.add(calcPoint.getY());
            assertTrue(calcPoint.getX() >= 0 && calcPoint.getX() <= 100);
            assertTrue(calcPoint.getY() >= 0 && calcPoint.getY() <= 100);
        }
        
        // Test average random placement.
        final double avgX = xvalues.stream().mapToDouble(d -> d).average().orElse(0);
        final double avgY = yvalues.stream().mapToDouble(d -> d).average().orElse(0);
        assertTrue(avgX < 51 && avgX > 49);
        assertTrue(avgY < 51 && avgY > 49);
    }
    
    
    @Test
    public void CirclePlacementTest() {
        
        Placement[] testPlacement = {
                Placement.NONE,
                Placement.MIDDLE,
                new CustomPlacement(1, 1, 0),
                new CustomPlacement(-1, -1, 0),
                new CustomPlacement(-51, -51, 0),
                new EdgePlacement(0),
                new EdgePlacement(90),
                new EdgePlacement(90 + 360 * 500),
                new EdgePlacement(-90 + 360 * 500),
                new EdgePlacement(45),
                new EdgePlacement(-45),
                new EdgePlacement(135),
                new EdgePlacement(-135),
                new EdgePlacement(180),
                Placement.EDGE_TOP,
                Placement.EDGE_RIGHT,
                Placement.EDGE_BOTTOM,
                Placement.EDGE_LEFT,
                Placement.CORNER_TOP_LEFT,
                Placement.CORNER_TOP_RIGHT,
                Placement.CORNER_BOTTOM_RIGHT,
                Placement.CORNER_BOTTOM_LEFT,
                new CornerTopLeftPlacement().withRelativePosition(-15, -15),
        };
        Point3D[] expectedResult = {
                Point3D.ZERO,
                new Point3D(50, 50, 0),
                new Point3D(51, 51, 0),
                new Point3D(49, 49, 0),
                new Point3D(-1, -1, 0),
                new Point3D(50, 0, 0),
                new Point3D(100, 50, 0),
                new Point3D(100, 50, 0),
                new Point3D(0, 50, 0),
                new Point3D(85, 15, 0),
                new Point3D(15, 15, 0),
                new Point3D(85, 85, 0),
                new Point3D(15, 85, 0),
                new Point3D(50, 100, 0),
                new Point3D(50, 0, 0),
                new Point3D(100, 50, 0),
                new Point3D(50, 100, 0),
                new Point3D(0, 50, 0),
                new Point3D(15, 15, 0),
                new Point3D(85, 15, 0),
                new Point3D(85, 85, 0),
                new Point3D(15, 85, 0),
                Point3D.ZERO,
        };
        
        
        // Test placements.
        for (int i = 0; i < testPlacement.length; i++) {
            
            Point3D calcPoint = circ.calculatePoint(testPlacement[i]);
            
            calcPoint = new Point3D(Math.round(calcPoint.getX()), 
                                    Math.round(calcPoint.getY()), 
                                    Math.round(calcPoint.getZ()));
            assertThat("Placement data set: " + testPlacement[i].toData(), 
                        calcPoint, 
                        equalTo(expectedResult[i]));
        }
        
        // Test random placement.
        final List<Double> xvalues = new LinkedList<Double>();
        final List<Double> yvalues = new LinkedList<Double>();
        for (int i = 0; i < 10000; i++) {
            final Point3D calcPoint = circ.calculatePoint(Placement.RANDOM);
            xvalues.add(calcPoint.getX());
            yvalues.add(calcPoint.getY());
            assertTrue(Math.pow(calcPoint.getX() - 50, 2) + Math.pow(calcPoint.getY() - 50, 2) 
                    < 50 * 50);
        }   
        
        // Test average random placement.
        final double avgX = xvalues.stream().mapToDouble(d -> d).average().orElse(0);
        final double avgY = yvalues.stream().mapToDouble(d -> d).average().orElse(0);
        assertTrue(avgX < 51 && avgX > 49);
        assertTrue(avgY < 51 && avgY > 49);
        
    }

    
    
    
    
    
    
    
    
    
}
