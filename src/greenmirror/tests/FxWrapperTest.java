package greenmirror.tests;

import static org.hamcrest.CoreMatchers.equalTo;
import static org.hamcrest.CoreMatchers.instanceOf;
import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.CoreMatchers.nullValue;
import static org.junit.Assert.assertThat;
import static org.junit.Assert.fail;

import greenmirror.FxWrapper;
import greenmirror.StoredBytesImage;
import greenmirror.fxwrappers.CircleFxWrapper;
import greenmirror.fxwrappers.ImageFxWrapper;
import greenmirror.fxwrappers.RectangleFxWrapper;
import greenmirror.fxwrappers.TextFxWrapper;
import org.junit.Before;
import org.junit.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import javafx.geometry.Point3D;
import javafx.scene.paint.Color;
import javafx.scene.paint.Paint;


public class FxWrapperTest {
    
    RectangleFxWrapper rect;
    CircleFxWrapper circ;
    ImageFxWrapper imag;
    TextFxWrapper text; 

    final String defaultRectangleMapValues = "{type=Rectangle, rotate=0.0, opacity=1.0, "
            + "fill=0x000000ff, x=null, y=null, width=null, height=null, arcWidth=null, arcHeight"
            + "=null, style=null}";
    final String defaultCircleMapValues = "{type=Circle, rotate=0.0, opacity=1.0, fill=0x000000ff"
            + ", centerX=null, centerY=null, radius=null, style=null}";
    final String defaultImageMapValues = "{type=Image, rotate=0.0, opacity=1.0, x=null, y=null, "
            + "fitWidth=null, fitHeight=null, image=null, style=null, preserveRatio=false}";
    final String defaultTextMapValues = "{type=Text, rotate=0.0, opacity=1.0, fill=0x000000ff, x"
            + "=null, y=null, wrappingWidth=null, text=null, style=null}";
    
    @Before
    public void setUp() {
        rect = new RectangleFxWrapper();
        circ = new CircleFxWrapper();
        imag = new ImageFxWrapper();
        text = new TextFxWrapper();
    }
    
    @Test
    public void newInstanceTest() {
        // Test invalid values.
        try {
            FxWrapper.getNewInstance("");
            FxWrapper.getNewInstance("invalid type");
            FxWrapper.getNewInstance("rECTANGLE");
            fail();
        } catch (IllegalArgumentException e) { 
            ; 
        }
    
        // Test valid values.
        assertThat(FxWrapper.getNewInstance("circle"), instanceOf(CircleFxWrapper.class));
        assertThat(FxWrapper.getNewInstance("Circle"), instanceOf(CircleFxWrapper.class));
        assertThat(FxWrapper.getNewInstance("rectangle"), instanceOf(RectangleFxWrapper.class));
        assertThat(FxWrapper.getNewInstance("Rectangle"), instanceOf(RectangleFxWrapper.class));
        assertThat(FxWrapper.getNewInstance("text"), instanceOf(TextFxWrapper.class));
        assertThat(FxWrapper.getNewInstance("Text"), instanceOf(TextFxWrapper.class));
        assertThat(FxWrapper.getNewInstance("image"), instanceOf(ImageFxWrapper.class));
        assertThat(FxWrapper.getNewInstance("Image"), instanceOf(ImageFxWrapper.class));
    }
    
    @Test
    public void fxWrapperTest() {
        
        // Test saving the original FxWrapper.
        assertThat(rect.getOriginalFxWrapper(), is(nullValue()));
        rect.saveAsOriginal();
        assertThat(rect.getOriginalFxWrapper().toMap().toString(), 
                equalTo(defaultRectangleMapValues));

        // Test opacity property.
        rect.setOpacity(0);
        assertThat(rect.getOpacity(), is(0.0));
        try {
            rect.setOpacity(-0.00001);
            fail();
        } catch (IllegalArgumentException e) {
            ;
        }
        try {
            rect.setOpacity(1.00001);
            fail();
        } catch (IllegalArgumentException e) {
            ;
        }

        assertThat(rect.getOpacity(), is(0.0));
        
        // Test rotate property
        assertThat(rect.setRotate( 90 * 5000).getRotate(), is( 90.0 * 5000.0));
        assertThat(rect.setRotate(-90 * 5000).getRotate(), is(-90.0 * 5000.0));
    }
    
    @Test
    public void shapeFxWrapperTest() {
        
        assertThat(rect.getFill(), equalTo(Color.BLACK));
        
        try {
            rect.setFill("invalid value");
            fail();
        } catch (IllegalArgumentException e) {
            ;
        }
        
        final String lin = "linear-gradient(white, black)";
        assertThat(rect.setFill(lin).getFill(), is(Paint.valueOf(lin)));
    }

    @Test
    public void rectangleTest() {
        
        // Test default values.
        assertThat(rect.toMap().toString(), equalTo(defaultRectangleMapValues));
        assertThat(rect.isPositionSet(), is(false));

        // Test arc width and height.
        assertThat(rect.setArcs(1).getArcWidth(), is(1.0));
        assertThat(rect.setArcs(1).getArcHeight(), is(1.0));
        assertThat(rect.setArcs(2, 3).getArcWidth(), is(2.0));
        assertThat(rect.setArcs(2, 3).getArcHeight(), is(3.0));
        
        // Test size.
        rect.setWidth(-100);
        assertThat(rect.getWidth(), is(-100.0)); // Possible, but use at your own risk.
        rect.setSize(100, 100);
        assertThat(rect.getWidth(), is(100.0));
        assertThat(rect.getHeight(), is(100.0));
        
        // Test positioning
        rect.setToPositionWithMiddlePoint(new Point3D(51, 52, 0));
        assertThat(rect.isPositionSet(), is(true));
        assertThat(rect.getX(), is(1.0));
        assertThat(rect.getY(), is(2.0));
        rect.setToPositionWithMiddlePoint(new Point3D(-50, -50, 0));
        assertThat(rect.getX(), is(-100.0));
        assertThat(rect.getY(), is(-100.0));
        try {
            rect.setFxToPositionWithMiddlePoint(new Point3D(1, 1, 0));
            fail();
        } catch (NullPointerException e) {
            ;
        }
        
        // Test setFromMap(Map)
        final RectangleFxWrapper rect2 = new RectangleFxWrapper();
        rect2.setFromMap(rect.toMap());
        assertThat(rect.toMap(), equalTo(rect2.toMap()));
        
        // Test clone
        assertThat(rect.clone().toMap(), equalTo(rect.toMap()));
    }

    @Test
    public void circleTest() {
        
        // Test default values.
        assertThat(circ.toMap().toString(), equalTo(defaultCircleMapValues));
        assertThat(circ.isPositionSet(), is(false));
        
        // Test size.
        try {
            circ.setRadius(-100);
        } catch (IllegalArgumentException e) {
            ;
        }
        assertThat(circ.setRadius(2).getRadius(), is(2.0));
        assertThat(circ.setDiameter(4).getRadius(), is(2.0));
        
        // Test positioning
        circ.setToPositionWithMiddlePoint(new Point3D(51, 52, 0));
        assertThat(circ.isPositionSet(), is(true));
        assertThat(circ.getX(), is(51.0));
        assertThat(circ.getY(), is(52.0));
        assertThat(circ.getCenterX(), is(51.0));
        assertThat(circ.getCenterY(), is(52.0));
        circ.setToPositionWithMiddlePoint(new Point3D(-50, -50, 0));
        assertThat(circ.getX(), is(-50.0));
        assertThat(circ.getY(), is(-50.0));
        try {
            circ.setFxToPositionWithMiddlePoint(new Point3D(1, 1, 0));
            fail();
        } catch (NullPointerException e) {
            ;
        }
        
        // Test setFromMap(Map)
        final Map<String, Object> testMap = new LinkedHashMap<String, Object>() {
            {
                put("type", "Circle");
                put("centerX", 1);
                put("centerY", 2);
                put("radius", 3);
                put("opacity", .4);
                put("rotate", 5);
                put("fill", "white");
                put("invalid property", null);
            }
        };
        circ.setFromMap(testMap);
        final CircleFxWrapper circ2 = new CircleFxWrapper();
        circ2.setFromMap(testMap);
        assertThat(circ.toMap(), equalTo(circ2.toMap()));
        
        // Test clone
        assertThat(circ.clone().toMap(), equalTo(circ.toMap()));
    }

    @Test
    public void imageTest() {
        
        
        // Test default values.
        assertThat(imag.toMap().toString(), equalTo(defaultImageMapValues));
        assertThat(imag.isPositionSet(), is(false));
        
        // Test setImage(Image)
        imag.setImageFromUrl("http://www.utwente.nl/repository/utwente/ws2013/img/nl/"
                           + "inv-utlogo.png");
        assertThat(((StoredBytesImage) imag.getImage()).getBytes().length, is(2258));
        imag.setImage(null);
        assertThat(imag.getImage(), is(nullValue()));
        imag.setImageFromFile("testcases/inv-utlogo.png");
        assertThat(((StoredBytesImage) imag.getImage()).getBytes().length, is(2258));

        // Test clone.
        assertThat(imag.clone().toMap(), equalTo(imag.toMap()));
        
        // Test setFromMap(Map)
        final ImageFxWrapper imag2 = new ImageFxWrapper();
        imag2.setFromMap(imag.toMap());
        assertThat(imag2.toMap(), equalTo(imag.toMap()));
    }

    @Test
    public void TextTest() {
        
        // Test default values.
        assertThat(text.toMap().toString(), equalTo(defaultTextMapValues));
        assertThat(text.isPositionSet(), is(false));
        
        // Test setText(String)
        assertThat(text.setText("foo").getText(), equalTo("foo"));
        assertThat(text.setText(null).getText(), is(nullValue()));
        assertThat(text.setText("").getText(), equalTo(""));

        // Test clone.
        assertThat(text.clone().toMap(), equalTo(text.toMap()));
        
        // Test setFromMap(Map)
        final TextFxWrapper text2 = new TextFxWrapper();
        text2.setFromMap(text.toMap());
        assertThat(text2.toMap(), equalTo(text.toMap()));
    }

}
