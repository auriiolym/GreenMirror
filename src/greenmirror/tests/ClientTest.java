package greenmirror.tests;

import greenmirror.client.Client;

import static org.junit.Assert.assertThat;
import static org.hamcrest.CoreMatchers.*;

import org.junit.Before;
import org.junit.Test;

/**
 * 
 * @author Karim El Assal
 */
public class ClientTest {

    /**
     * @throws java.lang.Exception
     */
    @Before
    public void setUp() throws Exception {
        testVar1 = false;
        testVar2 = false;
    }

    public static boolean testVar1;
    public static boolean testVar2;
    
    /**
     * Test method for {@link greenmirror.client.Client#main(java.lang.String[])}.
     */
    @Test
    public void testMain() {
        
        String[] arguments = new String[] {
                "-host:127.0.0.1", 
                "-port:-1", 
                "-model:groovyscript:clienttest.groovy",
                "-trace:file:clienttest.trace"
        };
        Client.main(arguments);
        assertThat(testVar1, is(true));
        assertThat(testVar2, is(true));
    }

}
