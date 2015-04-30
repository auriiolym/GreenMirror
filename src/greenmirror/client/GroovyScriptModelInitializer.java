package greenmirror.client;

import greenmirror.GreenMirrorController;
import groovy.lang.Binding;
import groovy.lang.GroovyShell;
import groovy.lang.Script;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;

import org.codehaus.groovy.control.CompilerConfiguration;

/**
 * The model initializer that initializes the model through a Groovy script.
 * 
 * @author Karim El Assal
 */
public class GroovyScriptModelInitializer implements ModelInitializer {
    

    // -- Constants --------------------------------------------------------------------------

    /**
     * The unique identifier of this <tt>ModelInitializer</tt>.
     */
    private static final String UID = "groovyscript";
    
    /**
     * The parameter discription.
     */
    private static final String PARAMS = "<filename>";
    
    /**
     * The base class for the Groovy script.
     */
    private static final Class<? extends Script> BASECLASS = GreenMirrorGroovyBaseScript.class;
    
    
    // -- Instance variables -----------------------------------------------------------------
    
    /**
     * The GreenMirror controller.
     */
    //@ private invariant getController() == controller;
    private Client controller;

    /**
     * The script that will be run. This includes the user's script and the base class.
     */
    private Script script;
    
    /**
     * The <tt>FileReader</tt> for the source file.
     */
    private FileReader filereader;
    
    
    // -- Constructors -----------------------------------------------------------------------

    // -- Queries ----------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see greenmirror.client.ModelInitializer#getController()
     */
    @Override
    /*@ pure */ public Client getController() {
        return controller;
    }

    /* (non-Javadoc)
     * @see greenmirror.client.TraceSelector#getParameterSpecification()
     */
    @Override
    //@ ensures \result != null;
    /*@ pure */ public String getParameterSpecification() {
        return PARAMS;
    }

    /* (non-Javadoc)
     * @see greenmirror.client.ModelInitializer#getIdentifier()
     */
    //@ ensures \result != null;
    @Override
    /*@ pure */ public String getIdentifier() {
        return UID;
    }
    
    
    // -- Setters ----------------------------------------------------------------------------

    /**
     * @param controller The controller to set.
     */
    //@ ensures getController() == controller;
    @Override
    public void setController(Client controller) {
        this.controller = controller;
    }

    /* (non-Javadoc)
     * @see greenmirror.client.ModelInitializer#setParameters(java.lang.String[])
     */
    @Override
    public void setParameters(String... parameters) throws IllegalArgumentException {
        // Check if we've got the exact amount of necessary parameters.
        if (parameters.length != 1) {
            throw new IllegalArgumentException("the Groovy script model initializer only "
                                             + "needs the filename as its parameter.");
        }
        // Check if the file can be found.
        try {
            filereader = new FileReader(parameters[0]);
        } catch (FileNotFoundException e) {
            throw new IllegalArgumentException("the Groovy script model initializer could "
                    + "not find the file \"" + parameters[0] + "\".");
        }
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    /**
     * Prepare this <tt>ModelInitializer</tt> for executing. This includes reading the
     * Groovy script source file, checking if the initialize() command is the first, and
     * parsing it.
     * @throws ModelInitializer.PreparationException If anything goes wrong.
     */
    @Override
    public void prepare() throws ModelInitializer.PreparationException {
        
        String source = "";
        
        // Read the source file.
        try (BufferedReader reader = new BufferedReader(filereader)) {
            String line = reader.readLine();

            while (line != null) {
                source += line + "\n";
                line = reader.readLine();
            }
        } catch (IOException e) {
            throw new ModelInitializer.PreparationException("an IO error occured while handling "
                    + "the source file.");
        }
        source = source.trim();
        
        // Check if the first command is initialize() or //#secondary.
        boolean scriptStartOkay = false;
        for (String line : source.split("\r?\n")) {
            line = line.trim();
            if (line.startsWith("initialize(") || line.startsWith("//#secondary")) {
                scriptStartOkay = true;
                break;
            // Ignore empty lines, single-line-comment lines and import statements.
            } else if (line.equals("") || line.startsWith("//")
                    || line.matches("^import [^;]*;?$")) {
                continue;
            // If anything else is on the line, it's not good.
            } else {
                break;
            }
        }
        if (!scriptStartOkay) {
            throw new ModelInitializer.PreparationException("your script should begin with an "
                    + "\"initialize()\" statement (or \"//#secondary\" if you know for sure that "
                    + "the visualizer has already been initialized by another model initializer). "
                    + "Import statements are also allowed.");
        }
        
        // Add the base class.
        Binding binding = new Binding();
        
        binding.setVariable("baseclass", BASECLASS.getName());
        // Give this to the base class. It won't be available in the script.
        binding.setVariable("GreenMirrorController", getController());
        
        source = "@BaseScript " + BASECLASS.getName() + " baseclass\n"
               + "import groovy.transform.BaseScript;\n"
               + "import greenmirror.*;\n"
               + "import greenmirror.visualcomponents.*;\n"
               + source;
        
        // And parse the script.
        script = new GroovyShell(binding).parse(source);
    }

    /* (non-Javadoc)
     * @see greenmirror.client.ModelInitializer#executeInitializer()
     */
    @Override
    public void executeInitializer() {
        script.run();
    }
}