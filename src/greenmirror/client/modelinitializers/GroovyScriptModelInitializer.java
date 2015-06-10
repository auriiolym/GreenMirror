package greenmirror.client.modelinitializers;

import greenmirror.client.Client;
import greenmirror.client.ModelInitializer;
import groovy.lang.Binding;
import groovy.lang.GroovyShell;
import groovy.lang.Script;

import org.eclipse.jdt.annotation.NonNull;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;

/**
 * The model initializer that initializes the model through a Groovy script.
 * 
 * @author Karim El Assal
 */
public class GroovyScriptModelInitializer implements ModelInitializer {
    

    // -- Constants --------------------------------------------------------------------------

    /** the unique identifier of this <code>ModelInitializer</code> */
    @NonNull private static final String UID = "groovyscript";
    
    /** the parameter description */
    @NonNull private static final String PARAMS = "<filename>";
    
    /** the base class for the Groovy script */
    @NonNull private static final Class<? extends Script> BASECLASS 
                                            = GreenMirrorGroovyBaseScript.class;
    
    /** the imports performed in the Groovy user script */
    public static final Object[] IMPORTS = new Object[]{
        "greenmirror.*",
        "greenmirror.placements.*",
        greenmirror.client.GridBuilder.class,
        "javafx.scene.paint.*",
        "javafx.geometry.*",
    };
    
    
    // -- Instance variables -----------------------------------------------------------------
    
    /** the GreenMirror controller */
    //@ private invariant getController() == controller;
    private Client controller;

    /** the script that will be ran. This includes the user's script and the base class */
    private Script script;
    
    /** the <code>FileReader</code> for the source file */
    private FileReader filereader;
    
    
    // -- Constructors -----------------------------------------------------------------------

    // -- Queries ----------------------------------------------------------------------------

    @Override
    /*@ pure */ public Client getController() {
        return controller;
    }

    @Override @NonNull 
    /*@ pure */ public String getParameterSpecification() {
        return PARAMS;
    }

    @Override @NonNull 
    /*@ pure */ public String getIdentifier() {
        return UID;
    }
    
    
    // -- Setters ----------------------------------------------------------------------------

    /** @param controller the controller to set */
    //@ ensures getController() == controller;
    @Override
    public void setController(@NonNull Client controller) {
        this.controller = controller;
    }

    @Override
    public void setParameter(@NonNull String parameter) throws IllegalArgumentException {
        
        // Check if the file can be found.
        try {
            filereader = new FileReader(parameter);
        } catch (FileNotFoundException e) {
            throw new IllegalArgumentException("the Groovy script model initializer could "
                    + "not find the file \"" + parameter + "\"");
        }
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    /**
     * Prepares this <code>ModelInitializer</code> for executing. This includes reading the
     * Groovy script source file, checking if the initialize() command is the first, and
     * parsing it.
     * 
     * @throws ModelInitializer.PreparationException if anything goes wrong
     */
    @Override
    public void prepare() throws ModelInitializer.PreparationException {
        
        String originalSource = "";
        
        // Read the source file.
        try (final BufferedReader reader = new BufferedReader(filereader)) {
            String line = reader.readLine();

            while (line != null) {
                originalSource += line + "\n";
                line = reader.readLine();
            }
        } catch (IOException e) {
            throw new ModelInitializer.PreparationException("an IO error occured while handling "
                    + "the source file.");
        }
        
        // Check if the first command is initialize() or //#secondary.
        boolean scriptStartOkay = false;
        for (String line : originalSource.trim().split("\r?\n")) {
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
                    + "Import statements, blank lines and single comment lines are also allowed.");
        }
        
        // Add the base class.
        final Binding binding = new Binding();
        
        binding.setVariable("baseclass", BASECLASS.getName());
        // Give this to the base class. It won't be available in the script.
        binding.setVariable("GreenMirrorController", getController());

        // Build statements that'll be added before the script.
        String importClasses = "";
        for (Object imp : IMPORTS) {
            importClasses += "import " + (imp instanceof Class 
                    ? ((Class<?>) imp).getName() : String.valueOf(imp)) + ";";
        }
        final String usedSource = ""
               + "@BaseScript " + BASECLASS.getName() + " baseclass;"
               + "import groovy.transform.BaseScript;"
               + importClasses
               + originalSource;
        
        // And parse the script.
        script = new GroovyShell(binding).parse(usedSource);
    }

    /**
     * If an exception is thrown due to the Groovy script, this method tries to remove
     * an irrelevant portion of the stacktrace.
     */
    @Override
    public void executeInitializer() {
        try {
            script.run();
        } catch (Exception e) {
            List<StackTraceElement> st = Arrays.asList(e.getStackTrace());
            for (StackTraceElement ste : e.getStackTrace()) {
                if (ste.getFileName().startsWith("Script") 
                 && ste.getFileName().endsWith(".groovy")) {
                    e.setStackTrace(st.subList(0, st.indexOf(ste) + 1)
                                    .toArray(new StackTraceElement[]{}));
                }
            }
            throw e;
        }
    }
}