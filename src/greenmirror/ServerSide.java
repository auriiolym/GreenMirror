package greenmirror;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

/**
 * An annotation to indicate that a class is meant to be used on the server side.
 * 
 * @author Karim El Assal
 */
@Retention(RetentionPolicy.RUNTIME)
public @interface ServerSide {}
