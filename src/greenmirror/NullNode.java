package greenmirror;

import org.eclipse.jdt.annotation.NonNull;

import java.util.Observable;

/**
 * A class to handle removed <code>Node</code>s better. It's an implementation of the null object
 * design pattern. All the getters except for {@link #getOldName()} and {@link #getOldType()}
 * return a <code>null</code> or <code>false</code> value and all the setters throw a
 * {@link RemovedNodeUsedException}.
 * 
 * @author Karim El Assal
 */
public class NullNode extends Node {
    
    // -- Exceptions -------------------------------------------------------------------------

    /**
     * An exception thrown when a removed node was used, which was impossible and essential.
     * 
     * @author Karim El Assal
     */
    public static class RemovedNodeUsedException extends RuntimeException {
        public RemovedNodeUsedException(@NonNull NullNode node) {
            super("You tried to work with a removed node ("
                    + "type: " + node.getOldType() + ", "
                    + "name: " + node.getOldName() + ").");
        }
    }

    /** the old type and name */
    private String oldType = null;
    private String oldName = null;
    
    
    // -- Constructors -----------------------------------------------------------------------
    
    /**
     * Creates a new <code>NullNode</code> with its old type and name.
     * 
     * @param oldType
     * @param oldName
     */
    //@ ensures oldType == getOldType() && oldName == getOldName();
    public NullNode(String oldType, String oldName) {
        this.oldType = oldType;
        this.oldName = oldName;
    }
    

    // -- Queries ----------------------------------------------------------------------------
    
    /** @return the old type of this <code>Node</code> */
    /*@ pure */ public String getOldType() {
        return oldType;
    }

    /** @return the old name of this <code>Node</code> */
    /*@ pure */ public String getOldName() {
        return oldName;
    }

    /** @return <code>null</code>: this is a removed node */
    @Override
    public String getType() {
        return null;
    }

    /** @return <code>null</code>: this is a removed node */
    @Override
    public String getName() {
        return null;
    }

    /** @return <code>false</code>: this is a removed node */
    @Override
    public boolean hasLabel(String label) {
        return false;
    }

    /** @return an empty <code>RelationList</code>: this is a removed node */
    @Override @NonNull 
    public RelationList getRelations() {
        return new RelationList();
    }

    /** @return <code>null</code>: this is a removed node */    
    @Override
    public FxWrapper getFxWrapper() {
        return null;
    }

    @Override @NonNull 
    public String toString() {
        return "DELETED " + super.toString();
    }
    
    
    // -- Setters ----------------------------------------------------------------------------

    /** @throws RemovedNodeUsedException because this node is removed */
    @Override @NonNull
    public Node setType(String type) {
        throw new RemovedNodeUsedException(this);
    }

    /** @throws RemovedNodeUsedException because this node is removed */
    @Override @NonNull 
    public Node setName(String name) {
        throw new RemovedNodeUsedException(this);
    }

    /** @throws RemovedNodeUsedException because this node is removed */
    @Override @NonNull 
    public Node addLabel(String label) {
        throw new RemovedNodeUsedException(this);
    }

    /** @throws RemovedNodeUsedException because this node is removed */
    @Override @NonNull 
    public Node removeLabel(String label) {
        throw new RemovedNodeUsedException(this);
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    /** @throws RemovedNodeUsedException because this node is removed */
    @Override @NonNull 
    public Node addRelation(@NonNull Relation relation) {
        throw new RemovedNodeUsedException(this);
    }

    /** @throws RemovedNodeUsedException because this node is removed */
    @Override
    public void removeRelation(Relation relation) {
        throw new RemovedNodeUsedException(this);
    }

    /** @throws RemovedNodeUsedException because this node is removed */
    @Override @NonNull 
    public Node set(@NonNull FxWrapper fxWrapper) {
        throw new RemovedNodeUsedException(this);
    }

    /** @throws RemovedNodeUsedException because this node is removed */
    @Override @NonNull 
    public FxWrapper fx(@NonNull String type) {
        throw new RemovedNodeUsedException(this);
    }

    /** @throws RemovedNodeUsedException because this node is removed */
    @Override @NonNull 
    public FxWrapper fx() {
        throw new RemovedNodeUsedException(this);
    }

    /** @throws RemovedNodeUsedException because this node is removed */
    @Override
    public void update(Observable observable, Object arg1) {
        throw new RemovedNodeUsedException(this);
    }

    /** @throws RemovedNodeUsedException because this node is removed */
    @Override @NonNull 
    public Node clone() {
        throw new RemovedNodeUsedException(this);
    }
}