package greenmirror;

import java.util.Observable;

/**
 * A class to handle removed <tt>Node</tt>s better.
 * 
 * @author Karim El Assal
 */
public class NullNode extends Node {
    
    // -- Exceptions -------------------------------------------------------------------------

    public static class RemovedNodeUsedException extends RuntimeException {
        public RemovedNodeUsedException(NullNode node) {
            super("You tried to work with a removed node ("
                    + "type: " + node.getOldType() + ", "
                    + "name: " + node.getOldName() + ").");
        }
    }

    /**
     * The old type and name. These are allowed to be <tt>null</tt>.
     */
    private String oldType = null;
    private String oldName = null;
    
    
    // -- Constructors -----------------------------------------------------------------------
    
    /**
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
    
    /**
     * @return The old type of this <tt>Node</tt>.
     */
    /*@ pure */ public String getOldType() {
        return oldType;
    }

    /**
     * @return The old name of this <tt>Node</tt>.
     */
    /*@ pure */ public String getOldName() {
        return oldName;
    }

    /* (non-Javadoc)
     * @see greenmirror.Node#getType()
     */
    @Override
    public String getType() {
        return null;
    }

    /* (non-Javadoc)
     * @see greenmirror.Node#getName()
     */
    @Override
    public String getName() {
        return null;
    }
    
    /* (non-Javadoc)
     * @see greenmirror.Node#hasLabel(java.lang.String)
     */
    @Override
    public boolean hasLabel(String label) {
        return false;
    }


    /* (non-Javadoc)
     * @see greenmirror.Node#getRelations()
     */
    @Override
    public RelationList getRelations() {
        return new RelationList();
    }

    /* (non-Javadoc)
     * @see greenmirror.Node#getFxContainer()
     */
    @Override
    public FxContainer getFxContainer() {
        return super.getFxContainer();
    }

    /* (non-Javadoc)
     * @see greenmirror.Node#toString()
     */
    @Override
    public String toString() {
        return "deleted " + super.toString();
    }
    
    
    // -- Setters ----------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see greenmirror.Node#setType(java.lang.String)
     */
    @Override
    public Node setType(String type) {
        throw new RemovedNodeUsedException(this);
    }

    /* (non-Javadoc)
     * @see greenmirror.Node#setName(java.lang.String)
     */
    @Override
    public Node setName(String name) {
        throw new RemovedNodeUsedException(this);
    }

    /* (non-Javadoc)
     * @see greenmirror.Node#addLabel(java.lang.String)
     */
    @Override
    public Node addLabel(String label) {
        throw new RemovedNodeUsedException(this);
    }

    /* (non-Javadoc)
     * @see greenmirror.Node#removeLabel(java.lang.String)
     */
    @Override
    public Node removeLabel(String label) {
        throw new RemovedNodeUsedException(this);
    }
    
    
    // -- Commands ---------------------------------------------------------------------------

    /* (non-Javadoc)
     * @see greenmirror.Node#addRelation(greenmirror.Relation)
     */
    @Override
    public Node addRelation(Relation relation) {
        throw new RemovedNodeUsedException(this);
    }


    /* (non-Javadoc)
     * @see greenmirror.Node#removeRelation(greenmirror.Relation)
     */
    @Override
    public void removeRelation(Relation relation) {
        throw new RemovedNodeUsedException(this);
    }


    /* (non-Javadoc)
     * @see greenmirror.Node#set(greenmirror.FxContainer)
     */
    @Override
    public Node set(FxContainer fxContainer) {
        throw new RemovedNodeUsedException(this);
    }


    /* (non-Javadoc)
     * @see greenmirror.Node#fx(java.lang.String)
     */
    @Override
    public FxContainer fx(String type) {
        throw new RemovedNodeUsedException(this);
    }

    /* (non-Javadoc)
     * @see greenmirror.Node#fx()
     */
    @Override
    public FxContainer fx() {
        throw new RemovedNodeUsedException(this);
    }


    /* (non-Javadoc)
     * @see greenmirror.Node#update(java.util.Observable, java.lang.Object)
     */
    @Override
    public void update(Observable observable, Object arg1) {
        throw new RemovedNodeUsedException(this);
    }

    /* (non-Javadoc)
     * @see greenmirror.Node#clone()
     */
    @Override
    public Node clone() {
        throw new RemovedNodeUsedException(this);
    }
}