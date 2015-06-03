package greenmirror.server.playbackstates;

import greenmirror.server.ToolbarButton;
import greenmirror.server.Visualizer.PlaybackState;

/**
 * The stepping <code>PlaybackState</code>.
 * 
 * @author Karim El Assal
 */
public class SteppingState extends PlaybackState {

    /* (non-Javadoc)
     * @see greenmirror.server.Visualizer.PlaybackState#determineButtonOperation(boolean, boolean)
     */
    @Override
    public void determineButtonOperation(boolean hasPreviousState, boolean hasNextState) {
        ToolbarButton.STEP_BACK_FAST.setEnabled(false);
        ToolbarButton.STEP_BACK.setEnabled(false);
        ToolbarButton.PLAY_BACK.setEnabled(false);
        ToolbarButton.PAUSE.setEnabled(false);
        ToolbarButton.PLAY.setEnabled(false);
        ToolbarButton.STEP.setEnabled(false);
        ToolbarButton.STEP_FAST.setEnabled(false);
    }

    /* (non-Javadoc)
     * @see greenmirror.server.Visualizer.PlaybackState#isContinuous()
     */
    @Override
    public boolean isContinuous() {
        return false;
    }

    /* (non-Javadoc)
     * @see greenmirror.server.Visualizer.PlaybackState#toString()
     */
    @Override
    public String toString() {
        return "stepping...";
    }

}
