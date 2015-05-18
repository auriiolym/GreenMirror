package greenmirror.server.playbackstates;

import greenmirror.server.ToolbarButton;
import greenmirror.server.Visualizer.PlaybackState;

/**
 * The paused <tt>PlaybackState</tt>.
 * 
 * @author Karim El Assal
 */
public class PausedState extends PlaybackState {

    /* (non-Javadoc)
     * @see greenmirror.server.Visualizer.PlaybackState#determineButtonOperation()
     */
    @Override
    public void determineButtonOperation(boolean hasPreviousState, boolean hasNextState) {
        ToolbarButton.STEP_BACK_FAST.setEnabled(hasPreviousState);
        ToolbarButton.STEP_BACK.setEnabled(hasPreviousState);
        ToolbarButton.PLAY_BACK.setEnabled(hasPreviousState);
        ToolbarButton.PAUSE.setEnabled(false);
        ToolbarButton.PLAY.setEnabled(hasNextState);
        ToolbarButton.STEP.setEnabled(hasNextState);
        ToolbarButton.STEP_FAST.setEnabled(hasNextState);
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
        return "paused";
    }

}
