package greenmirror.server.playbackstates;

import greenmirror.server.ToolbarButton;
import greenmirror.server.Visualizer.PlaybackState;

/**
 * The visualizer's stepping playback state.
 * 
 * @author Karim El Assal
 */
public class SteppingState implements PlaybackState {

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

    @Override
    public boolean isContinuous() {
        return false;
    }

    @Override
    public String toString() {
        return "stepping...";
    }

}
