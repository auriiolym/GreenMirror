package greenmirror.server.playbackstates;

import greenmirror.server.ToolbarButton;
import greenmirror.server.Visualizer.PlaybackState;

/**
 * The visualizer's paused playback state.
 * 
 * @author Karim El Assal
 */
public class PausedState implements PlaybackState {

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

    @Override
    public String toString() {
        return "paused";
    }

}
