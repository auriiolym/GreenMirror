package greenmirror.server.playbackstates;

import greenmirror.server.ToolbarButton;
import greenmirror.server.Visualizer.PlaybackState;

import org.eclipse.jdt.annotation.NonNull;

/**
 * The visualizer's playing playback state.
 * 
 * @author Karim El Assal
 */
public class PlayingState implements PlaybackState {

    @Override
    public void determineButtonOperation(boolean hasPreviousState, boolean hasNextState) {
        ToolbarButton.STEP_BACK_FAST.setEnabled(false);
        ToolbarButton.STEP_BACK.setEnabled(false);
        ToolbarButton.PLAY_BACK.setEnabled(false);
        ToolbarButton.PAUSE.setEnabled(true);
        ToolbarButton.PLAY.setEnabled(false);
        ToolbarButton.STEP.setEnabled(false);
        ToolbarButton.STEP_FAST.setEnabled(false);
    }

    @Override
    public boolean isContinuous() {
        return true;
    }

    @Override @NonNull
    public String toString() {
        return "playing...";
    }

}
