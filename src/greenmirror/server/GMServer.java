package greenmirror.server;

import greenmirror.*;

public class GMServer extends GreenMirrorController {

    private Visualizer visualizer;
    private List<javafx.animation.Transition> visualizationsQueue;
    private Scene scene;

    /**
     * 
     * @param port
     */
    public void listenForConnections(int port) {
        // TODO - implement GMServer.listenForConnections
        throw new UnsupportedOperationException();
    }

    public Scene getScene() {
        return scene;
    }

    /**
     * 
     * @param scene
     */
    public void setScene(Scene scene) {
        scene = scene;
    }

    public List<Transition> getVisualizationsQueue() {
        // TODO - implement GMServer.getVisualizationsQueue
        throw new UnsupportedOperationException();
    }

    public void executeVisualizations() {
        // TODO - implement GMServer.executeVisualizations
        throw new UnsupportedOperationException();
    }

    public Visualizer getVisualizer() {
        return visualizer;
    }

    /**
     * 
     * @param data
     */
    public void handlePeerData(String data) {
        // TODO - implement GMServer.handlePeerData
        throw new UnsupportedOperationException();
    }

}