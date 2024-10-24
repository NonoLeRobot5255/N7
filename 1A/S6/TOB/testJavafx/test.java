import javafx.application.Application;
import javafx.scene.Scene;
import javafx.scene.control.Label;
import javafx.scene.layout.StackPane;
import javafx.stage.Stage;

public class Test extends Application {

    @Override
    public void start(Stage primaryStage) {
        // Create a label
        Label label = new Label("Hello, JavaFX!");

        // Create a layout pane
        StackPane root = new StackPane();
        root.getChildren().add(label);

        // Create a scene
        Gridpane scene = new Gridpane(root, 400, 300);


        // Set the scene on the stage
        primaryStage.setScene(scene);

        // Set the title of the window
        primaryStage.setTitle("JavaFX Window");

        // Show the window
        primaryStage.show();
    }

    public static void main(String[] args) {
        launch(args);
    }
}