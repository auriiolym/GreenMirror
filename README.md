# GreenMirror
A framework for visualizing state-transitions.

### How to run
The server can be started by opening a command line prompt in the directory where GreenMirrorServer.jar is located and executing
```
java -jar GreenMirrorServer.jar --port=81
```
This assumes you have java in your PATH variable. The port number can of course be varied. Use the **--help** option to see all available options.

The client can be started the same way:
```
java -jar GreenMirrorClient.jar --host=<hostname>:<port> --model=<initializerimplementation>:<implementationparameter> --trace=<selectorimplementation>:<implementationparameter>
```
Again, use **--help** to see specifics about the available options.

### Test case
Try the following to see the ferryman puzzle:
```
java -jar GreenMirrorServer.jar --port=81
java -jar GreenMirrorClient.jar --host=localhost:81 --model=groovyscript:testcases/ferryman.java --trace=file:testcases/ferryman.trace
```