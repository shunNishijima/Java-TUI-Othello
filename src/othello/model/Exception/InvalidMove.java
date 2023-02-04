package othello.model.Exception;
import othello.model.server.Protocol;

public class InvalidMove extends Exception{
    public InvalidMove(){
        super(Protocol.forwardError("Invalid Move"));
    }
}
