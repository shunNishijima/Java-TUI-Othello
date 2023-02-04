package othello.model.Exception;

import othello.model.server.Protocol;

public class InvalidInput extends Exception{
    public InvalidInput(){
        super(Protocol.forwardError("Invalid Input, please try again"));
    }
}
