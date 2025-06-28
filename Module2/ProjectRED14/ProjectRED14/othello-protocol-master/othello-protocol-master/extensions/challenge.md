# CHALLENGE extension

The `CHALLENGE` extension provides an alternative to using the `QUEUE` command to start a new game. In brief, if two clients and the server support this extension, one client can `CHALLENGE` the other client to a game. The server then sends a `CHALLENGE` message to the other client. The other client can then choose to `ACCEPT` or `REJECT` the challenge. After an `ACCEPT`, the server starts a new game and sends the `NEWGAME` message.

It is not allowed to use `CHALLENGE` when already in the queue for a game.

# New commands

## CHALLENGE (client)

Sent by the client to challenge another player to play a game.

*Syntax*: `CHALLENGE~<username>`

After receiving this message, the server proceeds as follows:
* If the initiating client is already in a game, this message is illegal. (send `ERROR`)
* If the initiating client is already in the queue, this message is illegal. (send `ERROR`)
* If the target client is not online or is already in a game or does not support the extension or is already challenged by this client, then the server replies with `REJECT`
* Otherwise, the server sends the `CHALLENGE` command to the target client.
* If, after sending the `CHALLENGE` command, the target client disconnects or enters a game with another player, then the server sends `REJECT` to the initiating client.
* If the initiating client enters a game, uses `QUEUE`, or disconnects, all its challenges are silently erased.

## CHALLENGE (server)

Sent by the server to indicate that another player has challenged the client to play a game.

*Syntax:* `CHALLENGE~<username>`

After receiving this message, the client can reply with the `ACCEPT` or `REJECT` message. There is no obligation to reply.

## ACCEPT (client)

Sent by the client to indicate to accept the challenge to play a game.

*Syntax:* `ACCEPT~<username>`

After receiving this message, the server proceeds as follows:
* If there is no outstanding challenge from that client, then the server ignores the message.
* Otherwise, the server starts a new game and sends `NEWGAME` to both players. All other challenges involving the two clients are rejected and erased. That is, all *other* outstanding challenges to the two players are rejected, and all challenges originating from the two players are erased.

## REJECT (client)

Sent by the client to indicate to reject the challenge to play a game.

*Syntax:* `REJECT~<username>`

After receiving this message, the server proceeds as follows:
* If there is no outstanding challenge from that client, then the server ignores the message.
* Otherwise, the server sends `REJECT` to the initiating client and erases the challenge.

## REJECT (server)

Sent by the server to indicate that the client rejected the challenge, or that there was some other reason why the client cannot accept the challenge. For example, the client is not or no longer online, the client does not support the `CHALLENGE` extension, or the client already entered a game with a different player.

*Syntax:* `REJECT~<username>`

