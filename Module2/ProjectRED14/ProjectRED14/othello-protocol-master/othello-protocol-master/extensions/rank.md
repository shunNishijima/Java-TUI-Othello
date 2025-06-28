# RANK extension

The ranking extension allows the server to communicate the current player rankings on the server to the different clients. Support for this extension is indicated by adding `RANK` to the `HELLO` commands during initialization.

# New commands 

## RANK (client)
Sent by the client to request the current player ranking on the server. 

*Syntax*: `RANK`

## RANK (server)
Sent by the server to communicate the current server rankings to the requesting client. 

*Syntax*: `RANK[~username~score]*`

All players who have played at least one game on the server should be included in the ranking. The score must be a nonnegative integer (*doubles are not allowed*). The names should be given in order of descending score. 

## Examples
- Where the score is a win percentage, and Alice has just won the only game against Bob: `RANK~Alice~100~Bob~0`
- Where the score is the number of wins, and Bob hs won everything so far: `RANK~Bob~3~Alice~0~Charlie~0`

