# NOISE extension

The `NOISE` extension ensures confidentiality and authenticity of messages exchanged between client and server. Both static and ephemeral keys are exchanged during the initialization sequence described here, after which all remaining messages will be encrypted. Ephemeral keys are generated on the spot and guarantee *forward secrecy*, while static keys remain the same and are used to authenticate.

Support for this extension is indicated by adding `NOISE` to the `HELLO` messages during initialization.

The `NOISE` extension is based on the [Noise protocol](https://noiseprotocol.org/), a framework for crypto protocols based on Diffie-Hellman key agreement. We use the `Noise_XX_25519_AESGCM_SHA256` instantiation, that is, the XX handshake pattern using X25519 keys, AES-GCM ciphers and the SHA256 hash function. See also https://www.youtube.com/watch?v=ceGTgqypwnQ.

The XX handshake pattern consists of three messages:
1. A message from Initiator to Responder with I's ephemeral public key (32 bytes)
2. A message from Responder to Initiator with R's ephemeral public key and R's static public key encrypted (96 bytes)
3. A message from Initiator to Responder with I's static public key encrypted (64 bytes)
These messages also contain additional MAC tags to ensure that data is not tampered with, and optional payload, which we do not use. In the `NOISE` extension, the client initiates the handshake and the server responds. The messages are sent over the network as a Base64 encoded line. 

You do not need to implement the encryption scheme yourself. Instead, you need to use the Noise reference implementation, that is, `noise-java`, which can be found on GitHub of `rweather` or `signalapp`. The fork of `signalapp` is available as a `.jar` file via the Maven Central Repository.

Study the Javadoc of the library. The most important class is the `HandshakeState` that is initialized for the `INITIATOR` (the client) or the `RESPONDER` (the server). The framework generates the *ephemeral* keys automatically. You do need to supply a local static key, which can be used to authenticate your client. A X25519 private key is 32 bytes long and typically generated using a secure random generator (for example, `SecureRandom` in Java). It is recommended to store this private key in a secure location. The accompanying public key, which can be shared publicly, is automatically generated from the private key and is also 32 bytes long. After supplying the local static key to the `HandshakeState`, use `start` to begin writing and reading the messages. After the three messages are sent and received, use the `split` method to obtain the pair of ciphers for further communication, that is, a "sender" cipher for encrypting messages to send to the other party and a "receiver" cipher for decrypting messages received from the other party. See also the Javadoc of `CipherState`. We do not use associated data.

# Adapted handshake
After both `HELLO` messages have been exchanged and both parties support the `NOISE` extension, the client **must** initiate encryption by sending the first Noise message. The server will then reply with the second message, after which the client must reply with the third message. Finally, the client continues the handshake with the `LOGIN` message, this time encrypted.

# Messages after key exchange
After the described sequence of three messages, both parties compute the send/receive ciphers. All further messages must now be encrypted using these ciphers. The messages are encrypted using the sender cipher, then Base64-encoded and send as a single line over the network, received, Base64-decoded and decrypted using the receiver cipher.

The decrypted version of each message should result in a valid (plaintext) command as defined in other places of the protocol. 

# Authentication
If a user logs in while using the `NOISE` extension to authenticate and encrypt, then the server must store the public static key of the user and forbid any attempts to login with that username that is not encrypted or has a different public static key. This ensures that no other party can use that username. 
* Use the `WRONGKEY` response if a client tries to login with a different public static key.
* Use the `ALREADYLOGGEDIN` response if the client does not support `NOISE`, i.e., trying to login without a public static key.

The public static key of the other party can be obtained from the `HandshakeState` using the `getRemotePublicKey` method.

## WRONGKEY (server)

Sent as a reply to a `LOGIN` command from the client, when the client attempts to login with a username that has a different public static key.

*Syntax*: `WRONGKEY`

# Example
*Start of initialization sequence*
- Client -> server: 
  `HELLO~Crispy Clean Client by Charlie~NOISE~RANK`
- Server -> client: 
  `HELLO~Sanne's Secret Server~NOISE`
- Client -> server: (Noise message 1)
  `8Bam4p6FNMWMS1dDHhHClh3ciH5fb4DnwJhfoTbucUs=`
- Server -> client: (Noise message 2)   `8BmbrPdaoMr0TuuQaT1iEEXgo4IZ8saGzo9K5rqjQVnutRJFoAkvKdItXqf4LI3XGoAWTJAi++TwKmiUlYjgXIKML1NeJKN20hPWEZyaYurZsGBpZy8QkJIbnPx2/PWZ`
- Client -> server: (Noise message 3)
  `Ev5QxO/G2I3VACi7zBkM+KA5QOfJKdUILl56b5CkRw9icWnjGOeZraMRLuFCM/rAXawcSMRyRPt2mSo/7+NMLQ==`
- Client -> server: (LOGIN message)
  `wDKg5tCoIvwU4FALmY2IPN9cTicromKlMFOO`
- Server -> client: (LOGIN confirmation)
  `ppUxGGwWo3CyPZPjwS4CHsUzpi48`
- Client -> server: (QUEUE command)
  `bujMfAZ7xDpUxzj4JH0iCltuQ8+8` 
