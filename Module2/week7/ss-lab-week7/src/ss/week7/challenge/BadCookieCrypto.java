package ss.week7.challenge;

import java.security.InvalidAlgorithmParameterException;
import java.security.InvalidKeyException;
import java.security.NoSuchAlgorithmException;
import java.security.SecureRandom;
import java.util.Arrays;

import javax.crypto.BadPaddingException;
import javax.crypto.Cipher;
import javax.crypto.IllegalBlockSizeException;
import javax.crypto.NoSuchPaddingException;
import javax.crypto.spec.IvParameterSpec;
import javax.crypto.spec.SecretKeySpec;

import org.apache.commons.codec.binary.Base64;

/**
 * A simple illustration of how confidentiality should not be confused
 * with integrity. As such, this code should not be used as an example of how
 * to do proper crypto! I repeat, do not use this approach!
 *
 */
public class BadCookieCrypto {
	private static final int KEY_SIZE = 16;
	private static final int IV_SIZE = 16;
	private byte[] key;
	SecureRandom rand = new SecureRandom();
	public BadCookieCrypto() {
		// Generate random key
		key = new byte[KEY_SIZE];
		rand.nextBytes(key);
	}
	
	public String createCookie() {
		// Generate the message to encrypt ('the cookie')
		byte[] message = "user=alice;isAdmin=N".getBytes();
	
		
		// Use a random 16 byte nonce IV (in this case, a nonce)
		byte[] iv = new byte[16];
		rand.nextBytes(iv);
		IvParameterSpec ivSpec = new IvParameterSpec(iv);
		
		SecretKeySpec secretKeySpec = new SecretKeySpec(key, "AES");
		try {
			// AES in CTR mode without padding (=> ciphertext length the same as plaintext length)
			Cipher cipher = Cipher.getInstance("AES/CTR/NoPadding");
			cipher.init(Cipher.ENCRYPT_MODE, secretKeySpec, ivSpec);
			byte[] ciphertext = cipher.doFinal(message);
			
			// Prepend the iv/nonce to the ciphertext
			byte[] rawResult = new byte[iv.length + ciphertext.length];
			System.arraycopy(iv, 0, rawResult, 0, iv.length);
			System.arraycopy(ciphertext, 0, rawResult, iv.length, ciphertext.length);
			// And return the Base64 encoded version of it.
			return Base64.encodeBase64String(rawResult);
		} catch (NoSuchAlgorithmException | NoSuchPaddingException | InvalidKeyException | 
				InvalidAlgorithmParameterException | IllegalBlockSizeException | BadPaddingException e) {
			e.printStackTrace();
		}
		// Whenever something bad happened, let's just return null. No cookie! :)
		return null;
	}
	
	public boolean isAdmin(String cookie) {
		// Let's first decode the Base64
		byte[] rawData = Base64.decodeBase64(cookie);
		byte[] iv = Arrays.copyOfRange(rawData, 0, IV_SIZE);
		byte[] ciphertext = Arrays.copyOfRange(rawData, IV_SIZE, rawData.length);
		
		// Decrypt
		IvParameterSpec ivSpec = new IvParameterSpec(iv);
		SecretKeySpec secretKeySpec = new SecretKeySpec(key, "AES");
		
		try {
			Cipher cipher = Cipher.getInstance("AES/CTR/NoPadding");
			cipher.init(Cipher.DECRYPT_MODE, secretKeySpec, ivSpec);
			byte[] plaintextRaw = cipher.doFinal(ciphertext);
			String plaintext = new String(plaintextRaw);
			return plaintext.endsWith(";isAdmin=Y");
		} catch (NoSuchAlgorithmException | NoSuchPaddingException | InvalidKeyException | 
				InvalidAlgorithmParameterException | IllegalBlockSizeException | BadPaddingException e) {
			e.printStackTrace();
		}
		// If something fails, return false.
		return false;
	}
}
