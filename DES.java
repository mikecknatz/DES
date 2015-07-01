/**
 * Michael Knatz
 * DES.java
 * This program is an implementation of DES in Electronic Codebook (ECB)
 * Style with limited use of the java.security.* classes and methods.
 * 
 * ECB breaks the messages into into 64bit blocks which, in this implementation, are padded
 * if necessary then written line by line into the given output file.
 * 
 * The program is set to be rather rigid in its implementation so options are not currently stackable, IE
 * you can not flag for a key generation then in the same run have it use the just generated key for
 * encryption.
 */
import java.util.Scanner;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintWriter;
import java.math.BigInteger;
import java.security.SecureRandom;

public class DES {
	//four flags for four options
	private static boolean keyflag = false;
	private static Scanner fileScan;
	private static boolean help = false;
	private static boolean encryptflag = false;
	private static boolean decflag = false;
	private static int [] INITIAL_PERM = {58,	50,	42,	34,	26,	18,	10,	2,	60,	52,	44,	36,	28,	20,	12,	4,	62,	54,	46,	38,	30,	22,	14,	6,64,	56,	48,	40,	32,	24,	16,	8,	57,	49,	41,	33,	25,	17,	9,	1,	59,	51,	43,	35,	27,	19,	11,	3,	61,	53,	45,	37,	29,	21,	13,	5,	63,	55,	47,	39,	31,	23,	15,	7};
	private static int [] FINAL_PERM = {40,	8,	48,	16,	56,	24,	64,	32,	39,	7,	47,	15,	55,	23,	63,	31,	38,	6,	46,	14,	54,	22,	62,	30,	37,	5,	45,	13,	53,	21,	61,	29,	36,	4,	44,	12,	52,	20,	60,	28,	35,	3,	43,	11,	51,	19,	59,	27,	34,	2,	42,	10,	50,	18,	58,	26,	33,	1,	41,	9,	49,	17,	57,	25};
	private static int [] EXPANSION = {32,	1,	2,	3,	4,	5,	4,	5,	6,	7,	8,	9,	8,	9,	10,	11,	12,	13,	12,	13,	14,	15,	16,	17,	16,	17,	18,	19,	20,	21,	20,	21,	22,	23,	24,	25,	24,	25,	26,	27,	28,	29,	28,	29,	30,	31,	32,	1};
	private static int [] PERM = {16,	7,	20,	21,	29,	12,	28,	17,	1,	15,	23,	26,	5,	18,	31,	10,	2,	8,	24,	14,	32,	27,	3,	9,	19,	13,	30,	6,	22,	11,	4,	25};
	private static String input;
	private static String output;
	private static String key;
	private static int [][] s1 = {{14, 4, 13, 1,	2,	15,	11,	8,	3,	10,	6,	12,	5,	9,	0,	7},
									{0,	15,	7,	4,	14,	2,	13,	1,	10,	6,	12,	11,	9,	5,	3,	8},
									{4,	1,	14,	8,	13,	6,	2,	11,	15,	12,	9,	7,	3,	10,	5,	0},
									{15,	12,	8,	2,	4,	9,	1,	7,	5,	11,	3,	14,	10,	0,	6,	13}};
	
	private static int [][] s2 = {{15,	1,	8,	14,	6,	11,	3,	4,	9,	7,	2,	13,	12,	0,	5,	10},
		{3,	13,	4,	7,	15,	2,	8,	14,	12,	0,	1,	10,	6,	9,	11,	5},
		{0,	14,	7,	11,	10,	4,	13,	1,	5,	8,	12,	6,	9,	3,	2,	15},
		{13,	8,	10,	1,	3,	15,	4,	2,	11,	6,	7,	12,	0,	5,	14,	9}};
	
	private static int [][] s3 = {{10,	0,	9,	14,	6,	3,	15,	5,	1,	13,	12,	7,	11,	4,	2,	8},
									{13,	7,	0,	9,	3,	4,	6,	10,	2,	8,	5,	14,	12,	11,	15,	1},
									{13,	6,	4,	9,	8,	15,	3,	0,	11,	1,	2,	12,	5,	10,	14,	7},
									{1,	10,	13,	0,	6,	9,	8,	7,	4,	15,	14,	3,	11,	5,	2,	12}};
	
	private static int [][] s4 = {{7,	13,	14,	3,	0,	6,	9,	10,	1,	2,	8,	5,	11,	12,	4,	15},
			{13,	8,	11,	5,	6,	15,	0,	3,	4,	7,	2,	12,	1,	10,	14,	9},
			{10,	6,	9,	0,	12,	11,	7,	13,	15,	1,	3,	14,	5,	2,	8,	4},
			{3,	    15,	0,	6,	10,	1,	13,	8,	9,	4,	5,	11,	12,	7,	2,	14}};
	
	private static int [][] s5 = {{2,	12,	4,	1,	7,	10,	11,	6,	8,	5,	3,	15,	13,	0,	14,	9},
		{14,	11,	2,	12,	4,	7,	13,	1,	5,	0,	15,	10,	3,	9,	8,	6},
		{4,	2,	1,	11,	10,	13,	7,	8,	15,	9,	12,	5,	6,	3,	0,	14},
		{11,	8,	12,	7,	1,	14,	2,	13,	6,	15,	0,	9,	10,	4,	5,	3}};
	private static int [][] s6 = {{12,	1,	10,	15,	9,	2,	6,	8,	0,	13,	3,	4,	14,	7,	5,	11},
		{10,	15,	4,	2,	7,	12,	9,	5,	6,	1,	13,	14,	0,	11,	3,	8},
		{9,	14,	15,	5,	2,	8,	12,	3,	7,	0,	4,	10,	1,	13,	11,	6},
		{4,	3,	2,	12,	9,	5,	15,	10,	11,	14,	1,	7,	6,	0,	8,	13}};
	private static int [][] s7 = {{4,	11,	2,	14,	15,	0,	8,	13,	3,	12,	9,	7,	5,	10,	6,	1},
		{13,	0,	11,	7,	4,	9,	1,	10,	14,	3,	5,	12,	2,	15,	8,	6},
		{1,	4,	11,	13,	12,	3,	7,	14,	10,	15,	6,	8,	0,	5,	9,	2},
		{6,	11,	13,	8,	1,	4,	10,	7,	9,	5,	0,	15,	14,	2,	3,	12}};
	private static int [][] s8 = {{13,	2,	8,	4,	6,	15,	11,	1,	10,	9,	3,	14,	5,	0,	12,	7},
		{1,	15,	13,	8,	10,	3,	7,	4,	12,	5,	6,	11,	0,	14,	9,	2},
		{7,	11,	4,	1,	9,	12,	14,	2,	0,	6,	10,	13,	15,	3,	5,	8},
		{2,	1,	14,	7,	4,	10,	8,	13,	15,	12,	9,	0,	3,	5,	6,	11}};
	
	private static int [] pc1 = {57,	49,	41,	33,	25,	17,	9, 1,	58,	50,	42,	34,	26,	18, 10,	2,	59,	51,	43,	35,	27, 19,	11,	3,	60,	52,	44,	36, 63,	55,	47,	39,	31,	23,	15,7,	62,	54,	46,	38,	30,	22,14,	6,	61,	53,	45,	37,	29,21,	13,	5,	28,	20,	12,	4};
	
	private static int [] pc2 = {14,	17,	11,	24,	1,	5,	3,	28,15,	6,	21,	10,	23,	19,	12,	4,26,	8,	16,	7,	27,	20,	13,	2,41,	52,	31,	37,	47,	55,	30,	40,51,	45,	33,	48,	44,	49,	39,	56,34,	53,	46,	42,	50,	36,	29,	32};

	
	private static int [] keySchd = {1,1,2,2,2,2,2,2,1,2,2,2,2,2,2,1};
	
	/**
	 * Simple main for the program, only acting to control the flow.
	 * 
	 * @param args gives the flags and file to be read and either encrypted or decrypted;
	 * see checkFlag(string []) for more details.
	 */
	public static void main(String [] args){
		checkFlag(args);
		// as mentioned, only 1 flag can be triggered at a time.
		if(help){
			return;
		}else if(keyflag){
			genKey();
			System.out.println(key);
		}else if(encryptflag){
			encrypt();
		}else if(decflag){
			decrypt();
		}
	}
	/**
	 * genKey() - private, void
	 * 
	 * Generates a 64 bit key using the SecureRandom() class
	 * then using the BigInteger class, prints a 16 length hexadecimal value
	 * that becomes the key for encryption and decryption.
	 */
	private static void genKey() {
		SecureRandom srand = new SecureRandom();
		byte [] keyStart = srand.generateSeed(8); //8 bytes = 64 bits;
		BigInteger temp = new BigInteger(keyStart).abs();
		key = temp.toString(16);
		//while rare, padding may be necessary for the full 16 length string
		while(key.length() < 16){
			key = '0' + key;
		}
	}
	/**
	 * encrypt() - private, void
	 * 
	 * using the given key, encrypts the message within the file
	 * and prints encoded blocks line by line into the output file 
	 */
	private static void encrypt() {
		String message = "";
		String inputS = "";
		String keyH = key;
		
		try {
			fileScan = new Scanner(new File(input));
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
		while(fileScan.hasNext()){
			inputS += fileScan.nextLine()+"\n";
		}
		//Pad with null characters to fill out remaining bytes
		while(inputS.length()%8 != 0){
			inputS += '\0';
		}
		//for later use
		String [] inbin = new String[inputS.length()/8] ;
		for(int i = 0; i < inbin.length; i++){
			String bit8 = inputS.substring(i*8, (i*8)+8);
			inbin[i] = "";
			for(int j = 0; j < 8; j++){
				inbin[i] += ("00000000" + Integer.toBinaryString(bit8.charAt(j))).substring(Integer.toBinaryString(bit8.charAt(j)).length());
			}
		}
		//convert key to binary string from its hex string
		String keyB = new BigInteger(keyH, 16).toString(2);
		//make sure of leading in key due to nature of tostring...
		while(keyB.length() < 64){
			keyB = "0" + keyB;
		}
		String keyB2 = "";
		//get the 56 bits of pc1
		for(int pc = 0; pc < pc1.length; pc++){
			keyB2 += keyB.charAt(pc1[pc]-1);
		}
		//get the 16 variations of the key schedule
		String keyVar[] = keySched(keyB2);
		//create the 16 48bit pieces from the compression pc-2
		String keyComp[] = new String[16];
		for(int i = 0; i < 16; i++){
			String temps = "";
			for(int j = 0; j < pc2.length; j++){
				temps += keyVar[i].charAt(pc2[j]-1);
			}
			keyComp[i] = temps;
		}
		//will be performed on each 64bit block
		for(int i = 0; i < inbin.length; i++){
			//Do initial permutation of the 64bit block
			String temp = "";
			for(int initial = 0; initial < 64; initial++){
				temp += inbin[i].charAt(INITIAL_PERM[initial]-1);
			}
			//break up the permuted block into left and right 
			String left = temp.substring(0,32);
			String right = temp.substring(32);
			//16 rounds of des
			for(int j = 0; j < 16; j++){
				//expand the right half out to 48 bits
				String expanded = "";
				for(int k = 0; k < EXPANSION.length; k++){
					expanded += right.charAt(EXPANSION[k]-1);
				}
				//XOR the expanded right with the compressed keySchedule item
				BigInteger temp1 = new BigInteger(expanded, 2);
				BigInteger temp2 = new BigInteger(keyComp[j],2);
				temp1 = temp1.xor(temp2);
				String xord = temp1.toString(2);
				//again pad due to toString not having a set length for leading 0s
				while(xord.length() < 48){
					xord = "0" + xord;
				}
				
				//DUBIOUS AREA TODO
				String sboxed = "";
				for(int next = 0; next < 48; next += 6){
					String piece = xord.substring(next, next+6);
					int row = Integer.parseInt(piece.charAt(0) + "" + piece.charAt(5) , 2);
					int col = Integer.parseInt(piece.substring(1, 5), 2);
					if(next/6 == 0){
						sboxed += ("0000" + Integer.toString(s1[row][col], 2)).substring(Integer.toString(s1[row][col], 2).length());
					}else if(next/6 == 1){
						sboxed += ("0000" + Integer.toString(s2[row][col], 2)).substring(Integer.toString(s2[row][col], 2).length());
					}else if(next/6 == 2){
						sboxed += ("0000" + Integer.toString(s3[row][col], 2)).substring(Integer.toString(s3[row][col], 2).length());
					}else if(next/6 == 3){
						sboxed += ("0000" + Integer.toString(s4[row][col], 2)).substring(Integer.toString(s4[row][col], 2).length());
					}else if(next/6 == 4){
						sboxed += ("0000" + Integer.toString(s5[row][col], 2)).substring(Integer.toString(s5[row][col], 2).length());
					}else if(next/6 == 5){
						sboxed += ("0000" + Integer.toString(s6[row][col], 2)).substring(Integer.toString(s6[row][col], 2).length());
					}else if(next/6 == 6){
						sboxed += ("0000" + Integer.toString(s7[row][col], 2)).substring(Integer.toString(s7[row][col], 2).length());
					}else{
						sboxed += ("0000" + Integer.toString(s8[row][col], 2)).substring(Integer.toString(s8[row][col], 2).length());
					}
				}
				//System.out.println(sboxed);
				String permBox = "";
				for(int k = 0; k < PERM.length; k++){
					permBox += sboxed.charAt(PERM[k]-1);
				}
				//L[i] = R[i-1] R[i] = L[i-1] XOR f(R[i-1], k[i])
				temp1 = new BigInteger(permBox,2);
				temp2 = new BigInteger(left,2);
				temp1 = temp1.xor(temp2);
				left = right;
				right = temp1.toString(2);
				//keep padding
				while(right.length() < 32){
					right = 0 + right;
				}	
			}
			String stuff = right + left;
			for(int next = 0; next < FINAL_PERM.length; next++){
				message += stuff.charAt(FINAL_PERM[next]-1);
			}
		}
		String tempmes =  new BigInteger(message,2).toString(16);
		try {
			PrintWriter outfile = new PrintWriter(new FileOutputStream(output));
			for(int i = 0; i < tempmes.length(); i+=16){
				outfile.println(tempmes.substring(i,i+16));
			}
			outfile.close();
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	/**
	 * decrypt() - private, void
	 * 
	 * using the given key, decrypts the message within the file
	 * and prints the message into the output file 
	 */
	private static void decrypt() {
		String message = "";
		String inputS = "";
		String keyH = key;
		try {
			fileScan = new Scanner(new File(input));
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
		while(fileScan.hasNext()){
			inputS += fileScan.nextLine();
		}
		//Pad with null characters to fill out remaining bytes
		while(inputS.length()%16 != 0){
			inputS = "0" + inputS;
		}
		//System.out.println(new BigInteger(d,16).toString(2).length());
		String [] inbin = new String[inputS.length()/16] ;
		for(int i = 0; i < inbin.length; i++){
			String Hex8 = inputS.substring(i*16, (i*16)+16);
			inbin[i] = new BigInteger(Hex8,16).toString(2);
			while(inbin[i].length() < 64){
				inbin[i] = "0" + inbin[i];
			}
		}
		//convert key to binary string from its hex string
		String keyB = new BigInteger(keyH, 16).toString(2);
		//make sure of leading in key due to nature of tostring...
		while(keyB.length() < 64){
			keyB = "0" + keyB;
		}
		String keyB2 = "";
		//get the 56 bits of pc1
		for(int pc = 0; pc < pc1.length; pc++){
			keyB2 += keyB.charAt(pc1[pc]-1);
		}
		//get the 16 variations of the key schedule
		String keyVar[] = keySched(keyB2);
		//create the 16 48bit pieces from the compression pc-2
		String keyComp[] = new String[16];
		for(int i = 0; i < 16; i++){
			String temps = "";
			for(int j = 0; j < pc2.length; j++){
				temps += keyVar[i].charAt(pc2[j]-1);
			}
			keyComp[i] = temps;
		}
		//will be performed on each 64bit block
		for(int i = 0; i < inbin.length; i++){
			//Do initial permutation of the 64bit block
			String temp = "";
			for(int initial = 0; initial < 64; initial++){
				temp += inbin[i].charAt(INITIAL_PERM[initial]-1);
			}
			//break up the permuted block into left and right 
			String left = temp.substring(0,32);
			String right = temp.substring(32);
			//16 rounds of des
			for(int j = 0; j < 16; j++){
				//expand the right half out to 48 bits
				String expanded = "";
				for(int k = 0; k < EXPANSION.length; k++){
					expanded += right.charAt(EXPANSION[k]-1);
				}
				//XOR the expanded right with the compressed keySchedule item
				BigInteger temp1 = new BigInteger(expanded, 2);
				BigInteger temp2 = new BigInteger(keyComp[15-j],2);
				temp1 = temp1.xor(temp2);
				String xord = temp1.toString(2);
				//again pad due to toString not having a set length for leading 0s
				while(xord.length() < 48){
					xord = "0" + xord;
				}
				
				//DUBIOUS AREA TODO
				String sboxed = "";
				for(int next = 0; next < 48; next += 6){
					String piece = xord.substring(next, next+6);
					int row = Integer.parseInt(piece.charAt(0) + "" + piece.charAt(5) , 2);
					int col = Integer.parseInt(piece.substring(1, 5), 2);
					if(next/6 == 0){
						sboxed += ("0000" + Integer.toString(s1[row][col], 2)).substring(Integer.toString(s1[row][col], 2).length());
					}else if(next/6 == 1){
						sboxed += ("0000" + Integer.toString(s2[row][col], 2)).substring(Integer.toString(s2[row][col], 2).length());
					}else if(next/6 == 2){
						sboxed += ("0000" + Integer.toString(s3[row][col], 2)).substring(Integer.toString(s3[row][col], 2).length());
					}else if(next/6 == 3){
						sboxed += ("0000" + Integer.toString(s4[row][col], 2)).substring(Integer.toString(s4[row][col], 2).length());
					}else if(next/6 == 4){
						sboxed += ("0000" + Integer.toString(s5[row][col], 2)).substring(Integer.toString(s5[row][col], 2).length());
					}else if(next/6 == 5){
						sboxed += ("0000" + Integer.toString(s6[row][col], 2)).substring(Integer.toString(s6[row][col], 2).length());
					}else if(next/6 == 6){
						sboxed += ("0000" + Integer.toString(s7[row][col], 2)).substring(Integer.toString(s7[row][col], 2).length());
					}else{
						sboxed += ("0000" + Integer.toString(s8[row][col], 2)).substring(Integer.toString(s8[row][col], 2).length());
					}
				}
				//System.out.println(sboxed);
				String permBox = "";
				for(int k = 0; k < PERM.length; k++){
					permBox += sboxed.charAt(PERM[k]-1);
				}
				//L[i] = R[i-1] R[i] = L[i-1] XOR f(R[i-1], k[i])
				temp1 = new BigInteger(permBox,2);
				temp2 = new BigInteger(left,2);
				temp1 = temp1.xor(temp2);
				left = right;
				right = temp1.toString(2);
				//keep padding
				while(right.length() < 32){
					right = 0 + right;
				}	
			}
			String stuff = right + left;
			for(int next = 0; next < FINAL_PERM.length; next++){
				message += stuff.charAt(FINAL_PERM[next]-1);
			}
		}
		String tempmes = "";
		for(int i = 0; i < message.length(); i +=8){//
			tempmes += (char)Integer.parseInt(message.substring(i, i+8),2);
		}
		try {
			PrintWriter outfile = new PrintWriter(new FileOutputStream(output));
			outfile.print(tempmes.substring(0, tempmes.lastIndexOf('\n')));
			outfile.close();
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	/**
	 * keySched(String) - private, String
	 * 
	 * Create the 16 keys that will be used for the DES implementation,
	 * for more information please see DES wiki on Key Schedules.
	 */
	private static String[] keySched(String s){
		String [] k = new String [16];
		String left, right;
		left = s.substring(0,28);
		right = s.substring(28);
		for(int i = 0; i < 16; i++){
			//split at first
			//shift bits(using strings)
			String t1 = left.substring(0,keySchd[i]);
			left = left.substring(keySchd[i]) + right.substring(0, keySchd[i]);
			right = right.substring(keySchd[i]) + t1;
			k[i] = left+right;
		}
		return k;
		
	}
	
	/**
	 * checkFlag(string []) - private, void
	 * 
	 * simple method to check for and process correct input given from the command line.
	 * 
	 * @param args - flags given on command line.
	 * 
	 * will be reworking this at a later time to give the program more versatility.
	 */
	private static void checkFlag(String[] args) {
		if(args[0].equals("-h") || args.length < 6){
			System.out.println("options:");
			System.out.println("-h    : Shows this menu");
			System.out.println("-k    : Generates a 64-bit key then printed in hex");
			System.out.println("-e <64 bit key in hex> -i <input file> -o <output file>    :" +
					"Encrypts the input file and places the encrypted file into the specified output file ");
			System.out.println("-d <64 bit key in hex> -i <input file> -o <output file>    :" +
					"Decrypts the input file and places the decrypted file into the specified output file ");
			help = true;
		}else if(args[0].equals("-k")){
			keyflag = true;
		}else if(args[0].equals("-e")){
			encryptflag = true;
			key = args[1];
			input = args[3];
			output = args[5];
		}else if(args[0].equals("-d")){
			decflag = true;
			key = args[1];
			input = args[3];
			output = args[5];
		}else{
			System.out.println("options:");
			System.out.println("-h    : Shows this menu");
			System.out.println("-k    : Generates a 64-bit key then printed in hex");
			System.out.println("-e <64 bit key in hex> -i <input file> -o <output file>    :" +
					"Encrypts the input file and places the encrypted file into the specified output file ");
			System.out.println("-d <64 bit key in hex> -i <input file> -o <output file>    :" +
					"Decrypts the input file and places the decrypted file into the specified output file ");
			help = true;
		}
		
	}
}
