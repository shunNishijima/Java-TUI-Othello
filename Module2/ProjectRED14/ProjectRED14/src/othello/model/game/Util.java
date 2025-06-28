package othello.model.game;

/**
 * This is the utility method to convert board alphabet to index.
 */
public class Util {
    /**
     * calculating from String code to index number.
     * @param field String code like "A1"
     * @return converted number as index.
     */
    /*@
        requires field!=null;
        ensures \result>=0&&\result<64;
    */
    public static int calculateField(String field)
    {
        field = field.toLowerCase();
        char[] splitField = field.toCharArray();
        int asciiLetter = splitField[0];
        asciiLetter = (asciiLetter - 98);
        try{
            int num = Character.getNumericValue(splitField[1]);
            return (8*(num-1)) + asciiLetter+1;
        }catch (ArrayIndexOutOfBoundsException e){
            System.out.println("input error");
            return -1;
        }
    }

    /**
     * for convenience, calculate smallest number in array.
     * @param ar array of index.
     * @return smallest number in specific array.
     */
    /*@
        requires ar.length>0;
        ensures ((\forall int i; i<ar.length; \result<=ar[i]));
    */
    public static int getSmallestIntIndex(int[] ar){
        int j = 9999999;
        int k = -1;
        for (int i = 0; i < ar.length; i++){
            if(ar[i] < j){
                j = ar[i];
                k = i;
            }
        }
        return k;
    }
}



