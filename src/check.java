public class check {
    public static void main(String[] args) {
        byte[] result = new byte[2];
        result[0] = (byte) ((Integer.parseInt("001",3) << 5) + (Integer.parseInt("010") << 2) + 2);
        System.out.println((Integer.parseInt("001") << 5));
        String s1 = String.format("%8s",(Integer.parseInt("001") << 5));
        System.out.println(s1);
        result[1] = (byte) ((2 << 6) + (0 << 5) + 5);
        String s2 = String.format("%8s", Integer.toBinaryString(result[1] & 0xFF)).replace(' ', '0');
        System.out.println(s2);
    }
}
