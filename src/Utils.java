package group92.spectrangle;

import java.util.List;

public class Utils {

    public static int[] IntegerListToArray(List<Integer> list) {
        int[] result = new int[list.size()];
        for (int i = 0; i < result.length; i++) {
            result[i] = list.get(i);
        }
        return result;
    }

}
