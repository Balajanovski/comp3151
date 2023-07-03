import java.util.ArrayList;
import java.util.Arrays;
import java.util.stream.IntStream;

public class Test {
    public static void test_single_thread() throws InterruptedException {
        System.out.println("Testing single threaded functionality...");

        var array = new SortedArray(2);
        array.insert(10);
        array.insert(10);
        array.insert(12);
        assert(array.member(10));
        assert(!array.member(9));
        assert(!array.member(11));
        assert(array.member(12));

        array.delete(10);
        assert(!array.member(10));
        assert(array.member(12));
    }

    public static void test_multiple_inserts() throws InterruptedException {
        System.out.println("Testing multiple inserts...");

        int num_threads = 10;
        int insert_range = 10;
        int N = num_threads*insert_range;

        var threads = new ArrayList<Thread>();
        var array = new SortedArray(N);
        for (int t = 0; t < num_threads; ++t) {
            int curr_t = t;
            var thread = new Thread(() -> {
                for (int i = (curr_t*insert_range) + 1; i <= (curr_t+1)*insert_range; ++i) {
                    try {
                        array.insert(i);
                        assert(array.member(i));
                    } catch (InterruptedException e) {
                        throw new RuntimeException(e);
                    }
                }
            });
            thread.start();

            threads.add(thread);
        }

        for (var thread : threads) {
            thread.join();
        }

        assert(array.get_size() == N);
        assert(Arrays.equals(array.get_values(), IntStream.range(1, N + 1).toArray()));
    }

    public static void test_multiple_inserts_and_deletes() throws InterruptedException {
        System.out.println("Testing multiple inserts and deletes...");

        int num_threads = 10;
        int insert_range = 10;
        int N = num_threads*insert_range;

        var threads = new ArrayList<Thread>();
        var array = new SortedArray(num_threads*insert_range);
        for (int t = 0; t < num_threads; ++t) {
            int curr_t = t;
            var thread = new Thread(() -> {
                for (int i = (curr_t*insert_range) + 1; i <= (curr_t+1)*insert_range; ++i) {
                    try {
                        array.insert(i);
                        assert(array.member(i));
                    } catch (InterruptedException e) {
                        throw new RuntimeException(e);
                    }
                }

                for (int i = (curr_t*insert_range) + 1; i <= (curr_t+1)*insert_range; ++i) {
                    if (i % 2 == 0) {
                        array.delete(i);
                        assert(!array.member(i));
                    }
                }
            });
            thread.start();

            threads.add(thread);
        }

        for (var thread : threads) {
            thread.join();
        }

        assert(array.get_size() == N/2);
    }

    public static void main(String[] args) throws InterruptedException {
        test_single_thread();
        test_multiple_inserts();
        test_multiple_inserts_and_deletes();
    }
}
