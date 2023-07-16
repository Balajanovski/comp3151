import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.IntStream;

public class Test {
    public static void test_single_thread(ISetFactory set_factory) throws InterruptedException {
        System.out.println("Testing single threaded functionality...");

        var set = set_factory.construct(2);
        set.insert(10);
        set.insert(10);
        set.insert(12);
        assert(set.member(10));
        assert(!set.member(9));
        assert(!set.member(11));
        assert(set.member(12));

        set.delete(10);
        assert(!set.member(10));
        assert(set.member(12));
    }

    public static void test_multiple_members(ISetFactory set_factory) throws InterruptedException {
        System.out.println("Testing multiple members...");

        int num_threads = 10;
        int N = 20000;
        int search_range = N/num_threads;

        var array = set_factory.construct(N);
        for (int i = N; i >= 1; --i) {
            array.insert(i*2);
        }

        long start_time = System.currentTimeMillis();

        var threads = new ArrayList<Thread>();
        for (int t = 0; t < num_threads; ++t) {
            int curr_t = t;
            var thread = new Thread(() -> {
                for (int i = (curr_t*search_range) + 1; i <= (curr_t+1)*search_range; ++i) {
                    assert(array.member(i*2));
                    assert(!array.member(i*2+1));
                }
            });

            thread.start();
            threads.add(thread);
        }

        for (var thread : threads) {
            thread.join();
        }

        long end_time = System.currentTimeMillis();
        System.out.println("\tMultiple members took: " + (end_time - start_time) + "ms");
    }

    public static void test_multiple_inserts(ISetFactory set_factory) throws InterruptedException {
        System.out.println("Testing multiple inserts...");

        int num_threads = 10;
        int N = 10000;
        int insert_range = N/num_threads;

        long start_time = System.currentTimeMillis();

        var threads = new ArrayList<Thread>();
        var array = set_factory.construct(N);
        for (int t = 0; t < num_threads; ++t) {
            int curr_t = t;
            var thread = new Thread(() -> {
                for (int i = (curr_t*insert_range) + 1; i <= (curr_t+1)*insert_range; ++i) {
                    try {
                        array.insert(i);
                    } catch (InterruptedException e) {
                        throw new RuntimeException(e);
                    }

                    assert(array.member(i));
                }
            });
            thread.start();

            threads.add(thread);
        }

        for (var thread : threads) {
            thread.join();
        }

        long end_time = System.currentTimeMillis();
        System.out.println("\tMultiple inserts took: " + (end_time - start_time) + "ms");

        assert(Arrays.equals(array.get_values(), IntStream.range(1, N + 1).toArray()));
    }

    public static void test_multiple_inserts_and_deletes(ISetFactory set_factory) throws InterruptedException {
        System.out.println("Testing multiple inserts and deletes...");

        int num_threads = 10;
        int N = 10000;
        int insert_range = N / num_threads;

        long start_time = System.currentTimeMillis();

        var threads = new ArrayList<Thread>();
        var array = set_factory.construct(N);
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

        long end_time = System.currentTimeMillis();
        System.out.println("\tMultiple inserts and deletes took: " + (end_time - start_time) + "ms");

        var actual_values = array.get_values();
        var expected_values = IntStream.range(1, N+1).filter(i -> i % 2 == 1).toArray();
        assert(Arrays.equals(actual_values, expected_values));
    }

    public static void main(String[] args) throws InterruptedException {
        var set_factories = List.<ISetFactory>of(new ConcurrentSetFactory(), new NaiveSetFactory());

        for (var factory : set_factories) {
            System.out.println("\n=-=-= Testing " + factory.get_name());

            //test_single_thread(factory);
            test_multiple_members(factory);
            test_multiple_inserts(factory);
            test_multiple_inserts_and_deletes(factory);
        }
    }
}
