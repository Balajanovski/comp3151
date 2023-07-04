import java.util.Arrays;
import java.util.concurrent.Semaphore;
import java.util.concurrent.locks.ReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;
import java.util.stream.Stream;

public class SortedArray {
    private final int DELETED = -1;
    private final int PADDING = 0;

    private final int N;
    private int[] values;

    private ReadWriteLock[] region_locks;

    private Semaphore size_semaphore;

    public SortedArray(int N) {
        this.N = N;
        this.size_semaphore = new Semaphore(N);
        this.values = new int[N+2];

        this.region_locks = Stream.iterate(0, x->x+1)
                .limit(N+2)
                .map(i -> new ReentrantReadWriteLock())
                .toArray(ReentrantReadWriteLock[]::new);

        this.values[0] = Integer.MIN_VALUE;
        this.values[1] = Integer.MAX_VALUE;
        for (int i = 2; i < N+2; ++i) {
            this.values[i] = PADDING;
        }
    }

    public void insert(int x) throws InterruptedException {
        assert (x > 0);

        // Find left of insertion region
        int region_left = -1;
        this.region_locks[0].writeLock().lock();
        for (int i = 1; i < N+2 && region_left == -1; ++i) {
            this.region_locks[i].writeLock().lock();

            if (this.values[i] == x) {
                for (int j = 0; j <= i; ++j) {
                    this.region_locks[j].writeLock().unlock();
                }

                this.size_semaphore.release();
                return;
            } else if (this.values[i] > x) {
                region_left = i;
            }
        }
        assert(region_left != -1);

        // Find right of insertion region
        int region_right = -1;
        for (int i = region_left+1; i < N+2 && region_right == -1; ++i) {
            this.region_locks[i].writeLock().lock();
            if (this.values[i] == DELETED || this.values[i] == PADDING) {
                region_right = i;
            }
        }
        assert(region_right != -1);

        // Shift values
        for (int i = region_right; i >= region_left+1; --i) {
            this.values[i] = this.values[i-1];
        }
        this.values[region_left] = x;

        // Unlock array
        for (int i = 0; i <= region_right; ++i) {
            this.region_locks[i].writeLock().unlock();
        }
    }

    public int[] get_values() {
        return Arrays.stream(values).filter(i -> (i != Integer.MAX_VALUE && i > 0)).toArray();
    }

    public void delete(int x) {
        assert (x > 0);

        int x_index = find(x);
        if (x_index != -1) {
            this.values[x_index] = -1;
        }

        this.size_semaphore.release();
    }

    public boolean member(int x) {
        int x_index = find(x);
        return (x_index != -1);
    }

    public void print_sorted() {
        // Hand over hand locking to
        // prevent any inserts from modifying
        // past the read head
        this.region_locks[0].readLock().lock();
        for (int i = 1; i < N+2; ++i) {
            this.region_locks[i].readLock().lock();
            if (values[i] == Integer.MAX_VALUE) {
                this.region_locks[i-1].readLock().unlock();
                this.region_locks[i].readLock().unlock();
                return;
            }

            if (values[i] > 0) {
                System.out.println(values[i]);
            }

            this.region_locks[i-1].readLock().unlock();
        }
        this.region_locks[N+1].readLock().unlock();
    }

    public void cleanup() {

    }

    // =-=-=-=-=-=-=-=-
    // Helper functions
    // =-=-=-=-=-=-=-=-

    private int find(int x) {
        int low = 0;
        int high = N+1;
        int x_index = -1;

        // Locking left and right of binary search prevents
        // swaps travelling over a binary search region
        // and potentially invalidating it
        this.region_locks[low].readLock().lock();

        while (low <= high) {
            int mid = low + (high - low) / 2;

            int mid_value = this.values[mid];

            if (mid_value == -1) {
                // Search right
                boolean found_mid = false;
                for (int i = mid+1; i <= high; ++i) {

                    mid_value = this.values[i];

                    if (mid_value > 0) {
                        mid = i;
                        found_mid = true;
                        break;
                    } else if (mid_value == 0) {
                        // We have found the boundary of the array
                        // Early exit
                        break;
                    }
                }

                // Search left if not found a "midpoint"
                if (!found_mid) {
                    for (int i = mid-1; i >= low; --i) {

                        mid_value = this.values[i];

                        if (mid_value > 0) {
                            mid = i;
                            found_mid = true;
                            break;
                        }
                    }
                }

                if (!found_mid) {
                    break;
                }
            }

            if (mid_value == 0 || mid_value > x) {
                high = mid-1;
            } else if (mid_value < x) {
                this.region_locks[mid+1].readLock().lock();
                this.region_locks[low].readLock().unlock();
                low = mid+1;
            } else {
                x_index = mid;
                break;
            }
        }

        this.region_locks[low].readLock().unlock();

        return x_index;
    }
}
