import java.util.Arrays;
import java.util.concurrent.Semaphore;
import java.util.concurrent.locks.ReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

public class NaiveSet implements ISet {
    private final int PADDING = 0;

    private final int N;
    private int[] values;

    private ReadWriteLock rw_lock;

    private Semaphore size_semaphore;

    public NaiveSet(int N) {
        this.N = N;
        this.size_semaphore = new Semaphore(N, true);
        this.values = new int[N+2];
        this.rw_lock = new ReentrantReadWriteLock(true);

        this.values[0] = Integer.MIN_VALUE;
        this.values[1] = Integer.MAX_VALUE;
        for (int i = 2; i < N+2; ++i) {
            this.values[i] = PADDING;
        }
    }

    public void insert(int x) throws InterruptedException {
        assert (x > 0);

        this.rw_lock.writeLock().lock();

        // Find left of insertion region
        int region_left = -1;
        for (int i = 1; i < N+2 && region_left == -1; ++i) {
            if (this.values[i] == x) {
                this.size_semaphore.release();
                this.rw_lock.writeLock().unlock();
                return;
            } else if (this.values[i] > x) {
                region_left = i;
            }
        }
        assert(region_left != -1);

        // Find right of insertion region
        int region_right = -1;
        for (int i = region_left+1; i < N+2 && region_right == -1; ++i) {
            if (this.values[i] == PADDING) {
                region_right = i;
            }
        }
        assert(region_right != -1);

        // Shift values
        for (int i = region_right; i >= region_left+1; --i) {
            this.values[i] = this.values[i-1];
        }
        this.values[region_left] = x;

        this.rw_lock.writeLock().unlock();
    }

    public int[] get_values() {
        // Not thread-safe but only used for testing
        return Arrays.stream(values).filter(i -> (i != Integer.MAX_VALUE && i > 0)).toArray();
    }

    public void delete(int x) {
        assert (x > 0);

        this.rw_lock.writeLock().lock();

        int x_index = find(x);
        if (x_index != -1) {
            this.values[x_index] = -1;

            for (int i = x_index+1; i < N+2; ++i) {
                this.values[i-1] = this.values[i];
            }
            this.values[N+1] = 0;

            this.size_semaphore.release();
        }

        this.rw_lock.writeLock().unlock();
    }

    public boolean member(int x) {
        int x_index = find(x);
        return (x_index != -1);
    }

    public void print_sorted() {
        this.rw_lock.readLock().lock();

        for (int i = 1; i < N+2; ++i) {
            if (values[i] == Integer.MAX_VALUE) {
                this.rw_lock.readLock().unlock();
                return;
            }

            if (values[i] > 0) {
                System.out.println(values[i]);
            }
        }

        this.rw_lock.readLock().unlock();
    }

    public void cleanup() { }

    // =-=-=-=-=-=-=-=-
    // Helper functions
    // =-=-=-=-=-=-=-=-

    private int find(int x) {
        int low = 1;
        int high = N+1;
        int x_index = -1;

        this.rw_lock.readLock().lock();

        while (low <= high) {
            int mid = low + (high - low) / 2;

            int mid_value = this.values[mid];
            if (mid_value == 0 || mid_value > x) {
                high = mid-1;
            } else if (mid_value < x) {
                low = mid+1;
            } else {
                x_index = mid;
                break;
            }
        }

        this.rw_lock.readLock().unlock();

        return x_index;
    }
}
