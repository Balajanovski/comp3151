import java.util.concurrent.Semaphore;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;
import java.util.stream.Stream;

public class SortedArray {
    private final int N;
    private int[] values;
    private AtomicInteger size;

    private Lock[] mutation_locks;
    private Lock[] read_locks;
    private Semaphore size_semaphore;

    public SortedArray(int N) {
        this.N = N;
        this.size_semaphore = new Semaphore(N);
        this.size = new AtomicInteger(0);
        this.values = new int[N+2];
        this.mutation_locks = Stream.iterate(0, x->x+1)
                .limit(N+2)
                .map(i -> new ReentrantLock())
                .toArray(ReentrantLock[]::new);
        this.read_locks = Stream.iterate(0, x->x+1)
                .limit(N+2)
                .map(i -> new ReentrantLock())
                .toArray(ReentrantLock[]::new);
        this.values[0] = Integer.MIN_VALUE;
        this.values[1] = Integer.MAX_VALUE;
    }

    public void insert(int x) throws InterruptedException {
        assert (x > 0);

        this.size_semaphore.acquire();

        //this.cleanup();

        // Two phase solution
        // Phase 1: Find insertion location (write locks) (Potentially look at ReadWriteUpdate lock)
        // Phase 2: Lock remainder of array and insert (write locks)

        // Hand over hand locking
        int insertion_pos = -1; // Value of -1 means that an insertion position has not been found
        this.mutation_locks[0].lock();
        for (int i = 1; i < N+1 && insertion_pos == -1; ++i) {
            this.mutation_locks[i].lock();

            if (this.values[i] == x) {
                this.mutation_locks[i-1].unlock();
                this.mutation_locks[i].unlock();
                return;
            } else if (Math.abs(this.values[i]) > x) {
                insertion_pos = i;
                break;
            }

            this.mutation_locks[i-1].unlock();
        }

        if (insertion_pos == -1) {
            // Safely unlock. However, if a process ever gets here
            // something has gone DREADFULLY wrong
            // TODO: Check this never happens
            this.mutation_locks[N+1].unlock();
            return;
        }

        // At this point, the lock should be held at insertion_pos!
        // TODO: Validate it

        // Lock the right of the array
        // till the first zero
        int lock_end = N+1;
        for (int i = insertion_pos+1; i < N+2; ++i) {
            this.mutation_locks[i].lock();

            if (this.values[i] < 0) {
                lock_end = i;
                break;
            }
        }

        // Insert x into desired position
        for (int i = lock_end; i >= insertion_pos+1; --i) {
            this.read_locks[i-1].lock();
            this.read_locks[i].lock();

            int temp = this.values[i-1];
            this.values[i-1] = this.values[i];
            this.values[i] = temp;

            this.read_locks[i-1].unlock();
            this.read_locks[i].unlock();
        }

        assert(this.values[insertion_pos] < 0);
        this.values[insertion_pos] = x;

        // Update size
        this.size.addAndGet(1);

        // Unlock the array
        for (int i = insertion_pos-1; i <= lock_end; ++i) {
            this.mutation_locks[i].unlock();
        }
    }

    public int get_size() {
        return size.get();
    }

    public void delete(int x) {
        assert (x > 0);

        this.size_semaphore.release();
    }

    public boolean member(int x) {
        // -1 encodes a deleted member
        // 0 encodes array padding

        int low = 0;
        int high = N-1;

        while (low <= high) {
            int mid = low + (high - low) / 2;
        }
    }

    public void print_sorted() {
        this.read_locks[0].lock();
        for (int i = 1; i < N+2; ++i) {
            this.read_locks[i].lock();
            if (values[i] == Integer.MAX_VALUE) {
                this.read_locks[i-1].unlock();
                this.read_locks[i].unlock();
                return;
            }

            if (values[i] > 0) {
                System.out.println(values[i]);
            }

            this.read_locks[i-1].unlock();
        }
        this.read_locks[N+1].unlock();
    }

    public void cleanup() {

    }
}
