import java.util.Arrays;
import java.util.LinkedList;
import java.util.Queue;
import java.util.concurrent.Semaphore;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReadWriteLock;
import java.util.concurrent.locks.ReentrantLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;
import java.util.stream.Stream;

public class SortedArray {
    // -1 encodes a deleted member
    // 0 encodes array padding

    private final int N;
    private int[] values;
    private AtomicInteger size;

    private Lock[] insert_region_locks;
    private Lock[] swap_locks;
    private Semaphore size_semaphore;

    public SortedArray(int N) {
        this.N = N;
        this.size_semaphore = new Semaphore(N);
        this.size = new AtomicInteger(0);
        this.values = new int[N+2];
        this.insert_region_locks = Stream.iterate(0, x->x+1)
                .limit(N+2)
                .map(i -> new ReentrantLock())
                .toArray(ReentrantLock[]::new);
        this.swap_locks = Stream.iterate(0, x->x+1)
                .limit(N+2)
                .map(i -> new ReentrantLock())
                .toArray(ReentrantLock[]::new);

        this.values[0] = Integer.MIN_VALUE;
        this.values[1] = Integer.MAX_VALUE;
        for (int i = 2; i < N+2; ++i) {
            this.values[i] = 0;
        }
    }

    public void insert(int x) throws InterruptedException {
        assert (x > 0);

        this.size_semaphore.acquire();

        //this.cleanup();

        // Hand over hand locking
        int region_left = -1; // Value of -1 means that an insertion position has not been found
        this.insert_region_locks[0].lock();
        for (int i = 1; i < N+1; ++i) {
            this.insert_region_locks[i].lock();

            if (this.values[i] == x) {
                // Handle duplicate

                this.insert_region_locks[i-1].unlock();
                this.insert_region_locks[i].unlock();
                this.size_semaphore.release();

                return;
            } else if (this.values[i] > x) {
                region_left = i;
                break;
            }

            this.insert_region_locks[i-1].unlock();
        }

        // If this ever occurs this means there is no more space left
        // this should never happen with our size semaphore
        assert(region_left != -1);

        this.insert_region_locks[region_left-1].unlock();


        // Find right side of insertion region
        int region_right = -1;
        if (this.values[region_left] <= 0) {
            region_right = region_left;
        } else {
            for (int i = region_left+1; i < N+2; ++i) {
                this.insert_region_locks[i].lock();
                if (this.values[i] <= 0) {
                    region_right = i;
                    break;
                }
            }
        }

        // If this ever occurs this means there is no more space left
        // this should never happen with our size semaphore
        assert(region_right != -1);
        assert(this.values[region_right] <= 0);

        // Insert x into desired position
        this.values[region_right] = -1;
        for (int i = region_right; i >= region_left+1; --i) {
            // Try lock to prevent deadlock. Let any searches finish first before swapping in
            // Read priority. However, this can lead to write starvation.
            boolean lock_acquired = false;
            while (!lock_acquired) {
                if (!this.swap_locks[i-1].tryLock()) {
                    continue;
                } if (!this.swap_locks[i].tryLock()) {
                    this.swap_locks[i-1].unlock();
                    continue;
                }

                lock_acquired = true;
            }

            int temp = this.values[i-1];
            this.values[i-1] = this.values[i];
            this.values[i] = temp;

            this.swap_locks[i-1].unlock();
            this.swap_locks[i].unlock();
        }

        assert(this.values[region_left] == -1);

        this.values[region_left] = x;

        // Unlock the array
        for (int i = region_left; i <= region_right; ++i) {
            this.insert_region_locks[i].unlock();
        }

        // Update size
        this.size.addAndGet(1);
    }

    public int get_size() {
        return size.get();
    }

    public int[] get_values() {
        return Arrays.copyOfRange(values, 1, N+1);
    }

    public void delete(int x) {
        assert (x > 0);

        int x_index = find(x);
        if (x_index != -1) {
            this.values[x_index] = -1;
            this.swap_locks[x_index].unlock();
        }

        this.size_semaphore.release();
        this.size.addAndGet(-1);
    }

    public boolean member(int x) {
        int x_index = find(x);
        if (x_index != -1) {
            this.swap_locks[x_index].unlock();
            return true;
        } else {
            return false;

        }
        return isMember;
    }

    public void print_sorted() {
        this.swap_locks[0].lock();
        for (int i = 1; i < N+2; ++i) {
            this.swap_locks[i].lock();
            if (values[i] == Integer.MAX_VALUE) {
                this.swap_locks[i-1].unlock();
                this.swap_locks[i].unlock();
                return;
            }

            if (values[i] > 0) {
                System.out.println(values[i]);
            }

            this.swap_locks[i-1].unlock();
        }
        this.swap_locks[N+1].unlock();
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
        this.swap_locks[low].lock();
        this.swap_locks[high].lock();

        while (low <= high) {
            int mid = low + (high - low) / 2;

            // Lock ensures that swaps are atomic
            this.swap_locks[mid].lock();
            int mid_value = this.values[mid];

            if (mid_value == -1) {
                // Search right
                boolean found_mid = false;
                int currently_locked = mid;
                for (int i = mid+1; i <= high; ++i) {
                    this.swap_locks[i].lock();
                    this.swap_locks[currently_locked].unlock();
                    currently_locked = i;

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
                        this.swap_locks[i].lock();
                        this.swap_locks[currently_locked].unlock();
                        currently_locked = i;

                        mid_value = this.values[i];

                        if (mid_value > 0) {
                            mid = i;
                            found_mid = true;
                            break;
                        }
                    }
                }

                if (!found_mid) {
                    this.swap_locks[currently_locked].unlock();
                    break;
                }
            }

            if (mid_value == 0 || mid_value > x) {
                this.swap_locks[mid-1].lock();
                this.swap_locks[high].unlock();
                this.swap_locks[mid].unlock();
                high = mid-1;
            } else if (mid_value < x) {
                this.swap_locks[mid+1].lock();
                this.swap_locks[low].unlock();
                this.swap_locks[mid].unlock();
                low = mid+1;
            } else {
                x_index = mid;
                break;
            }
        }

        this.swap_locks[low].unlock();
        this.swap_locks[high].unlock();

        return x_index;
    }
}
