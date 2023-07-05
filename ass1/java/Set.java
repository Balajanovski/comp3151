import java.util.Arrays;
import java.util.concurrent.Semaphore;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.locks.ReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;
import java.util.stream.Stream;

public class Set {
    private final int DELETED = -1;
    private final int PADDING = 0;

    private final double MIN_HOLE_PERCENT_CLEANUP = 0.2;
    private final int MIN_ARRAY_SIZE_CLEANUP = 20;

    private final int N;
    private int[] values;

    private AtomicInteger uncompacted_size;
    private AtomicInteger num_holes;

    private ReadWriteLock[] region_locks;
    private ReadWriteLock cleanup_lock;

    private Semaphore size_semaphore;

    public Set(int N) {
        this.N = N;
        this.size_semaphore = new Semaphore(N);
        this.values = new int[N+2];

        this.region_locks = Stream.iterate(0, x->x+1)
                .limit(N+2)
                .map(i -> new ReentrantReadWriteLock())
                .toArray(ReentrantReadWriteLock[]::new);
        this.cleanup_lock = new ReentrantReadWriteLock();

        this.values[0] = Integer.MIN_VALUE;
        this.values[1] = Integer.MAX_VALUE;
        for (int i = 2; i < N+2; ++i) {
            this.values[i] = PADDING;
        }

        this.uncompacted_size = new AtomicInteger(0);
        this.num_holes = new AtomicInteger(0);
    }

    public void insert(int x) throws InterruptedException {
        assert (x > 0);

        this.cleanup_lock.readLock().lock();

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
                this.cleanup_lock.readLock().unlock();
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

        this.uncompacted_size.incrementAndGet();
        this.cleanup_lock.readLock().unlock();
    }

    public int[] get_values() {
        return Arrays.stream(values).filter(i -> (i != Integer.MAX_VALUE && i > 0)).toArray();
    }

    public void delete(int x) {
        assert (x > 0);

        int x_index = find(x, true);
        if (x_index != -1) {
            this.values[x_index] = -1;
            this.region_locks[x_index].writeLock().unlock();
        }

        this.size_semaphore.release();

        var curr_num_holes = (double) this.num_holes.incrementAndGet();
        var curr_uncompacted_size = (double) this.uncompacted_size.get();
        var hole_proportion = curr_num_holes / curr_uncompacted_size;

        // These constants were picked arbitrarily
        if (hole_proportion > this.MIN_HOLE_PERCENT_CLEANUP && curr_uncompacted_size > this.MIN_ARRAY_SIZE_CLEANUP) {
            // There is a specific interleaving where multiple cleanups can occur
            cleanup();
        }

    }

    public boolean member(int x) {
        int x_index = find(x, false);
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
        this.cleanup_lock.writeLock().lock();

        int uncompacted_write_position = 1;
        for (int i = 1; i < N+2; ++i) {
            if (this.values[i] == PADDING) {
                break;
            } else if (this.values[i] != DELETED) {
                this.values[uncompacted_write_position++] = this.values[i];
            }
        }

        this.uncompacted_size.set(uncompacted_write_position-1);
        this.num_holes.set(0);

        for (; uncompacted_write_position < N+2; ++uncompacted_write_position) {
            this.values[uncompacted_write_position] = PADDING;
        }

        this.cleanup_lock.writeLock().unlock();
    }

    // =-=-=-=-=-=-=-=-
    // Helper functions
    // =-=-=-=-=-=-=-=-

    private int find(int x, boolean lock_x_index) {
        int low = 1;
        int high = N+1;
        int x_index = -1;

        this.cleanup_lock.readLock().lock();

        // Locking left and right of binary search prevents
        // swaps travelling over a binary search region
        // and potentially invalidating it
        this.region_locks[low-1].readLock().lock();

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
                this.region_locks[mid].readLock().lock();
                this.region_locks[low-1].readLock().unlock();
                low = mid+1;
            } else {
                x_index = mid;
                break;
            }
        }

        if (x_index != -1 && lock_x_index) {
            this.region_locks[x_index].writeLock().lock();
        }
        this.region_locks[low-1].readLock().unlock();

        this.cleanup_lock.readLock().unlock();

        return x_index;
    }
}
