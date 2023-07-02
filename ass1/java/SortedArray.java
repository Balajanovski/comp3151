import java.util.concurrent.Semaphore;
import java.util.concurrent.locks.ReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;
import java.util.stream.Stream;

public class SortedArray {
    private final int N;
    private int[] values;
    private int size;

    private ReadWriteLock[] rw_locks;
    private Semaphore size_semaphore;

    public SortedArray(int N) {
        this.N = N;
        this.size_semaphore = new Semaphore(N);
        this.size = 0;
        this.values = new int[N+2];
        this.rw_locks = Stream.iterate(0, x->x+1)
                .limit(N+2)
                .map(i -> new ReentrantReadWriteLock())
                .toArray(ReadWriteLock[]::new);
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
        this.rw_locks[0].writeLock().lock();
        for (int i = 1; i < N+2 && insertion_pos == -1; ++i) {
            this.rw_locks[i].writeLock().lock();

            if (this.values[i] == x) {
                this.rw_locks[i-1].writeLock().unlock();
                this.rw_locks[i].writeLock().unlock();
                return;
            } else if (Math.abs(this.values[i]) > x) {
                insertion_pos = i;
                break;
            }

            this.rw_locks[i-1].writeLock().unlock();
        }

        if (insertion_pos == -1) {
            // Safely unlock. However, if a process ever gets here
            // something has gone DREADFULLY wrong
            // TODO: Check this never happens
            this.rw_locks[N+1].writeLock().unlock();
            return;
        }

        // At this point, the lock should be held at insertion_pos!
        // TODO: Validate it

        // Lock the right of the array
        for (int i = insertion_pos+1; i < N+2; ++i) {
            this.rw_locks[i].writeLock().lock();
        }

        // Insert x into desired position
        for (int i = insertion_pos; i < N+2; ++i) {
            int temp = this.values[i];
            this.values[i] = x;
            x = temp;
        }

        // Update size
        ++this.size;

        // Unlock the array
        for (int i = insertion_pos-1; i < N+2; ++i) {
            this.rw_locks[i].writeLock().unlock();
        }
    }

    public void delete(int x) {
        assert (x > 0);

        int low = 0;

        this.rw_locks[N+1].readLock().lock();
        // Ensure that size is not modified
        int high = this.size-1;
        this.rw_locks[high].writeLock().lock(); // Write, not read lock
        this.rw_locks[N+1].readLock().unlock();

        while (low <= high) {
            int mid = low + (high - low) / 2;

            if (this.values[mid] < 0) {
                boolean found_positive = false;
                for (int i = mid+1; i <= high; ++i) {
                    if (this.values[i] > 0) {
                        found_positive = true;
                        mid = i;
                        break;
                    }
                }

                if (!found_positive) {
                    for (int i = mid-1; i >= low; --i) {
                        if (this.values[i] > 0) {
                            found_positive = true;
                            mid = i;
                            break;
                        }
                    }
                }

                if (!found_positive) {
                    break;
                }
            }

            if (this.values[mid] < x) {
                low = mid+1;
            } else if (this.values[mid] > x) {
                // Hand over hand locking
                // Allow mutations to the right of the search

                this.rw_locks[mid-1].writeLock().lock();
                this.rw_locks[high].writeLock().unlock();

                high = mid-1;
            } else {
                this.values[mid] = -this.values[mid];
                break;
            }
        }

        this.rw_locks[high].writeLock().unlock();
        this.size_semaphore.release();
    }

    public boolean member(int x) {
        int low = 0;

        this.rw_locks[N+1].readLock().lock();
        // Ensure that size is not modified
        int high = this.size-1;
        this.rw_locks[high].readLock().lock();
        this.rw_locks[N+1].readLock().unlock();

        boolean found_x = false;
        while (low <= high) {
            int mid = low + (high - low) / 2;

            if (this.values[mid] < 0) {
                boolean found_positive = false;
                for (int i = mid+1; i <= high; ++i) {
                    if (this.values[i] > 0) {
                        found_positive = true;
                        mid = i;
                        break;
                    }
                }

                if (!found_positive) {
                    for (int i = mid-1; i >= low; --i) {
                        if (this.values[i] > 0) {
                            found_positive = true;
                            mid = i;
                            break;
                        }
                    }
                }

                if (!found_positive) {
                    break;
                }
            }

            if (this.values[mid] < x) {
                low = mid+1;
            } else if (this.values[mid] > x) {
                // Hand over hand locking
                // Allow mutations to the right of the search

                this.rw_locks[mid-1].readLock().lock();
                this.rw_locks[high].readLock().unlock();

                high = mid-1;
            } else {
                found_x = true;
                break;
            }
        }

        this.rw_locks[high].readLock().unlock();
        return found_x;
    }

    public void print_sorted() {
        this.rw_locks[0].readLock().lock();
        for (int i = 1; i < N+2; ++i) {
            this.rw_locks[i].readLock().lock();
            if (values[i] == Integer.MAX_VALUE) {
                this.rw_locks[i-1].readLock().unlock();
                this.rw_locks[i].readLock().unlock();
                return;
            }

            if (values[i] > 0) {
                System.out.println(values[i]);
            }

            this.rw_locks[i-1].readLock().unlock();
        }
        this.rw_locks[N+1].readLock().unlock();
    }

    public void cleanup() {
        this.rw_locks[0].writeLock().lock();
        for (int i = 1; i < N+2; ++i) {
            this.rw_locks[i].writeLock().lock();

            if (this.values[i] < 0) {
                for (int j = i+1; j < N+2; ++j) {
                    this.rw_locks[j].writeLock().lock();
                }

                int insert_pos = i;
                for (int j = i+1; j < N+2; ++j) {
                    if (this.values[j] > 0) {
                        this.values[insert_pos] = this.values[j];
                        ++insert_pos;
                    }
                }
                for (int j = insert_pos; j < N+2; ++j) {
                    this.values[j] = 0;
                }

                for (int j = i+1; j < N+2; ++j) {
                    this.rw_locks[j].writeLock().unlock();
                }
            }

            this.rw_locks[i-1].writeLock().unlock();
        }
    }
}
