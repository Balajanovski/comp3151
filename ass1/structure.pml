#define N 10

int values[N];
int size = 0;
int uncompacted_size = 0;

// Readers-writer lock
// Implemented using two mutexes as channels
// according to https://en.wikipedia.org/wiki/Readers%E2%80%93writer_lock
int b = 0;
chan r = [1] of { bool };
chan g = [1] of { bool };

// We need a new lock to not ensure 
// that no inserts interleave and break the
// size invariant
chan attempting_insert = [1] of { bool };

proctype insert(int x) {
    assert (x > 0);

    // Lock tokens
    bool g_token;
    bool attempting_insert_token;

    // Iterator variable
    int i;

    attempting_insert?attempting_insert_token -> ; // Only allow 1 insert in
    // !! TODO: Verify this

    (size < N);
    g?g_token -> ; // Readers-writer write lock

    // Invariant is that size < N here
    // !! TODO: Verify this

    //
    // Clear deleted items
    // This should be implemented as a cleanup process
    //

    // !! TODO

    //
    // Insert into items
    //

    // Find insert index
    i = 0;
    do
    :: (i < (N-1)) -> 
        if
        :: (values[i] == 0 || values[i] > x) -> break;
        :: else -> i = i + 1;
        fi
    :: else -> break
    od;

    // Insert and shift up
    int temp1 = x;
    int temp2;
    do
    :: (i < N) ->
        temp2 = values[i];
        values[i] = temp1;
        temp1 = temp2;
        i = i + 1;

        if
        :: (temp1 == 0) -> break;
        :: else -> ;
        fi;
    :: else -> break
    od;

    size = size + 1;
    uncompacted_size = size;

    g!true; // Readers-writer write unlock
    attempting_insert!true;
}

proctype delete(int x) {
    // Lock tokens
    bool g_token;
}

proctype member(int x) {
    bool found_x = false;

    // Lock tokens
    bool r_token;
    bool g_token;

    // Readers-writer read lock
    atomic {
        r?r_token -> ;
        b = b + 1;
        if
        :: (b == 1) ->
            g?g_token -> ;
        fi;
        r!true;
    }

    int low = 0;
    int high = uncompacted_size - 1;
    int mid;
    int middle_value;

    do
    :: (low <= high) ->
        mid = low + (high - low) / 2;
        middle_value = values[mid];

        if
        :: (middle_value < 0) ->
            // Scan to find value

            bool found_positive_val = false;

            int i;
            for (i: (mid + 1) .. high) {
                middle_value = values[i];
                if
                :: (middle_value > 0) -> 
                    found_positive_val = true;
                    mid = i;
                    break;
                :: else -> ;
                fi;
            }

            if
            :: !found_positive_val -> {
                i = mid - 1;
                do
                :: (i >= low) -> {
                    middle_value = values[i];
                    if
                    :: (middle_value > 0) ->
                        found_positive_val = true;
                        mid = i;
                        break;
                    :: else -> ;
                    fi;
                    i = i - 1;
                }
                :: else -> break;
                od;
            }
            :: else -> ;
            fi;

            if
            :: !found_positive_val -> goto member_return;
            :: else -> ;
            fi;
        :: else -> ;
        fi;

        // Middle must be positive now
        assert (middle_value > 0 && values[mid] == middle_value);

        // Binary search
        if
        :: (middle_value == x) ->
            found_x = true;
            goto member_return;
        :: (middle_value > x) ->
            high = mid - 1;
        :: else ->
            low = mid + 1;
        fi;
    :: else -> break;
    od;

member_return:
    // Readers-writer read unlock
    atomic {
        r?r_token -> ;
        b = b - 1;
        if
        :: (b == 0) ->
            g!true;
        fi;
        r!true;
    }
}

proctype print_sorted() {
    // Lock tokens
    bool r_token;
    bool g_token;

    // Readers-writer read lock
    atomic {
        r?r_token -> ;
        b = b + 1;
        if
        :: (b == 1) ->
            g?g_token -> ;
        fi;
        r!true;
    }

    int i = 0;
    for (i: 0 .. uncompacted_size-1) {
        if
        :: (values[i] > 0) -> printf("%d\n", values[i]);
        :: else -> ;
        fi;
    }

    // Readers-writer read unlock
    atomic {
        r?r_token -> ;
        b = b - 1;
        if
        :: (b == 0) ->
            g!true;
        fi;
        r!true;
    }
}

init {
    // Init array
    int i = 0;
    for (i: 0 .. N-1) {
        values[i] = 0;
    }

    // Init locks
    r!true;
    g!true;
    attempting_insert!true;
    
    
}
