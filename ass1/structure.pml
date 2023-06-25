#define N 10

int values[N];
int size = 0;

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

inline insert(x) {
    bool g_token;
    bool attempting_insert_token;
    int _i;

    attempting_insert?attempting_insert_token -> {
        (size < N);

        g?g_token -> {
            // Invariant is that size < N here
            // !! TODO: Verify this

            //
            // Clear deleted items
            //

            // !! TODO

            //
            // Insert into items
            //

            // Find insert index
            _i = 0;
            do
            :: (_i < (N-1)) -> 
                if
                :: (values[_i] == 0 || values[_i] > x) -> break;
                :: else -> _i = _i + 1;
                fi
            :: else -> break
            od;

            // Insert and shift up
            int temp1 = x;
            int temp2;
            do
            :: (_i < N) ->
                temp2 = values[_i];
                values[_i] = temp1;
                temp1 = temp2;

                _i = _i + 1
            :: else -> break
            od;

            size = size + 1;
            g!g_token;
        }

        attempting_insert!attempting_insert_token;
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
    
    insert(4);
    insert(3);
    insert(2);
    insert(1);
}
