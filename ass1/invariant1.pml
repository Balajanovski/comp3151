#define N 10

int array[N];
bool locks[N];
int insertPos = -1;
int binaryPos = 0;
bool searchStarted = 0;

init {
    // Init array
    int i = 0;
    byte randint = 0;


    for (i: 0 .. N-2) { //fill array 
        select (randint : randint+1 .. randint+3);
        array[i] = randint;
        locks[i] = false;
    }
    array[N-1] = 0;         //last element 0
    locks[N-1] = false;
    select(i : 1..20)      //targets from 1-20
    run binarySearch(i); 
    select(i : 1..20)       //targets from 1-20
    run insert(i); 
}

proctype insert(byte target) {
    int region_left = -1;
    int region_right = -1;
L1: atomic {
    if
    :: locks[0] == false ->
        locks[0] = true;
        insertPos = 0;
    :: else -> goto L1
    fi
    };
    int i;
    for (i : 1 .. N+1){
L2:         if 
        :: locks[i] == false ->
            insertPos = i;
            if 
            :: array[i] == target -> //duplicate
                break; // return todo
            :: array[i] > target ->
                region_left = i;
                break;
            fi
        :: else -> goto L2;
        fi
    }
    if 
    :: region_left == -1 -> 
        goto end;
        // array full
    fi 
    for (i : region_left + 1 .. N + 1) {
L3:         if 
        :: locks[i] == false ->
            insertPos = i;
            if 
            :: array[i] == 0 ->
                region_right = i;
            fi
        :: else -> goto L3;
        fi
    }
    if 
    :: region_right == -1 -> 
        // array full
        goto end;
    fi 
    atomic {
        i = region_right;
        do
        :: i >= region_left + 1 -> 
            array[i] = array[i-1];
            i--;
        od
        array[region_left] = target;
    }
    locks[0] = false;
end: skip;
}

proctype binarySearch(byte target) {
    byte low = 1;
    byte high = N-1;
    byte mid;
bs1: atomic {
    if 
    :: locks[low-1] == false ->
        locks[low-1] = true;
        searchStarted = true;
        binaryPos = low-1;
    :: else -> 
        goto bs1;
    fi
    };
    do
    :: low <= high ->
        mid = (low + high) / 2;
        atomic {
        if
        :: array[mid] == target ->
        printf("Target found at index %d\n", mid);
        break;
        :: array[mid] < target ->
        locks[mid] = true;
        locks[low-1] = false;
        binaryPos = mid;
        low = mid + 1;
        :: array[mid] > target ->
        high = mid - 1;
        fi;
        }
    :: else ->
        break
    od;
    searchStarted = false;
    locks[low-1] = false;
}

ltl inv1 {
    [](
        (binaryPos > insertPos && searchStarted) 
        || !searchStarted
    ) 
}