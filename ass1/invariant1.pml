#define N 10

int array[N] = {1,3,5,7,9,10,13,15,18,0};
bool locks[N];
int insertPos = -1;
int binaryPos = 0;
bool searchStarted = 0;

init {
    // Init array
    //int i = 0;
    //byte randint = 0;
    //select(i : 1..8)      //targets from 1-20
    //run binarySearch(i); 
    //select(i : 1..8)       //targets from 1-20
    //run insert(i); 
    do
    :: run binarySearch(1);
        break;
    :: run binarySearch(15);
        break;
    :: run binarySearch(9);
        break;
    od;

    do
    :: run insert(2);
        break;
    :: run insert(19);
        break;
    :: run insert(10);
        break;
    od;
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
    for (i : 0 .. N+1) {
L2:     if 
        :: locks[i] == false ->
            insertPos = i;
        :: i == 0 -> skip;
        :: else -> 
            goto L2;
        fi;
        if 
        :: array[i] == target -> //duplicate
            break;
        :: array[i] > target ->
            region_left = i;
            break;
        :: array[i] == 0 -> //hole found
            region_left = i;
            array[i] = target
            goto end;
        fi;
    };
    if 
    :: region_left == -1 -> 
        goto end;
        // array full or duplicate
    fi 
    for (i : region_left + 1 .. N + 1) {
L3:     if 
        :: locks[i] == false ->
            insertPos = i;
            if 
            :: array[i] == 0 ->
                region_right = i;
                break;
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
        :: else ->
            break;
        od
        array[region_left] = target;
    }
end:    locks[0] = false;
}

proctype binarySearch(byte target) {
    byte low = 1;
    byte high = N-2; // last element 0
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