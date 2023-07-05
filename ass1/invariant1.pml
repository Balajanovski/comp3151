#define N 10

int array[N];
bool locks[N];
int insertPos = -1;
int binaryPos = 0;


init {
    // Init array
    int i = 0;
    for (i: 0 .. N-1) {
        array[i] = 0;
        locks[i] = false;
    }
    run binarySearch(); // needs target
    run insert(); // needs target
}

proctype insert(byte target) {
    byte region_left = -1;
    byte region_right = -1;
L1: if
    :: locks[0] == false ->
        insertPos = 0;
        int i;
        for (i : 1 .. N+1){
L2:         if 
            :: locks[i] == false ->
                insertPos = i;
                if 
                :: array[i] == target ->
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
    :: else -> goto L1
    fi
}

proctype binarySearch(byte target) {
    byte low = 1;
    byte high = N-1;
    byte mid;

    locks[low-1] = true;
    binaryPos = low-1;
    do
    :: low <= high ->
        mid = (low + high) / 2;
    :: atomic {
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
    od;
    locks[low-1] == false;
}

ltl inv1 {
    [](
        binaryPos > insertPos
    )
}