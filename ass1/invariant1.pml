#define N 10

int expData[10] = {0,3,5,7,9,10,13,15,18,0};
bool locks[10];
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

    expData[0] = 1; //incuded so ispin tracks the array
    do
    :: run binarySearch(1);
        break;
    :: run binarySearch(15);
        break;
    :: run binarySearch(9);
        break;
    od;

    do
    :: run insert(11);
        break;
    :: run insert(19);
        break;
    :: run insert(10);
        break;
    od;
}

proctype insert(int target) {
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
    int i = 1;
    do
    :: i < N+2 ->
L2:     if 
        :: locks[i] == false ->
            insertPos = i;
        :: else -> 
            goto L2;
        fi;
        int currentData = expData[i];
        if
        :: currentData > target ->
            region_left = i;
            break;
        :: currentData == 0 -> //hole found
            region_left = i;
            expData[i] = target
            goto L4;
        :: currentData == target -> //duplicate
            break;
        :: else -> skip;
        fi;
        i++;
    :: else -> break;
    od;
    if 
    :: region_left == -1 -> 
        goto L4;
        // array full or duplicate
    :: else -> skip;
    fi 
    for (i : region_left + 1 .. N + 1) {
L3:     if 
        :: locks[i] == false ->
            insertPos = i;
        :: else -> goto L3;
        fi;
        if 
        :: expData[i] == 0 ->
            region_right = i;
            break;
        :: else -> skip;
        fi;
    }
    if 
    :: region_right == -1 -> 
        // array full
        goto L4;
    :: else -> skip;
    fi 
    atomic {
        i = region_right;
        do
        :: i >= region_left + 1 -> 
            expData[i] = expData[i-1];
            i--;
        :: else ->
            break;
        od
        expData[region_left] = target;
    }
L4:     insertPos = -1;
        locks[0] = false;
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
        :: expData[mid] == target ->
            printf("Target found at index %d\n", mid);
            break;
        :: expData[mid] < target ->
            locks[mid] = true;
            locks[low-1] = false;
            binaryPos = mid;
            low = mid + 1;
        :: expData[mid] > target ->
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