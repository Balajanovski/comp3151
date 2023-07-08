#define N 10

int expData[10] = {0,3,5,7,9,10,13,15,18,0};
bool writelocks[10];
int deletePID[4] = {0,1,2,3};

init {

    expData[0] = 1; //incuded so ispin tracks the array
    deletePID[0] = 0;
    deletePID[1] = -1;
    deletePID[2] = -2;
    deletePID[3] = -3;

    run insert(10);
    run delete(10);
    run insert(10);
}

proctype insert(int target) {
    int region_left = -1;
    int region_right = -1;
L1: atomic {
    if
    :: writelocks[0] == false ->
        writelocks[0] = true;
        deletePID[_pid] = 0;
    :: else -> goto L1
    fi
    };
    int i = 1;
    do
    :: i < N+2 ->
L2:     atomic {
        if 
        :: writelocks[i] == false ->
            writelocks[i] = true;
            deletePID[_pid] = i;
        :: else -> 
            goto L2;
        fi;
        }
        int currentData = expData[i];
        if
        :: currentData > target ->
            region_left = i;
            break;
        :: currentData == target -> //duplicate
            deletePID[_pid] = -_pid;
            int j;
            for (j : 0 .. i) {
                writelocks[j] = false;
            };
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
L3:     atomic {
        if 
        :: writelocks[i] == false ->
            writelocks[i] = true;
            deletePID[_pid] = i;
        :: else -> goto L3;
        fi;
        };
        if 
        :: expData[i] == 0 ->
            region_right = i;
            break;
        :: else -> skip;
        fi;
    }
//    if 
//    :: region_right == -1 -> 
//        // array full
//        int k = 0;
//        for (k : 0 .. i) {
//            writelocks[k] = false;
//        };
//        goto L4;
//    :: else -> skip;
//    fi 
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
    i = 0;
    for (i : 0 .. region_right) {
        writelocks[i] = false;
    };
L4: 
    deletePID[_pid] = -_pid;
    writelocks[0] = false;
}


proctype delete(byte target) {
    byte low = 1;
    byte high = N-2; // last element 0
    byte mid;
    do
    :: low <= high ->
        mid = (low + high) / 2;
        atomic {
        if
        :: expData[mid] == target ->
            printf("Target found at index %d\n", mid);
            break;
        :: expData[mid] == -1 ->
            mid = mid + 1;
        :: expData[mid] < target ->
            low = mid + 1;
        :: expData[mid] > target ->
            high = mid - 1;
        fi;
        }
    :: else ->
        break
    od;

bs2: atomic {
    if 
    :: writelocks[mid] == false ->
        writelocks[mid] = true;
        deletePID[_pid] = mid;
    :: else -> 
        goto bs2;
    fi
    };

    if 
    :: expData[mid] == target ->
        expData[mid] = -1;
    :: else -> skip;
    fi;
    deletePID[_pid] = -_pid;
    writelocks[mid] = false
}

ltl inv6 {
    []!(
        deletePID[1] == deletePID[2] || deletePID[2] == deletePID[3]
    ) 
}