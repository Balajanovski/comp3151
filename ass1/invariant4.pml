#define N 10

int expData[10] = {0,3,5,7,9,10,13,15,18,0};
bool locks[10];
bool writelocks[10];
int deletePID[3] = {0,1,2};

init {

    expData[0] = 1; //incuded so ispin tracks the array
    deletePID[0] = 0;
    deletePID[1] = -1;
    deletePID[2] = -2;

    run delete(10);
    run delete(10);
}




proctype delete(byte target) {
    byte low = 1;
    byte high = N-2; // last element 0
    byte mid;
bs1: atomic {
    if 
    :: locks[low-1] == false ->
        locks[low-1] = true;
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
        :: expData[mid] == -1 ->
            mid = mid + 1;
        :: expData[mid] < target ->
            locks[mid] = true;
            locks[low-1] = false;
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
    locks[low-1] = false;
}

ltl inv4 {
    []!(
        deletePID[1] == deletePID[2]
    ) 
}