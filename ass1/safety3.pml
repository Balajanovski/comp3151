#define N 10

int expData[10] = {0,3,5,7,9,10,13,15,18,0};
bool locks[10];
int insertPID[3] = {0,1,2};

init {
    expData[0] = 1; //incuded so ispin tracks the array
    insertPID[0] = 0;
    insertPID[1] = -1;
    insertPID[2] = -2;
    run insert(11);
    run insert(11);
}

proctype insert(int target) {
    int region_left = -1;
    int region_right = -1;
L1: atomic {
    if
    :: locks[0] == false ->
        locks[0] = true;
        insertPID[_pid] = 0;
    :: else -> goto L1
    fi
    };
    int i = 1;
    do
    :: i < N+2 ->
L2:     if 
        :: locks[i] == false ->
            insertPID[_pid] = i;
        :: else -> 
            goto L2;
        fi;
        int currentData = expData[i];
        if
        :: currentData > target ->
            region_left = i;
            break;
//        :: currentData == 0 -> //hole found
//            region_left = i;
//            expData[i] = target
//            goto L4;
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
            insertPID[_pid] = i;
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
L4:     insertPID[_pid] = -_pid;
        locks[0] = false;
}

ltl inv {
    []!(
        insertPID[1] == insertPID[2]
    ) 
}