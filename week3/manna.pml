int wantp;
int wantq;


inline critical_section() {
    inCritical = 1;
    inCritical = 0; 
}


inline non_critical_section() {
    inNonCritical = 1; 
    do
    :: true ->
            skip
    :: true ->
            break
    od; 
    inNonCritical = 0;
}


proctype P() {
    bit inNonCritical = 1;
    bit inCritical = 0;
    do
        :: true ->
            non_critical_section();
            
            if
                :: (wantq == -1) -> wantp = -1
                :: else -> wantp = 1
            fi;

            (wantp != wantq);
            
            csp: critical_section();
            wantp = 0;
    od;
}


proctype Q() {
    bit inNonCritical = 1;
    bit inCritical = 0;
    do
        :: true ->
            non_critical_section();

            if
                :: (wantp == -1) -> wantq = 1
                :: else -> wantq = -1
            fi;

            (wantp != -wantq);

            csq: critical_section();
            wantq = 0;
    od;
}


init {
    wantp = 0;
    wantq = 0;

    run P();
    run Q();
}

ltl mutex { [] !(P@csp && Q@csq) }
