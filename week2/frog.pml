#define N 3

byte state[2*N + 1];

proctype Male(byte index) {
	do
		:: atomic {
			(index < 2*N) && (state[index+1] == 0) ->
			state[index] = 0;
			state[index+1] = 1;
			index = index + 1;
		}
		:: atomic {
			(index < 2*N-1) && (state[index+1] != 0) && (state[index+2] == 0) ->
			state[index] = 0;
			state[index+2] = 1;
			index = index + 2;
		}
	od;
}

proctype Female(byte index) {
	do
		:: atomic {
			(index >= 1) && (state[index-1] == 0) ->
			state[index] = 0;
			state[index-1] = 2;
			index = index - 1;
		}
		:: atomic {
			(index >= 2) && (state[index-1] != 0) && (state[index-2] == 0) ->
			state[index] = 0;
			state[index-2] = 2;
			index = index - 2;
		}
	od;

}

init {
	byte i = 0;

	state[N] = 0;
	for (i: 1 .. N) {
		state[i-1] = 1;
		state[i+N] = 2;
	}	

	for (i: 1 .. N) {
		run Male(i-1);
		run Female(i+N);
	}
}

ltl solved {
	!<>(
		(state[0] == 2) &&
		(state[1] == 2) &&
		(state[2] == 2) &&
		(state[3] == 0) &&
		(state[4] == 1) &&
		(state[5] == 1) &&
		(state[6] == 1)
	)
}
