/*
	Elevator template model for Assignment 2 of 2IX20 - Software Specification.
	Set up for one elevator and two floors.
*/

// LTL formulas to be verified
// ltl p1 { []<> (floor_request_made[1]==true) } /* this property does not hold, as a request for floor 1 can be indefinitely postponed. */
// ltl p4 { []<>((floor_request_made[0]> 0) && (floor_request_made[1] < N))}
// ltl p5 { [] ((cabin_door_is_open == true) && (cabin_door_is_open == false))} // this property should never hold
// ltl a1 { [] ((floor_request_made[1]) -> <>(current_floor==1)) }
// ltl a2 { [] ((floor_request_made[2]) -> <>(current_floor==2)) }
// ltl b1 { []<> (elevators[0].cabin_door_is_open==true) } /* this property should hold, but does not yet; at any moment during an execution, the opening of the cabin door will happen at some later point. */
// ltl b2 { []<> (elevators[0].cabin_door_is_open==false) } /* this property should hold, but does not yet; at any moment during an execution, the closing of the cabin door will happen at some later point. */
// ltl c { [] (cabin_door_is_open -> floor_door_is_open[current_floor]) }
// ltl e { [] ((floor_request_made[0]) -> <>(!floor_request_made[0])) }
// ltl f { [] (<>(f==0) && <>(f==1) && <>(f==2)) }
ltl h { []<> (floor_request_made[h]) }


#define N 3                       // the number of floors
#define M 3                       // the number of elevators
#define cabid  	_pid							// IDs of cabin doors
#define elevid 	_pid-M 						// IDs of elevator engines
#define mcid		_pid-2*M					// IDs of main controls
#define reqid  	_pid-3*M-1  			// IDs of req_button processes

// Variables for LTL
byte f;
byte h=N-1;

// type for direction of elevator
mtype { down, up, none };

// asynchronous channel to handle passenger requests
chan request = [N] of { byte };
// status of requests per floor
bool floor_request_made[N];

// status of M elevators
typedef elevator {
    mtype direction = none;
    byte current_floor;
    bool cabin_door_is_open;
    bool floor_door_is_open[N]; 	// status of floor doors of the shaft of the single elevator
}
elevator elevators[M];

// status and synchronous channels for elevator cabin and engine
chan update_cabin_door[M] = [0] of { bool };
chan cabin_door_updated[M] = [0] of { bool };
chan move[M] = [0] of { bool };
chan floor_reached[M] = [0] of { bool };

// synchronous channels for communication between request handler and main control
chan go[M] = [0] of { byte };
chan served = [M] of { byte };

// cabin door process
active [M] proctype cabin_door() {
	do
	:: update_cabin_door[cabid]?true -> 
		elevators[cabid].floor_door_is_open[elevators[cabid].current_floor] = true; 
		elevators[cabid].cabin_door_is_open = true; 
		cabin_door_updated[cabid]!true;
	:: update_cabin_door[cabid]?false -> 
		elevators[cabid].cabin_door_is_open = false; 
		elevators[cabid].floor_door_is_open[elevators[cabid].current_floor] = false; 
		// assert(cabin_door_is_open==floor_door_is_open[current_floor]); // assert floor door is open when cabin door is open
		cabin_door_updated[cabid]!false;
	od;
}

// process combining the elevator engine and sensors
active [M] proctype elevator_engine() {
	do
	:: move[elevid]?true ->
		do
		:: move[elevid]?false -> break;
		:: floor_reached[elevid]!true;
		od;
	od;
}

// DUMMY main control process. Remodel it to control the doors and the engine!
active [M] proctype main_control() {
	byte dest;
	do
	:: go[mcid]?dest ->
		if
		:: dest < elevators[mcid].current_floor -> elevators[mcid].direction = down;
		:: dest > elevators[mcid].current_floor -> elevators[mcid].direction = up;
		:: else -> skip;
		fi
		
		if
		:: elevators[mcid].cabin_door_is_open -> update_cabin_door[mcid]!false; cabin_door_updated[mcid]?false;
		:: else -> skip;
		fi

	  // an example assertion.
	  assert(0 <= elevators[mcid].current_floor && elevators[mcid].current_floor < N);
		assert(elevators[mcid].cabin_door_is_open == false);

		if 
		:: elevators[mcid].current_floor != dest -> 
			move[mcid]!true;
			do
			:: elevators[mcid].current_floor != dest ->
				if
				:: elevators[mcid].direction == up -> elevators[mcid].current_floor++;
				:: elevators[mcid].direction == down -> elevators[mcid].current_floor--;
				fi
				floor_reached[mcid]?true;
			:: elevators[mcid].current_floor == dest -> break;
			od
			move[mcid]!false;
		:: else -> skip;
		fi

		elevators[mcid].direction = none;
		update_cabin_door[mcid]!true; cabin_door_updated[mcid]?true;

	  floor_request_made[dest] = false;
	  served!mcid;
		assert(elevators[mcid].current_floor == dest);
	od;
}

// request handler process. Remodel this process to serve M elevators!
active proctype req_handler() {
	byte dest;
	byte count=0;
	byte id;
	do
	:: count < M -> 
		served!count;
		count++;
	:: count == M -> break;
	od
	do
	:: request?dest -> 
		served?id; 
		f=id;
		go[id]!dest;
	od;
}

// request button associated to a floor i to request an elevator
active [N] proctype req_button() {
	do
	:: !floor_request_made[reqid] ->
	  atomic {
		request!reqid;
		floor_request_made[reqid] = true;
	  }
	od;
}
