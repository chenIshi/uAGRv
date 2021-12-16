/*
Naive aggregation within rack
Definitions:
	1. Naive aggregation means there is no other optimizations
	    -> only aggregation for proper target
	2. In-rack network topology means that there would be only 
	    a single aggregator responsible for all the traffic.
	3. Only consider one-directional traffic: generators to 
            to aggregator
            
Assumptions:
	1. No link buffer overflow
	2. No arithmetic overflow
	3. Every generator send traffic with the same ID only once
	4. Don't consider packet drop for now: senders iteratively send responses in order
	    
Objectives:
	1. All traffic are aggregated? (might have to use LTL "eventually")
*/

// {byte, byte, byte} := {traffic ID}

mtype = {number, signal};

proctype aggregator(chan link; chan result)
{	int latest_id, aggrd_cnt;
	int forward_cnt, id;

	do
	:: link?number(id) ->
		if
		:: id > latest_id ->
			latest_id = id;
			aggrd_cnt = 1;
		:: id == latest_id ->
			aggrd_cnt ++;
			if
			:: aggrd_cnt < 2 -> skip
			// forward aggred traffic
			:: aggrd_cnt == 2 -> forward_cnt ++
			:: else -> assert(false)
			fi;
		// drop or forward back traffic
		:: id < latest_id -> skip
		:: else -> assert(false)
		fi		
	:: link?signal(id) ->
		result!forward_cnt;
		break
	od;
}

proctype sender(chan link)
{
	int i;
	for (i : 1 .. 10) {
		link!number(i);
	}
	link!signal(1);
}

init {
	chan link = [20] of {mtype, int};
	chan result = [5] of {int};
	int forward_cnt;
	run aggregator(link, result);
	run sender(link);
	run sender(link);
	result?forward_cnt;
	printf("result: %d\n", forward_cnt);
}

