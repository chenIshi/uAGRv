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
	    
Objectives:
	1. All traffic are aggregated? (might have to use LTL "eventually")
*/

// {byte, byte, byte} := {traffic ID, traffic value}
chan links[2] = [10] of {byte, byte}

active proctype aggregator()
{	byte latest_id, aggrd_cnt;
	do
	:: links?id,val ->
		if
		:: id > latest_id ->
			latest_id = id;
			aggrd_cnt = 1;
		:: id == latest_id ->
			aggrd_cnt ++;
			if
			:: aggrd_cnt >= 2 -> 
			// forward aggred traffic
			fi;
		:: id < latest_id ->
			// drop or forward back traffic
			
	od
}

active proctype generator(chan link)
{

}


