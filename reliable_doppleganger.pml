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
	3. Don't consider packet drop for now: senders iteratively send responses in order
	
Challenges:
	1. Each sender could send traffic with the same ID more than once (twice now)
	    
Objectives:
	1. Collector never recieves traffic with the same ID
*/

// {byte, byte, byte} := {traffic ID}

// sender packet type
mtype = {info, signal};

typedef info_t {
	int flow_id;
	int mon_id;
};

proctype aggregator(chan link; chan sendback)
{	int latest_id, aggrd_cnt;
	bool isSeen[2];
	isSeen[0] = false; isSeen[1] = false;
	int forward_cnt;
	info_t pkt;

	do
	:: link?info(pkt) ->
		if
		:: pkt.flow_id == latest_id ->
			// ignore packets with duplicated monitor id
			if 
			:: isSeen[pkt.mon_id] == false ->
				isSeen[pkt.mon_id] = true;
				aggrd_cnt ++;
				if
				:: aggrd_cnt < 2 -> skip;
				:: aggrd_cnt >= 2 ->
					forward_cnt ++;
					sendback!info(pkt);
				fi;
			:: else -> skip;
			fi;
		:: pkt.flow_id > latest_id ->
			// cleanup interal state
			latest_id = pkt.flow_id;
			aggrd_cnt = 1;
			isSeen[0]=false; isSeen[1]=false;
			isSeen[pkt.mon_id] = true;
		:: else -> skip;
		fi;
	:: link?signal(pkt) ->
		sendback!signal(pkt);
		break;
	od;
	
}

proctype sender(int mon_id; chan link)
{	int i;
	info_t pkt;
	pkt.mon_id = mon_id;
	for (i : 1 .. 5) {
		pkt.flow_id = i;
		link!info(pkt);
		link!info(pkt);
	}
	link!signal(pkt);
}

proctype collector(chan sendback)
{	int latest_id = -1;
	info_t res;

	do
	:: sendback?info(res) ->
		assert(latest_id != res.flow_id);
		latest_id = res.flow_id;
	:: sendback?signal(res) -> break;
	od;

}

init {
	chan link = [20] of {mtype, info_t};
	chan sendback = [5] of {mtype, info_t};
	run aggregator(link, sendback);
	run sender(0, link);
	run sender(1, link);
	run collector(sendback);
}

