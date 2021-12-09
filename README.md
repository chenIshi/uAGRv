# uAGRv
Verifying the abstract behavior of unreliable aggregation.

## Motivations

In-network aggregation under an unreliable network condition basically mix a level of "consistency" concepts from distributed system to in-network computation. However, the 
primitives and related constrains are pretty much different. As a result, in current stage 
I want to call for formal verification tools like *Spin* to help me design such protocol.

## Challenges
Basically everything.

The promela semantic is very different from traditional programming language. I try to link it to previous expriences in coding HDL or designing compiler IR, however it still take a huge amount of time to be familiar to it.

Also, the objective of such protocol is hard to define since currently there are no "strict" restrictions on such protocol (everything could change in current stage).
