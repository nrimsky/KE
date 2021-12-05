/* 	
	ke.pl 
	Implementation of the KE Calculus
	Based on Lab 2 of AI Course
	swipl ke.pl

	Example queries:
	?- ke( [(q=>r), ((p&q)<=>(q&r)), -p], [], [], [], 0 ).
	?- ke( [- ( (a => (b v c) ) => ((( b => -a ) & (-c)) => -a) )], [], [], [], 0 ).
	?- ke( [- ((- x) & y <=> x & y <=> - y) ], [], [], [], 0 ).
	?- ke( [s=>p, w&(-z), -p, -z=>(s v q v r), (w v y) => -q, -r], [], [], [], 0 ).

	To prove {} |-F, start with the negation of F and everything else empty
	?- ke( [-F], [], [], [], 0 ).

	Or more generally, to prove S |-F, start with each premise in S and the negation of the conclusion:
	?- ke( [P1, P2, ..., Pn, -F], [], [], [], 0 ).
*/

/* Declaring the operators */

:-  op(400,fy,-),    % negation
	op(500,xfy,&),   % conjunction
	op(600,xfy,v),   % disjunction
	op(650,xfy,=>),  % implication
	op(700,xfy,<=>). % equivalence

/* Helpers */

literal(A) :-
	atom(A);
	(complement(A, Ac), atom(Ac)).

complement(A, -A).
complement(-A, A).

/* Formula types and their components */

alpha(A & B, A, B).
alpha(-(A => B), A, -B).
alpha(-(A v B), -A, -B).

beta(-(A & B), -A, -B).
beta(A => B, -A, B).
beta(A v B, A, B).

eta(A <=> B, A, B, -A, -B).
eta(-(A <=> B), A, -B, -A, B).

/* 	?- ke( Unvisited, Visited, Literals, Analysed, BranchNumber ). */

ke( [F|_], _, L, _, _ ) :-
	/* If the complement of F is in L, then the formula is unsatisfiable (closure) */
	literal(F),
	complement(F, Fc),
	member(Fc, L), 
	!,
	write("Close "), write(F), write(","), write(Fc), nl.

ke( [F|U], V, L, G, B ) :-
	/* F is a literal and the complement of F is not in L */
	literal(F),
	!,
	ke(U, V, [F|L], G, B).

ke( [F|U], V, L, G, B ) :-
	/* F is a double negation */
	F = -(-FP),
	!,
	ke([FP|U], V, L, [F|G], B).

ke([F|U], V, L, G, B ) :-
	/* F is an alpha formula with components A1 and A2 */
	alpha(F, A1, A2),
	!,
	write("Alpha "), write(A1), nl,
	write("Alpha "), write(A2), nl,
	ke([A1,A2|U], V, L, [F|G], B).

ke([F|U], V, L, G, B ) :-
	/* 
	F is a beta formula with components B1 and B2
	Either component of F is in U, V, L or G - Beta simplification
	*/
	beta(F, B1, B2),
	flatten([U, V, L, G], All),
	(member(B1, All); member(B2, All)),
	!,
	ke(U, V, L, [F|G], B).

ke( [F|U], V, L, G, B ) :-
	/* 
	F is a beta formula with components B1 and B2
	Complement B1c of component B1 is in U, V, L or G 
	*/
	beta(F, B1, B2),
	flatten([U, V, L, G], All),
	complement(B1, B1c),
	member(B1c, All),
	!,
	write("Beta "), write(B2), nl,
	append(U, V, UV),
	ke([B2|UV], [], L, [F|G], B).

ke( [F|U], V, L, G, B ) :-
	/* 
	F is a beta formula with components B1 and B2
	Complement B2c of component B1 is in U, V, L or G 
	*/
	beta(F, B1, B2),
	flatten([U, V, L, G], All),
	complement(B2, B2c),
	member(B2c, All),
	!,
	write("Beta "), write(B1), nl,
	append(U, V, UV),
	ke([B1|UV], [], L, [F|G], B).


ke( [F|U], V, L, G, B ) :-
	/* 
	F is a beta formula with components B1 and B2
	Neither B1 nor B2 nor their complements are in U, V, L, or G
	Save F as a candidate for PB rule
	*/
	beta(F, _, _),
	!,
	ke(U, [F|V], L, G, B).


ke( [], [F|VP], L, G, B ) :-
	/* 
	U is empty and V is not
	Pick a formula F in V: it will be a beta formula with components B1 and B2
	Let VP be V without F
	Try to prove ke( [F,B1|VP], [], L, G, B ) and ke( [F,B1c|VP], [], L, G, B )
	F will be analysed on the next recursive call by beta elimination on one branch and beta simplification on the other
	*/
	beta(F, B1, _),
	complement(B1, B1c),
	!,
	(ke( [F,B1|VP], [], L, G, B), ke( [F,B1c|VP], [], L, G, B)).

   
ke( [F|U], V, L, G, B ) :-
	/* 
	Eta rule
	Branch on one part of the formula
	The other component of the eta pair can be added to a branch if the first component is already present
	*/
	eta(F, E11, E12, E21, E22),
	!,
	B_1 is B + 1,
	B_2 is B + 2,
	write("Branch "), write(B_1), write(" "), write(E11), nl,
	write("Eta "), write(E12), nl,
	ke([E12, E11|U], V, L, [F|G], B_1),
	write("Branch "), write(B_2),  write(" "), write(E21), nl,
	write("Eta "), write(E22), nl,
	ke([E22, E21|U], V, L, [F|G], B_2).


ke( [], [], L, _, _) :-
	/* 
	If U is empty and V is also empty
	You have an open branch, and an assignment of truth value to literals which make –(F) true (and hence F false)
	*/
	write("Open "), write(L), nl.

