//*********************************************
// MISC COMBINATORIAL FUNCTIONS: 

// Given a set S, return the set of lists of the form `[A,B]`, where A,B are disjoint
// two element subsets of S. (Note [A,B] ne [B,A].)
function PairsOfOrderedPairs(S)
    subs := Subsets(S,2);

    function PairListsWithPrefix(a)
	J := S diff a;
	subs_next := Subsets(J,2);
	return { [a,b] : b in subs_next};
    end function;
    
    return &join [PairListsWithPrefix(a) : a in subs];
end function;

// Given a set `S` of size 6, return the different ways of writing S as a disjoint union
// S = A join B of 3-element subsets.
function BalancedPartitionOfSixEltSet(S)
    assert #S eq 6;
    subs := Subsets(S,3);
    return { { a, S diff a} : a in subs };
end function;
