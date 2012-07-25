-- -*- coding: utf-8 -*- -- 

newPackage(
        "PDSSensitivity",
        Version => "0.1", 
        Date => "July 24, 2012",
        Authors => {{Name => "Chris Miles", 
                  Email => "milesc@lafayette.edu"}},
        Headline => "A package that runs sensitivity analysis on a polynomial dynamical system",
        DebuggingMode => true
        )

needsPackage "RationalPoints" -- for solving varieties

export {
     -- funcs
     makeRing, getDivisors, composeEfficiently, allSteadyStatesIndependent, 
     allCyclesIndependent, computeIndependentSS, computeIndependentCycles, computeSensitivity,
     
     -- options
     fileOut
     }


--=======================================================================
-- generate quotient ring with n variables and r unknowns

makeRing = method()
makeRing (ZZ,ZZ,ZZ) := (n,r,c) -> (
     ll :=  apply( (1..n), i -> value concatenate("x",toString i)); -- make list of x's
     kk :=  apply( (1..r), i -> value concatenate("k",toString i)); -- make list of k's
     R1 :=ZZ/c[kk][ll];
     L := ideal apply((gens R1)|(gens coefficientRing R1), x -> x^c-x);
     R1/L
);

--=======================================================================
-- returns the ideal of solutions for <f^m(x) - x>

composeEfficiently = method()
composeEfficiently(Matrix, ZZ) := (F, m) -> (   
   R := ring F;
   
   -- code breaks if not actually composing, so just return F
   if m == 1 then return ideal apply(flatten entries F, gens R, (f,x)-> f - x);
      
   c := char R;
   n := numgens R;
   vx := apply( (1..n), i -> "x" | toString i ); -- makes list of x's
   
   -- creates all other variables  --> if we get to m = 10 this breaks, this is bad
   v := flatten apply ( m-1, j -> toList apply( (1..n), i -> (toString (vars j)) | (toString i ) ));
   
   -- make polynomial ring with all new vars
   S := (coefficientRing R)[vx, v];
   J := ideal for x in (gens S | gens coefficientRing R) list x^c - x ;
   newR := S / J; -- make it a quotientRing
   
   -- partition the vars
   varList := apply(m, j-> for i from 0 to (n-1) list newR_(i + j*n) );  
      
   -- make the map of variables ... 
   xToY := map(newR, newR, (flatten for i from 1 to (m-1) list varList#i) | (varList#0));

   I := ideal F; -- turn our functions into an ideal
   I = sub(I, newR); -- make them part of newR so vars work

   -- makes system

   P :=  trim ideal join(I_* - varList#1, flatten toList apply( (1..m-1), j -> (xToY^j I)_* - varList#((j+1)%m)));
     
   -- need a new polynom ring for eliminate to be happy
   newR2 := (coefficientRing coefficientRing S)[vx, v, gens coefficientRing S];
   J2 := sub(J, newR2); -- put mod out ideal in new ring
   I2 := sub(P, newR2) + J2; -- put our old ideal and new mod out in new ideal
  
   I2 = ideal gens gb I2;
   

   -- eliminate all the bad variables next
   Ielim := eliminate(I2, apply(join( flatten apply( toList (1..(m-1)), j -> varList#j ) ), v -> sub(v,newR2)));
     
     
   Ir := sub(Ielim, R); -- put back in original ring
   Irgb := ideal gens gb Ir -- return gb
  
);

--=======================================================================
--getDivisors: takes an integer and outputs a list of all its divisors

getDivisors = method()
getDivisors ZZ := List => c -> (
     --get a list of the factors
     factorExponents := apply(toList(factor c), j -> toList(j));
     factors := splice apply(factorExponents, j ->
     	  if j#1 == 1 then (j#0)
	  else lift(j#1, ZZ):j#0);
     
     --get a list of all possible exponents (2^# of factors)
     lens := length factors;
     ourset := set(0,1);
     exponentList := ourset^**lens;
     exponentList = apply(toList(exponentList), i-> toList(i));
     
     --get a list of the divisors
     divisorCombos := apply(exponentList, i -> apply(factors, i, (p, q) -> p^q));
     divisors := apply(divisorCombos, i -> times toSequence(i));
     divisors = unique divisors;
     sort divisors
);

--=======================================================================
-- checks whether or not all steady states are independent of parameters

allSteadyStatesIndependent = method()
allSteadyStatesIndependent (Matrix) := (F) -> (
     R := ring F;
     c := char R;
     I := ideal apply(flatten entries F, gens R, (f,x)-> f - x);  
     PR := (coefficientRing coefficientRing R)[gens R, gens coefficientRing R];   -- polynomial ring for eliminate
     J := ideal for x in (gens PR) list x^c - x;
     I2 := sub(I, PR)+J; -- add mod out ideal
     result := eliminate( apply(gens coefficientRing R, k -> sub(k,PR)), I2);
     I2 = ideal gens gb I2;
     result = result+J; -- add J back in for equality
     ideal gens gb I2 == ideal gens gb result -- returns true\false
);

--=======================================================================
-- checks whether or not all cycles of length m are independent of parameters

allCyclesIndependent = method()
allCyclesIndependent (Matrix, ZZ) := (F, m) -> (
     R := ring F;
     c := char R;
     divisors := getDivisors(m);

     I := composeEfficiently(F, m); 
     PR := (coefficientRing coefficientRing R)[gens R, gens coefficientRing R];  
     I = sub(I, PR); 
     J := ideal for x in (gens PR) list x^c - x; -- mod out ideal
     I = I + J;   
     for i from 0 to #divisors-2 do ( -- -2 since we don't want p
         l := divisors#i; 
	 Il := composeEfficiently(F, l);
	 Il = sub(Il, PR);
	 Il = ideal gens gb Il;
         longlist := {}; -- build list of products
         for j from 1 to (c-1) do (
              shortlist := apply(flatten entries gens Il, x -> x - j );
              longlist = longlist | shortlist; -- add to list of products
          );
	 P :=  product longlist;
         I =  I + ideal P; -- add the new product to the ideal
     );

     result := eliminate( apply(gens coefficientRing R, k -> sub(k,PR)), I);
     result = result+J;
     gens gb I == gens gb result
);

--=======================================================================
-- returns a list of the steady states independent of parameters

computeIndependentSS = method()
computeIndependentSS (Matrix) := (F) -> (
   QR := ring F;
   I := ideal apply( flatten entries F, gens QR, (fx) -> f -x );
   onesList := toList(apply ( gens coefficientRing QR, i -> i =>1)); -- build list to plug in 1's
   zeroesList := toList(apply ( gens coefficientRing QR, i -> i=>0));
   I0 := sub(I, zeroesList); -- plug in 0 to ideal
   I1 := sub(I, onesList);  -- plug in 1 to the ideal
   Icombined :=  I0 + I1; 
   PR := (coefficientRing coefficientRing QR)[gens QR]; 
   J := ideal for x in (gens PR) list x^(char QR) - x;
   J = sub(J, PR);     
   Icombined = sub(Icombined, PR) + J;
   if degree Icombined == 0 then return {}; -- if no solutions, RationalPoints breaks so just return
   points := rationalPoints(Icombined, UseGB => true);
   apply( points, i-> apply(i, j-> sub(j, QR))) -- returns a list of the points
);

--=======================================================================
-- returns a list of the cycles dividing m independent of parameters

computeIndependentCycles = method()
computeIndependentCycles(Matrix, ZZ) := (F, m) -> (
   QR := ring F;
   c := char QR;

   I := composeEfficiently(F, m);

   onesList := toList(apply ( gens coefficientRing QR, i -> i =>1)); -- build list to plug in 1's
   zeroesList := toList(apply ( gens coefficientRing QR, i -> i=>0));
   I0 := sub(I, zeroesList); -- plug in 0 to ideal
   I1 := sub(I, onesList);  -- plug in 1 to the ideal
   Icombined := I0 + I1; -- check 0 and 1
   PR := (coefficientRing coefficientRing QR)[gens QR]; 
   J := ideal for x in (gens PR) list x^c - x; -- constrain to make faster
   Icombined = sub(Icombined, PR)+J;
   if degree Icombined == 0 then return {}; -- if no solutions, RationalPoints breaks so just return
   points := rationalPoints ideal (gens gb Icombined); -- get list of possible candidates

   isGoodList := {};
   for i from 0 to #points-1 do (
       xvals := points#i;	
       isGood := true;
       for j from 1 to m do (
           plugIns := apply(gens QR, xvals, (g,thisx) -> g=>thisx); -- get x values to plug in
           plugIns0 := plugIns |  apply(gens coefficientRing QR, k-> k=>0);
           plugIns1 := plugIns |  apply(gens coefficientRing QR, k-> k=>1);  	    
	   if promote(sub(F, plugIns0), ZZ/c) != promote(sub(F,plugIns1), ZZ/c) then isGood = false;	 -- check if F^j(xbar,0) = F^j(xbar,1)
	   if isGood == false then break;
	   xvals = flatten entries promote(sub(F, plugIns0), ZZ/c);
	   );
	    
       if isGood == true then isGoodList = append(isGoodList, points#i); -- if good, append to list
     ); -- return all valid points
     apply( isGoodList, i-> apply(i, j-> sub(j, QR)))
 );

--=======================================================================
-- replaces each line of table and checks if steady states are independent
-- optional input: write to file

computeSensitivity = method(Options => {fileOut => false})
computeSensitivity(Matrix) := opts -> (F) -> (
     if (opts.fileOut) then ( 
	  out := read "Output file name: ";
	  out << "AllPreserved,TableChanged" << endl;
	  );
     QR := ring F;
     c := char QR;
     n := #(flatten entries F);
     R := makeRing(n,1,c);
     F = sub(F, R);
     initialf := flatten entries F; -- keep track of original functions 
     funcs := flatten entries F;
     nodeList := new MutableList;
     
     
    time for i from 1 to n do ( 
        if i == 1 then print " ";
        inputs := support sub(initialf_(i-1),R);
        if inputs == {} then continue; 
        X := set( 0..(c-1));
        X = toList X^**(#inputs); -- cartesian product
        plugInTable := new MutableHashTable; -- option inputs for functions
        apply(X, x-> plugInTable#x = apply(x, inputs, (x,i)-> sub(i,R)=>sub(x,R)));
        resultTable := new MutableHashTable; -- output ressults
        apply (X, x-> resultTable#x = sub(funcs#(i-1), plugInTable#x));
        
	truecount := 0; -- keep track of how many trues
	
     
       for j from 0 to #X-1 do (  -- for each line in table
	  jResultTable := copy resultTable;
	  jResultTable#(X#j) = first gens coefficientRing R;

          --interpolate
	  newfunc := sum (X, x-> sub((jResultTable#x),R)*product(0..(#inputs-1), i-> (1- (inputs#i - x#i)^(c-1))));

	  thisf := copy initialf;
	  thisf = new MutableList from toList(thisf);
	  thisf#(i-1) = newfunc;
	  thisf = toList thisf;
	  F = matrix(R, {toList thisf});
	  truevalue := allSteadyStatesIndependent(F);

	  if (opts.fileOut) then (
	       outstring := toString(truevalue) |  ",x" | toString(i);
	       out << outstring << endl;
	       );

	  if truevalue then truecount = truecount+1;
           );

       -- add all nodes to a list and sort by %
       nodeList = append(nodeList, ( sub((truecount/(#X)),RR), ("x"|toString i)));
       );

      if (opts.fileOut) then out << close;
      nodeList = sort toList nodeList;
      apply( nodeList, k -> print(k#1, k#0));
  );

--=======================================================================

beginDocumentation()
document { 
        Key => PDSSensitivity,
        Headline => "A package that provides code that runs sensitivity analysis on a polynomial dynamical system",
        EM "PDSSensitivity", " is a package that provides methods for running sensitivity analysis on a polynomial dynamical systems"
        }

--=======================================================================

doc ///
  Key
    (makeRing, ZZ, ZZ, ZZ)
    makeRing
  Headline
    generate quotient ring for polynomial dynamical systems
  Usage
    makeRing(n,r,c)
  Inputs
    n:ZZ
      number of known variables
    r:ZZ
      number of unknown variables      
    c:ZZ
      characteristic of the field
  Outputs
    QR:QuotientRing
  Description
    Text
      Generates $ZZ/c[x_1, \ldots, x_n, k_1, \ldots, k_r]/ <x_1^c - x_1, x_2^c - x_2, \ldots, k_r^c - k_r >$. 
    Example
      describe makeRing(4,2,3)
///  

--=======================================================================

doc ///
  Key
    (getDivisors, ZZ)
    getDivisors
  Headline
    get a list of divisors of an integer
  Usage
    getDivisors(n)
  Inputs
    n:ZZ
      some integer to be split into divisors
  Outputs
    divisors: List
      a list of all of the divisors of n
  Description
    Text
      Returns a list of all of the divisors of some integer. This can be used when figuring out if a limit cycle is a subcycle of another. 
    Example
      getDivisors(480)
///  

--=======================================================================

doc ///
  Key
    (composeEfficiently, Matrix, ZZ)
    composeEfficiently
  Headline
    build a system of equations to efficiently compose a PDS to solve for limit cycles
  Usage
    composeEfficiently(F, m)
  Inputs
    F:Matrix
      a matrix with the PDS equations in the quotient ring to be computed in
   m:ZZ
	  the number of times to be composed (MAX = 10)
  Outputs
    I:Ideal
	  the Groebner basis of the ideal $<F^m(x) - x>$. 
  Description
    Text
       Sets up a system of equations and solves to efficiently compute the Gröbner basis for the ideal of $<f^m(x) - x>$. Often this is much faster than manually
	   composing the function.
    Example
      QR = makeRing(2, 1, 2);
      F = matrix(QR, {{k1*x1*x2+ x1*x2 + x1 + x2 + 1, x1}});
      composeEfficiently(F,2)      
///  

--=======================================================================
    
doc ///      
  Key
    (allSteadyStatesIndependent, Matrix)
    allSteadyStatesIndependent
  Headline
    algebraically check whether all steady states of a PDS are preserved over all possible unknown parameters
  Usage
    allSteadyStatesIndependent(F)
  Inputs
    F: Matrix
      Matrix consisting of the input functions in the quotient ring to be computed in
  Outputs
    allIndependent: Boolean
      whether or not all steady states are preserved
  Description
    Text
      Computes whether $ < f(x) - x > =  <  f(x) - x  > \cap \mathbb{F}[x]$. 
    Example
	  QR = makeRing(2, 1, 3);
	  fx1 = x1^2*x2-x1*x2+x2^2-x1-x2+1;
	  fx2 = x1^2*x2^2*k1+x1^2*x2^2-x1^2*x2*k1-x1*x2^2-x2^2*k1-x1*x2-x2^2+x2*k1-x1-x2;
	  F = matrix(QR, {{fx1, fx2}});
      allSteadyStatesIndependent(F)
///

--=======================================================================

doc ///      
  Key
    (allCyclesIndependent, Matrix, ZZ)
    allCyclesIndependent
  Headline
    algebraically check whether all cycles of length m of a PDS are preserved over all possible unknown parameters
  Usage
    allSteadyStatesIndependent(F, m)
  Inputs
    F:Matrix
      Matrix consisting of the input functions in the quotient ring to be computed in
    m:ZZ
     integer corresponding to the length of the limit cycles desired
  Outputs
    allIndependent: Boolean
      whether or not all m-cycles are preserved
  Description
    Text
      Computes whether $<f^m(x) - x  >+ \sum_{j|m} <\prod_{i=1..p-1}f^{\,j}(x)- x - i>  = ( <f^m(x) - x  >+ \sum_{j|m} <\prod_{i=1..p-1}f^{\,j}(x)- x - i> )\cap \mathbb{F}[x]$. Warning: computationally intensive. 
    Example
       QR = makeRing(2, 1, 3);
       fx1 = x1^2*x2-x1*x2+x2^2-x1-x2+1;
       fx2 = x1^2*x2^2*k1+x1^2*x2^2-x1^2*x2*k1-x1*x2^2-x2^2*k1-x1*x2-x2^2+x2*k1-x1-x2;
       F = matrix(QR, {{fx1, fx2}});
       allCyclesIndependent(F,2)
       allCyclesIndependent(F,3)
       allCyclesIndependent(F,4)
///

--=======================================================================

doc ///      
  Key
    (computeIndependentSS, Matrix)
    computeIndependentSS
  Headline
    algebraically compute all steady states that are preserved over all unknown parameter choices
  Usage
    computeIndependentSS(F)
  Inputs
    F: Matrix
      Matrix consisting of the input functions in the quotient ring to be computed in
  Outputs
    steadyStates: List
      a list of all of the steady states preserved over parameters
  Description
    Text
      Computes $V(<f(x, 1) - x>)\cap V(<f(x,0) - x>)$ and returns all solutions.
    Example
      QR = makeRing(2, 1, 3);
      fx1 = x1^2*x2-x1*x2+x2^2-x1-x2+1;
      fx2 = x1^2*x2^2*k1+x1^2*x2^2-x1^2*x2*k1-x1*x2^2-x2^2*k1-x1*x2-x2^2+x2*k1-x1-x2;
      F = matrix(QR, {{fx1, fx2}});
      computeIndependentSS(F)
///

--=======================================================================

doc ///      
  Key
    (computeIndependentCycles, Matrix, ZZ)
    computeIndependentCycles
  Headline
    algebraically compute all cycles of length DIVIDING m that are preserved over all unknown parameter choices
  Usage
    computeIndependentCycles(F,m)
  Inputs
    F: Matrix
      Matrix consisting of the input functions in the quotient ring to be computed in
    m: ZZ
      integer corresponding to the length of the cycles desired
  Outputs
    cycles: List
      a list of all of the limit cycles of length DIVIDING m preserved over parameters
  Description
    Text
      Computes $V(<f^m(x, 1) - x>)\cap V(<f^m(x,0) - x>)$ and returns all solutions. Note that this returns all cycles DIVIDING length m. Therefore, $m=4$ will return 2 cycles. Warning: Computationally expensive. 
    Example
      QR = makeRing(2, 1, 3);
      fx1 = x1^2*x2-x1*x2+x2^2-x1-x2+1;
      fx2 = x1^2*x2^2*k1+x1^2*x2^2-x1^2*x2*k1-x1*x2^2-x2^2*k1-x1*x2-x2^2+x2*k1-x1-x2;
      F = matrix(QR, {{fx1, fx2}});
      computeIndependentCycles(F,2)
      computeIndependentCycles(F,3)
///

--=======================================================================

doc ///      
  Key
    (computeSensitivity, Matrix)
    computeSensitivity
  Headline
     run sensitivity analysis on the PDS by replacing individual lines with unknown parameter
  Usage
    computeSensitivity(F)
  Inputs
    F: Matrix
      Matrix consisting of the input functions in the quotient ring to be computed in
  Description
    Text
      Iterates over all lines of the transition tables determining the states of each node and replaces with an unknown parameters. From there,
      whether or not the steady states are disturbed is recorded. The final ranking is performed by the percentage of rows in a node's transition table
      that disrupted the steady states. 
    Example
      QR = makeRing(2, 0, 2);
      F = matrix(QR, {{x1*x2+ x1*x2 + x1 + x2 + 1, x1}})
      computeSensitivity(F)
///

--=======================================================================

doc ///
Key
  [computeSensitivity, fileOut]
Headline
     when true, user is prompted for a file name and flushes output to a .csv file    
///

--=======================================================================

doc ///
Key 
   fileOut
Headline 
   flushes the raw data of sensitivity analysis to a .csv file
Description
  Text
   When enabled, the user will be prompted for an output file name and all of the data for the sensitivity analysis
   will be dumped to that file name. This allows the user to further analyze the behavior of the nodes in the system if necessary.
///

--=======================================================================

TEST ///
R = makeRing(2, 1, 2);
F = matrix(R, {{k1, x2+k1}})
assert not allSteadyStatesIndependent F
///

--=======================================================================

TEST ///
R = makeRing(2, 1, 2)
F = matrix(R, {{k1*x1*x2+ x1*x2 + x1 + x2 + 1, x1}})
assert allCyclesIndependent(F, 3)
assert not allSteadyStatesIndependent(F)
assert ((sort computeIndependentCycles(F, 3)) == (sort {{0_R,0_R},{1_R,0_R},{0_R,1_R}}))
///

--=======================================================================

TEST ///
R = ZZ/3[k1][x1,x2,x3]
QR = R/(ideal(x1^3-x1, x2^3-x2, x3^3-x3,k1^3-k1));
f1 = k1*x1+2*x2;
f2 = x1*x2*x3;
f3 = x1*x2+x3^2;
F = matrix(QR, {{f1, f2, f3}});
c = computeIndependentSS(F);
assert ( (sort c) ==  (sort {{0,0,0},{0,0,1}}))
///

--=======================================================================

TEST ///
QR = makeRing(2, 1, 3);
s = {{0,0}, {0,1}, {0,2}, {1,0}, {1,1}, {1,2}, {2,0}, {2,1}, {2,2}};
tx1 = {1, 1, 0, 0, 0, 2, 2, 1, 2};
tx2 = {0, 1, k1, 2, 2, 0, 1, 2, 2};
fx1 = sum ( s,tx1, (sj, tj) -> tj * (1 - (x1 - sj_0 )^2) * ( 1 - (sj_1 - x2)^2) );
fx2 = sum ( s,tx2, (sj, tj) -> tj * (1 - (x1 - sj_0 )^2) * ( 1 - (sj_1 - x2)^2) );
F = matrix(QR, {{fx1, fx2}});
assert (computeIndependentSS(F) == {{2_QR,2_QR}});
assert (allSteadyStatesIndependent(F) == false);
assert (computeIndependentCycles(F, 2) ==  {{2_QR,2_QR}});
assert ((sort computeIndependentCycles(F, 3) == (sort {{2_QR, 2_QR}, {1_QR, 2_QR}, {2_QR, 0_QR}, {2_QR, 1_QR} })));
assert (computeIndependentCycles(F, 4) ==  {{2_QR,2_QR}});
assert (allCyclesIndependent(F,2) == true);
assert (allCyclesIndependent(F,3) == false);
assert (allCyclesIndependent(F,4) == true);
///

--=======================================================================

end 
restart


loadPackage "PDSSensitivity"
check "PDSSensitivity"

installPackage "PDSSensitivity"


