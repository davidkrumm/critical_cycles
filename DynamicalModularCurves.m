/* 
This file contains MAGMA code used for constructing dynamical modular curves.
This includes:
 - Construction of the curve Z_f for a rational function f (starting on line 58)
 - Construction of dynatomic polynomials and curves (line 93)
 - Construction of generalized dynatomic polynomials and curves (line 134)
 - Construction of trace polynomials and curves (line 174)
 - Construction of preimage curves (line 217)
 - Construction of standard maps between modular curves (line 239)
 */
 
/* Given a nonzero rational function p in one variable with rational coefficients,
returns the union of the sets of rational zeros and poles of p. */
ZerosAndPoles := function(p)
	p_degree :=  Max(Degree(Numerator(p)),Degree(Denominator(p)));
	if p_degree eq 0 then
		return {};
	else
		return {r[1]: r in Roots(Numerator(p))} join {r[1]: r in Roots(Denominator(p))};
	end if;
end function;

/* Given a nonconstant rational function p(t,x) in Q(t)(x),
and a pair of variables (a,b), returns p(a,b). */
Substitute := function(p, vars)
value_num := Evaluate(Polynomial([Evaluate(c, vars[1]) : c in Coefficients(Numerator(p))]), vars[2]);
value_den := Evaluate(Polynomial([Evaluate(c, vars[1]) : c in Coefficients(Denominator(p))]), vars[2]);
return value_num/value_den;
end function;

/* Given a nonconstant rational function f with coefficients in a function field,
writes f = p*A/B, where p is the content of f and A, B are coprime and primitive polynomials.
In addition, returns the set of rational roots and poles of p. */
Normalize := function(f)
	// Ensure f has coefficients in a one-variable function field.
	Qt := FieldOfFractions(CoefficientRing(Parent(f)));
//	f_copy := Substitute(f,[Qt.1,Parent(f).1]);
	a := Numerator(f);
	b := Denominator(f);
	//a := Substitute(a,[Qt.1,Parent(a).1]);
	//b := Substitute(b,[Qt.1,Parent(b).1]);
	a := Polynomial([Qt ! coeff : coeff in Coefficients(a)]);
	b := Polynomial([Qt ! coeff : coeff in Coefficients(b)]); 
	// Now a,b,f have coefficients in a function field.
	f_copy := a/b;
	// Find the content and primitive part of a and b.
	a_gcd := GCD([Numerator(c): c in Coefficients(a)]);
	a_lcm := LCM([Denominator(c): c in Coefficients(a)]);
	b_gcd := GCD([Numerator(c): c in Coefficients(b)]);
	b_lcm := LCM([Denominator(c): c in Coefficients(b)]);
	A := a*(a_lcm/a_gcd);
	B := b*(b_lcm/b_gcd);
	
	// Verify we have found the content of f, and A, B as required.
	f_content := b_lcm*a_gcd/(b_gcd*a_lcm);
	assert f_copy eq f_content*A/B;
	
	// Check that that A, B have coefficients in a polynomial ring.
	assert {Denominator(coeff) : coeff in Coefficients(A)} eq {1};
	assert {Denominator(coeff) : coeff in Coefficients(B)} eq {1};
	
	// Create A, B as polynomials with coefficients in a polynomial ring.
	A := Polynomial([Numerator(coeff) : coeff in Coefficients(A)]);
	B := Polynomial([Numerator(coeff) : coeff in Coefficients(B)]);
	
	// Check that A,B are coprime and primitive.
	assert GCD(A,B) eq 1;
	assert Content(A) eq 1 and Content(B) eq 1;
	return f_content, A, B, ZerosAndPoles(f_content);
end function;

/* Given a nonconstant rational function f with coefficients in a function field,
returns a list of irreducible components of the curve Z_f,
as well as the exceptional set of f over the rationals. */
Z := function(f)
	// Write f in normalized form f = p*A/B.
	p, A, B, exc := Normalize(f); // exc is the exceptional set of f over Q.
	
	// Construct the irreducible components of the curve A(t,x) = 0.
	A2 := AffineSpace(Rationals(),2);
	g := Evaluate(Polynomial([Evaluate(c, A2.1) : c in Coefficients(A)]),A2.2);
	A_curves := [Curve(A2,poly[1]): poly in Factorization(g)];
	return A_curves, exc;
end function;

// An auxiliary function for iteration of rational maps.
Iterate := function(f,n)
	assert n ge 0;
	z := Parent(f).1;
	fn := z;
	for i := 1 to n do
		fn := Evaluate(fn,f);
	end for;
	return fn;
end function;


/* Given a nonconstant rational function f with coefficients in a function field,
returns a finite set of rational numbers c outside of which the specialization
f_c is defined and equal to f(c,x).*/
BadReductionSet := function(f)
p, A, B, exc := Normalize(f); // exc is the exceptional set of f over Q.
A_roots := {r[1]: r in Roots(LeadingCoefficient(A))};
B_roots := {r[1]: r in Roots(LeadingCoefficient(B))};
return exc join A_roots join B_roots;
end function;


/// *** Construction of dynatomic polynomials and curves. *** ///

/* Computes a normalized nth dynatomic polynomial of f,
as well as the content of the nth dynatomic polynomial.
If A is the normalization and p is the content, we have Phi_n = p*A. */
DynatomicPolynomial := function(f,n)
	assert n ge 1;
	F := FieldOfFractions(Parent(f));
	z := F.1;
	PHI := F ! 1;
	f_iterate := z;
	for k := 1 to n do
		f_iterate := Evaluate(f_iterate, f);
		if n mod k eq 0 then
			p := Numerator(f_iterate);
			q := Denominator(f_iterate);
			PHI *:= (z*q - p)^MoebiusMu(n div k);
		end if;
	end for;
	assert Denominator(PHI) eq 1;
	PHI := Numerator(PHI);
	p, A, B := Normalize(PHI); // PHI = p*A/B
	assert B eq 1;
	return A, p;
end function;

/* Computes an affine plane model of the nth dynatomic curve Y_1(n).
A list of irreducible components of Y_1(n) is returned.
In addition, a finite set of exceptional parameters c is returned,
outside of which points (c,alpha) on Y_1(n) correspond to pairs (f_c,alpha)
such that f_c is defined and alpha is n-periodic for f_c. */
DynatomicCurves := function(f,n)
	Phi_n, p := DynatomicPolynomial(f,n); 
	// p is the content of the nth dynatomic polynomial.
	disc := Discriminant(Phi_n);
	assert disc ne 0;
	curves,_ := Z(Phi_n);
	return curves, BadReductionSet(f) join ZerosAndPoles(p) join ZerosAndPoles(disc);
end function;


/// *** Construction of generalized dynatomic polynomials and curves. *** ///

/* Computes a normalized generalized dynatomic polynomial of f,
as well as the content of the generalized dynatomic polynomial.
If A is the normalization and p is the content, we have Phi_{m,n} = p*A. */
GeneralizedDynatomicPolynomial := function(f,m,n)
	assert m ge 1 and n ge 1;
	Phi_n, Phi_n_content := DynatomicPolynomial(f,n);
	if m eq 0 then
		return Phi_n, Phi_n_content;
	else
		fm1 := Iterate(f,m - 1);
		fm := Evaluate(fm1,f);
		PHI := Evaluate(Phi_n,fm)/Evaluate(Phi_n,fm1);
		f_degree := Max(Degree(Numerator(f)),Degree(Denominator(f)));
		S := &+[f_degree^d*MoebiusMu(n div d) : d in Divisors(n)];
		PHI *:= Denominator(fm)^S/Denominator(fm1)^S;
		q,A,B := Normalize(PHI); // PHI = q*A/B
		assert B eq 1;
		Phi_mn_content := q*Phi_n_content;
		return A, Phi_mn_content;
	end if;
end function;

/* Computes an affine plane model of the generalized dynatomic curve Y_1(m,n).
A list of irreducible components of Y_1(m,n) is returned.
In addition, a finite set of exceptional parameters c is returned,
outside of which points (c,alpha) on Y_1(m,n) correspond to pairs (f_c,alpha)
such that f_c is defined and alpha is has pre-periodic type (m,n) for f_c. */
GeneralizedDynatomicCurves := function(f,m,n)
Phi_mn, p := GeneralizedDynatomicPolynomial(f,m,n);
Phi_n, q := DynatomicPolynomial(f,n);
disc := Discriminant(Phi_n);
assert disc ne 0;
curves,_ := Z(Phi_mn);
exceptions := ZerosAndPoles(p) join ZerosAndPoles(q) join ZerosAndPoles(disc);
for i := 1 to m - 1 do
	Phi_in, s := GeneralizedDynatomicPolynomial(f,i,n);
	lambda := Resultant(Phi_mn,Phi_in);
	exceptions join:= ZerosAndPoles(lambda) join ZerosAndPoles(s);
end for;
return curves, exceptions join BadReductionSet(f);
end function;

/// *** Construction of trace polynomials and curves *** ///

/* Computes a normalized nth trace polynomial of f, as well as
the content of the trace polynomial. If A is the normalization
and p is the content, we have T_{n,f} = p*A. */
TracePolynomial := function(f,n)
	assert n ge 1;
	D, content := DynatomicPolynomial(f,n); // Phi_n = content*D
	lc := LeadingCoefficient(D);
	R := Parent(Numerator(f)); 
	z := R.1;
	trace := z;
	iterate := z;
	for i in [1..n-1] do
		iterate := Evaluate(f,iterate);
		trace +:= iterate;
	end for;
	q := Numerator(trace);
	h := Denominator(trace);
	e := Maximum(Degree(q),Degree(h)) - Degree(h);
	_<y> := PolynomialRing(R);
	Dy := Evaluate(D,y);
	hy := Evaluate(h,y);
	qy := Evaluate(q,y);
	quo := Resultant(Dy,hy*z - qy)/(Resultant(D,h)*lc^e);
	_, trace_poly := IsPower(quo,n);
	T := lc*trace_poly;
	assert Denominator(T) eq 1;
	p,A,B := Normalize(T);
	assert B eq 1;
	return A,p/content^e;
end function;

/* Computes an affine plane model of the nth trace curve Y_t(n).
A list of irreducible components of Y_t(n) is returned.
In addition, the exceptional set of the trace polynomial is returned. */
TraceCurves := function(f,n)
	T, p := TracePolynomial(f,n);
	curves,_ := Z(T);
	return curves, ZerosAndPoles(p);
end function;

/// *** Construction of preimage curves *** ///

/* Computes an affine plane model of the mth preimage curve Y(m,P), where P is a rational function.
A list of irreducible components of Y(m,P) is returned. In addition, a finite set of
exceptional parameters c is returned, outside of which points (c,alpha) on Y(m,P) correspond to 
pairs (f_c,alpha) such that f_c and P(c) are defined and f_c^m(alpha) = P(c). */
PreimageCurves_finite := function(f,m,P)
	fm := Iterate(f,m);
	curves, exceptions := Z(fm - P);
	return curves, exceptions join BadReductionSet(f);
end function;

/* Computes an affine plane model of the mth preimage curve Y(m,\infinity).
A list of irreducible components of Y(m,\infinity) is returned. In addition, a finite set of
exceptional parameters c is returned, outside of which points (c,alpha) on Y(m,\infinity)
correspond to pairs (f_c,alpha) such that f_c and P(c) are defined and f_c^m(alpha) = P(c). */
PreimageCurves_infinity := function(f,m)
	fm := Iterate(f,m);
	curves, exceptions := Z(1/fm);
	return curves, exceptions join BadReductionSet(f);
end function;

/// *** Construction of standard maps between modular curves *** ///

// The map Y_1(n) -> Y_1(n) of order n
DynatomicAutomorphism := function(f,n);
	AA := AffineSpace(Rationals(),2);
	dp := DynatomicPolynomial(f,n);
	g := Evaluate(Polynomial([Evaluate(c, AA.1) : c in Coefficients(dp)]), AA.2);
	Y1_n := Curve(AA,g);
	return map<Y1_n->Y1_n|[AA.1,Substitute(f,[AA.1,AA.2])]>;
end function;

// The trace map Y_1(n) -> Y_t(n)
TraceCovering := function(f,n);
	// Construct Y_1(n) and Y_t(n).
	AA := AffineSpace(Rationals(),2);
	dp := DynatomicPolynomial(f,n);
	g := Evaluate(Polynomial([Evaluate(c, AA.1) : c in Coefficients(dp)]), AA.2);
	Y1_n := Curve(AA,g);
	tp := TracePolynomial(f,n);
	g := Evaluate(Polynomial([Evaluate(c, AA.1) : c in Coefficients(tp)]), AA.2);
	Yt_n := Curve(AA,g);
	// Compute the trace function.
	trace := &+[Iterate(f,i) : i in [1..n]];
	return map<Y1_n->Yt_n|[AA.1,Substitute(trace,[AA.1,AA.2])]>;
end function;

// The map Y_1(m,n) -> Y_1(i,n) for 1<= i < m
GeneralizedDynatomicMorphism := function(f,m,n,i)
	assert i lt m and i ge 1;
	// Construct Y_1(m,n) and Y_1(i,n).
	AA := AffineSpace(Rationals(),2);
	dp := GeneralizedDynatomicPolynomial(f,m,n);
	g := Evaluate(Polynomial([Evaluate(c, AA.1) : c in Coefficients(dp)]), AA.2);
	Y1_mn := Curve(AA,g);
	gdp := GeneralizedDynatomicPolynomial(f,i,n);
	g := Evaluate(Polynomial([Evaluate(c, AA.1) : c in Coefficients(gdp)]), AA.2);
	Y1_in := Curve(AA,g);
	// Construct the map Y_1(m,n) -> Y_1(i,n)
	iterate := Iterate(f,m - i);
	return map<Y1_mn->Y1_in|[AA.1,Substitute(iterate,[AA.1,AA.2])]>;
end function;

// The map Y(m,P) -> Y(i,P) for 1 <= i <= m and P finite
PreimageMorphism_finite := function(f,m,P,i)
	assert i ge 1 and i le m;
	AA := AffineSpace(Rationals(),2);
	// Construct the curve Y(m,P).
	_,F,_,_ := Normalize(Iterate(f,m) - P);
	g := Substitute(F,[AA.1,AA.2]);
	YmP := Curve(AA,g);
	// Construct the curve Y(i,P).	
	_,F,_,_ := Normalize(Iterate(f,i) - P);
	g := Substitute(F,[AA.1,AA.2]);
	YiP := Curve(AA,g);
	// Construct the map Y(m,P) -> Y(i,P).
	iterate := Iterate(f,m - i);
	return map<YmP->YiP|[AA.1,Substitute(iterate,[AA.1,AA.2])]>;
end function;

// The map Y(m,infty) -> Y(i,infty) for 1 <= i <= m
PreimageMorphism_infinity := function(f,m,i)
	assert i ge 1 and i le m;
	AA := AffineSpace(Rationals(),2);
	// Construct the curve Y(m,infty).
	_,F,_,_ := Normalize(1/Iterate(f,m));
	g := Substitute(F,[AA.1,AA.2]);
	YmP := Curve(AA,g);
	// Construct the curve Y(i,infty).	
	_,F,_,_ := Normalize(1/Iterate(f,i));
	g := Substitute(F,[AA.1,AA.2]);
	YiP := Curve(AA,g);
	// Construct the map Y(m,infty) -> Y(i,infty).
	iterate := Iterate(f,m - i);
	return map<YmP->YiP|[AA.1,Substitute(iterate,[AA.1,AA.2])]>;
end function;
