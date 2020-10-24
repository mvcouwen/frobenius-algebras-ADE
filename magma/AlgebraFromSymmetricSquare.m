// Most of this code is written by Tom De Medts and Sergey Shpectorov

function AlgebraFromSymmetricSquare(R)
  L := LieAlgebra(R, Rationals());
  dd := Dimension(L);
  e,f,h := ChevalleyBasis(L);
  M := KillingForm(L);
  M := M/M[1,Dimension(L)];

  // Adjoint module

  A := AdjointModule(L: LeftAction := true);
  AV := VectorSpace(A);

  // Here it really starts
  // Compute the symmetric square of A as a right module
  inds := {@ [i,j] : j in [i..Dimension(AV)] , i in [1..Dimension(AV)]@};
  Sort(~inds);
  SV := RModule(CoefficientRing(L),#inds);
  act := function(x,v) // x is an element of L, v is an element of SV
    cc := Coordinates(SV,v);
    w := Zero(SV);
    for i in [1..#cc] do
      if not IsZero(cc[i]) then
        ii := inds[i];
        for j in [1..2] do
          crds := [* A.ii[r] : r in [1..2] *];
          crds[j] := x^crds[j];
          if not &or[ IsZero(u) : u in crds ] then
            crds := [ Coordinates(A,crds[r]) : r in [1..2]];
            vec_inds := [ [] ];
            cfs := [cc[i]];
            for k in [1..#crds] do
              inds1 := [];
              cfs1 := [];
              for r in [1..#crds[k]] do
                if not IsZero( crds[k][r] ) then
                  for t in [1..#vec_inds] do
                    Append(~inds1 , vec_inds[t] cat [r]);
                    Append(~cfs1 , cfs[t]*crds[k][r] );
                  end for;
                end if;
              end for;
              vec_inds := inds1;
              cfs := cfs1;
            end for;
            u := Eltseq(Zero(SV));
            for k in [1..#vec_inds] do
              Sort( ~vec_inds[k]);
              u[ Index( inds,vec_inds[k])] +:= cfs[k];
            end for;
            w := w + SV!u;
          end if;
        end for;
      end if;
    end for;
    return w;
  end function;
  S:= Module(L,map<CartesianProduct(L,SV) -> SV | t :-> act(t[1],t[2])>);
  VS := VectorSpace(S);
  fu := function(tuple)
    cc := [];
    for i in [1..#tuple] do
      Append(~cc,Coordinates(A,tuple[i]));
    end for;
    vec_inds := [ [] ];
    cfs := [ 1 ];
    for k in [1..#cc] do
      inds1 := [];
      cfs1 := [];
      for r in [1..#cc[k]] do
        if not IsZero(cc[k][r]) then
          for t in [1..#vec_inds] do
            Append( ~inds1 , vec_inds[t] cat [r]);
            Append( ~cfs1, cfs[t]*cc[k][r]);
          end for;
        end if;
      end for;
      vec_inds := inds1;
      cfs := cfs1;
    end for;
    u := Eltseq(Zero(S));
    for k in [1..#vec_inds] do
      Sort(~vec_inds[k]);
      u[ Index(inds,vec_inds[k])] +:= cfs[k];
    end for;
    return S!u;
  end function;
  phi := map<CartesianProduct([A,A]) -> S | t :-> fu(t) >;
  phiL := function (a,b)
    return phi(A!AV!a, A!AV!b);
  end function;
  D := Decomposition(S);
  WV,V := WeightsAndVectors(S);

  BLstr := ["f" cat IntegerToString(#PositiveRoots(R)-i+1) : i in [1..#PositiveRoots(R)]];
  BLstr cat:= ["h" cat IntegerToString(i) : i in [1..Rank(R)]];
  BLstr cat:= ["e" cat IntegerToString(i) : i in [1..#PositiveRoots(R)]];
  BSstr := [BLstr[ind[1]] cat "." cat BLstr[ind[2]] : ind in inds];

  PrintElementOfS2L := procedure(v)
    c := Coordinates(VS, VS!S!v);
    zero := true;
    for i in [1..#c] do
      co := c[i];
      if co ne 0 then print co,BSstr[i]; zero := false; end if;
    end for;
    if zero then print 0; end if;
  end procedure;

  Phi := [[phi(A.i,A.j) : i in [1..Dimension(A)]] : j in [1..Dimension(A)]];

  MultiplyInS2L := function(a, b)
    c := Coordinates(VS, VS!a);
    d := Coordinates(VS, VS!b);
    res := S!0;
    for i in [1..#c] do
      cc := c[i];
      if cc ne 0 then
        for j in [1..#c] do
          dd := d[j];
          if dd ne 0 then
            a1 := inds[i][1];
            a2 := inds[i][2];
            a3 := inds[j][1];
            a4 := inds[j][2];
            res +:= 1/4 * cc * dd * (M[a1,a3] * Phi[a2,a4] + M[a1,a4] * Phi[a2][a3] + M[a2,a3] * Phi[a1][a4] + M[a2,a4] * Phi[a1][a3]);
          end if;
        end for;
      end if;
    end for;
    return(res);
  end function;

  BS2L := function(a,b)
    c := Coordinates(VS,VS!S!a);
    d := Coordinates(VS,VS!S!b);
    res := 0;
    for i in [1..#c] do
      cc := c[i];
      if cc ne 0 then
        for j in [1..#c] do
          dd := d[j];
          if dd ne 0 then
            a1 := inds[i][1];
            a2 := inds[i][2];
            a3 := inds[j][1];
            a4 := inds[j][2];
            res +:= 1/2*cc*dd*(M[a1,a3]*M[a2,a4] + M[a2,a3]*M[a1,a4]);
          end if;
        end for;
      end if;
    end for;
    return res;
  end function;

  MS2L := procedure(a, b)
    PrintElementOfS2L(MultiplyInS2L(a,b));
  end procedure;

  Ba := [];
  Dims := []; i := 1;
  for ee in D do
    dim := Dimension(ee);
    Append(~Dims, [i,i+dim-1]);
    i +:= dim;
  end for;

  for i in [1..#D] do
    bb := Basis(D[i]);
    Ba cat:= [S!b : b in bb];
  end for;

  VB := VectorSpaceWithBasis([VS!b : b in Ba]);

  ProjectionDecomposition := function(v)
    r := [* *];
    for i in [1..#D] do
      v := VB!S!v;
      co := Coordinates(VB, v);
      res := S!0;
      for j in [Dims[i][1]..Dims[i][2]] do
        res +:= co[j]*Ba[j];
      end for;
      Append(~r, D[i]!res);
    end for;
    return r;
  end function;

  comp := [i : i in [1..#D] | not 2*HighestRoot(R) in Weights(D[i])];
  basisAl := [];
  for i in comp do
    for j in [Dims[i][1]..Dims[i][2]] do
      Append(~basisAl,Ba[j]);
    end for;
  end for;

  Al := sub<S|basisAl>;

  ProjectionOntoAl := function(v)
    dec := ProjectionDecomposition(v);
    vproj := &+[S!dec[i] : i in comp];
    return Al!vproj;
  end function;

  Overline := hom< S -> Al | Matrix([ProjectionOntoAl(b):b in Basis(S)])>;

  MInAl := function(v,w)
    return Overline(MultiplyInS2L(S!v,S!w));
  end function;

  BInAl := function(v,w)
    return BS2L(S!v,S!w);
  end function;

  AdjointInAl := function(v)
    return Matrix([MInAl(Al.i,v) : i in [1..Dimension(Al)]]);
  end function;

  Nlambda := function(l)
    res := [];
    for i in [1..#Roots(R)] do
      for j in [i..#Roots(R)] do
        if Root(R,i)+Root(R,j) eq l then
          Append(~res,[i,j]);
        end if;
      end for;
    end for;
    return res;
  end function;

  nlambda := function(l)
    return #Nlambda(l);
  end function;

  return L,S,Al,Overline,phiL,PrintElementOfS2L,MInAl,BInAl;
end function;
