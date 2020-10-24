declare type AssocSch;
declare attributes AssocSch: n,deg,R,A,BM,BMA,BME,P,Q,E,mult;

intrinsic Print(X::AssocSch)
  {Returns information about the association scheme.}
  printf "Association scheme of rank %o",Rank(X);
end intrinsic;

intrinsic HadamardProduct(A::Mtrx,B::Mtrx) -> Mtrx
  {Returns the Hadamard (pointwise) product of A and B}
  require Nrows(A) eq Nrows(B) and Ncols(A) eq Ncols(B) : "matrices do not have the same dimensions";
  return Matrix(BaseRing(A),Nrows(A),Ncols(A),[A[i,j]*B[i,j] : j in [1..Ncols(A)] , i in [1..Nrows(A)]]);
end intrinsic;

intrinsic AssociationScheme(A::[Mtrx]) -> AssocSch
  {Returns the association scheme constructed from the adjancency matrices [A1,...,An].}
  X := New(AssocSch);
  X`n := #A;
  X`deg := Nrows(A[1]);
  X`R := BaseRing(A[1]);
  require &and[Ncols(a) eq X`deg and Nrows(a) eq X`deg : a in A] : "matrices are not square or do not have the same dimensions.";
  require &and[Transpose(a) in A : a in A] : "relations are not closed under transpose";
  require &+A eq Matrix(X`R,X`deg,X`deg,[X`R!1 : i in [1..X`deg^2]]) : "matrices do not sum to all one matrix";
  X`A := A;
  X`BM := MatrixAlgebra<X`R,X`deg|A>;
  require Dimension(X`BM) eq X`n : "intersection numbers or not well defined";
  require IsCommutative(X`BM) : "association scheme is not commutative";
  BMdiag,U := Diagonalisation(X`BM);
  X`E := [U^(-1)*B*U : B in Basis(BMdiag)];
  MS := RMatrixSpace(BaseRing(X),Degree(X),Degree(X));
  X`BME := RMatrixSpaceWithBasis([MS!e : e in X`E]);
  X`BMA := RMatrixSpaceWithBasis([MS!a : a in X`A]);
  P := [];
  Q := [];
  for i in [1..X`n] do
    Pii := [];
    Qi := [];
    for j in [1..X`n] do
      Pj := Coordinates(X`BMA,(X`BMA)!(A[i]*A[j]));
      Qj := [X`deg*c : c in Coordinates(X`BME,X`BME!(HadamardProduct(X`E[i],X`E[j])))];
      Append(~Pii,Pj);
      Append(~Qi,Qj);
    end for;
    Append(~P,Pii);
    Append(~Q,Qi);
  end for;
  X`P := P;
  X`Q := Q;
  X`mult := [];
  for i in [1..X`n] do
    Append(~X`mult,Rank(X`E[i]));
  end for;
  return X;
end intrinsic;

intrinsic AssociationScheme(G::GrpPerm) -> AssocSch
  {Returns the association scheme corresponding to a permutation group.}
  X := Labelling(G);
  Y := {@[x,y] : x,y in X@};
  GY := GSet(G,Y);
  A := [];
  for orbit in Orbits(G,GY) do
    M := ZeroMatrix(Rationals(),Degree(G),Degree(G));
    for elt in orbit do
      M[Index(X,elt[1]),Index(X,elt[2])] := 1;
    end for;
    Append(~A,M);
  end for;
  return AssociationScheme(A);
end intrinsic;

intrinsic AssociationScheme(G::GrpPerm,R::Rng) -> AssocSch
  {Returns the association scheme corresponding to a permutation group.}
  X := Labelling(G);
  Y := {@[x,y] : x,y in X@};
  GY := GSet(G,Y);
  A := [];
  for orbit in Orbits(G,GY) do
    M := ZeroMatrix(R,Degree(G),Degree(G));
    for elt in orbit do
      M[Index(X,elt[1]),Index(X,elt[2])] := 1;
    end for;
    Append(~A,M);
  end for;
  return AssociationScheme(A);
end intrinsic;

intrinsic AssociationScheme(D::Mtrx) -> AssocSch
  {Returns the association scheme corresponding to the distance matrix D.}
  n := Ncols(D);
  require n eq Nrows(D) : "the given matrix must be square";
  distances := {@ D[i,j] : i,j in [1..n] , j in [1..n]@};
  A := [ZeroMatrix(Rationals(),n,n) : i in [1..#distances]];
  for i,j in [1..n] do
    A[Index(distances,D[i,j])][i,j] := 1;
  end for;
  return AssociationScheme(A);
end intrinsic;

intrinsic Rank(X::AssocSch) -> RngIntElt
  {Returns the rank of the association scheme.}
  return X`n;
end intrinsic;

intrinsic Dimension(X::AssocSch) -> RngIntElt
  {Returns the dimension of the Bose Mesner algebra of X also known as the rank of X.}
  return Rank(X);
end intrinsic;

intrinsic BoseMesnerAlgebra(X::AssocSch : Gens := "A") -> AlgMat
  {Returns the Bose-Mesner/adjacency algebra of the association scheme.}
  if Gens eq "E" then
    return MatrixAlgebra<BaseRing(X),Degree(X)|PrimitiveIdempotents(X)>;
  else
    return X`BM;
  end if;
end intrinsic;

intrinsic AdjacencyAlgebra(X::AssocSch : Gens := "A") -> AlgMat
  {Returns the Bose-Mesner/adjacency algebra of the association scheme.}
  return BoseMesnerAlgebra(X : Gens := Gens);
end intrinsic;

intrinsic IntersectionNumbers(X::AssocSch) -> []
  {Returns the intersection numbers of X.}
  return X`P;
end intrinsic;

intrinsic IntersectionNumber(X::AssocSch,i::RngIntElt,j::RngIntElt,k::RngIntElt) -> RngElt
  {Returns the intersection number p_ij^k.}
  require i le Rank(X) and j le Rank(X) and k le Rank(X) : "i,j and k should be lower than or equal to the rank of X";
  return X`P[i][j][k];
end intrinsic;

intrinsic BaseRing(X::AssocSch) -> Rng
  {Returns the base ring of X.}
  return X`R;
end intrinsic;

intrinsic IntersectionMatrix(X::AssocSch,k::RngIntElt) -> Mtrx
  {Returns the k-th intersection matrix of A.}
  require k le Rank(X) : "k should be lower than or equal to the rank of X";
  return Matrix(IntegerRing(),Rank(X),Rank(X),[IntersectionNumber(X,i,j,k) : i,j in [1..Rank(X)]]);
end intrinsic;

intrinsic AdjacencyMatrices(X::AssocSch) -> []
  {Returns the adjacency matrices of X.}
  return X`A;
end intrinsic;

intrinsic AdjacencyMatrix(X::AssocSch,i::RngIntElt) -> Mtrx
  {Returns the i-th adjacency matrix of X.}
  require i le Rank(X) : "i should be lower than or equal to the rank of X";
  return AdjacencyMatrices(X)[i];
end intrinsic;

intrinsic DistanceMatrix(X::AssocSch) -> Mtrx
  {Returns the distance matrix of X.}
  A := AdjacencyMatrices(X);
  D := &+[(i-1)*A[i] : i in [1..Rank(X)]];
  return ChangeRing(D,IntegerRing());
end intrinsic;

intrinsic FirstEigenmatrix(X::AssocSch) -> Mtrx
  {Returns the first eigenmatrix of X.}
  M := [];
  for i in [1..Rank(X)] do
    Append(~M,Coordinates(X`BME,X`BME!(X`A[i])));
  end for;
  return Transpose(Matrix(BaseRing(X),Rank(X),Rank(X),M));
end intrinsic;

intrinsic PrimitiveIdempotents(X::AssocSch) -> []
  {Returns the primitive idempotents of X.}
  return X`E;
end intrinsic;

intrinsic PrimitiveIdempotent(X::AssocSch,i::RngIntElt) -> Mtrx
  {Returns the i-th primitive idempotent of X.}
  require i le Rank(X) : "i should be lower than or equal to the rank of X";
  return PrimitiveIdempotents(X)[i];
end intrinsic;

intrinsic SecondEigenmatrix(X::AssocSch) -> Mtrx
  {Returns the second eigenmatrix of X.}
  M := [];
  for i in [1..Rank(X)] do
    Append(~M,Coordinates(X`BMA,X`BMA!(X`E[i])));
  end for;
  return Degree(X)*Transpose(Matrix(BaseRing(X),Rank(X),Rank(X),M));
end intrinsic;

intrinsic KreinParameters(X::AssocSch) -> []
  {Returns the Krein parameters of X.}
  return X`Q;
end intrinsic;

intrinsic KreinParameter(X::AssocSch,i::RngIntElt,j::RngIntElt,k::RngIntElt) -> RngElt
  {Returns the Krein parameter q_ij^k.}
  require i le Rank(X) and j le Rank(X) and k le Rank(X) : "i,j and k should be lower than or equal to the rank of X";
  return KreinParameters(X)[i,j,k];
end intrinsic

intrinsic Multiplicities(X::AssocSch) -> []
  {Returns the multiplicities of X.}
  return X`mult;
end intrinsic;

intrinsic Multiplicity(X::AssocSch,i::RngIntElt) -> RngIntElt
  {Returns the i-th multiplicity of X.}
  require i le Rank(X) : "i should be lower than or equal to the rank of X";
  return Multiplicities(X)[i];
end intrinsic;

intrinsic Degree(X::AssocSch) -> RngIntElt
  {Returns the dimension of X.}
  return X`deg;
end intrinsic;

intrinsic VectorSpace(X::AssocSch) -> ModTupRng
  {Returns the vector space on which the Bose Mesner algebra of X acts.}
  return RSpace(BaseRing(X),Degree(X));
end intrinsic;

intrinsic Eigenspace(X::AssocSch,i::RngIntElt) -> ModTupRng
  {Returns the i-th eigenspace of X, i.e. the row space of E_i.}
  return RowSpace(PrimitiveIdempotent(X,i));
end intrinsic;

intrinsic Eigenspace(X::AssocSch,I::[RngIntElt]) -> ModTupRng
  {Returns the sum of the i-th eigenspaces where i is in I.}
  return RowSpace(&+[PrimitiveIdempotent(X,i) : i in I]);
end intrinsic;

intrinsic PointwiseProduct(u::ModTupRngElt,v::ModTupRngElt) -> ModTupRngElt
  {Returns the pointwise product of u and v.}
  require Degree(u) eq Degree(v) : "u and v should have the same degree";
  return RSpace(BaseRing(u),Degree(u))![u[i]*v[i] : i in [1..Degree(u)]];
end intrinsic;

intrinsic Sigma(X::AssocSch,i::RngIntElt,j::RngIntElt,k::RngIntElt) -> Map
  {Returns the homomorphism sigma_ij^k: V tensor V -> V_i tensor V_j -> V_k.}
  V := VectorSpace(X);
  Ei := PrimitiveIdempotent(X,i);
  Ej := PrimitiveIdempotent(X,j);
  Ek := PrimitiveIdempotent(X,k);
  return hom<TensorProduct(V,V) -> Eigenspace(X,k) | [Eigenspace(X,k)!(PointwiseProduct(Ei[x],Ej[y])*Ek) : x,y in [1..Dimension(V)]]>;
end intrinsic;

intrinsic Sigma(X::AssocSch,I::[RngIntElt],J::[RngIntElt],K::[RngIntElt]) -> Map
  {Returns the homomorphism sigma_ij^k: V tensor V -> V_i tensor V_j -> V_k.}
  V := VectorSpace(X);
  Ei := &+[PrimitiveIdempotent(X,i) : i in I];
  Ej := &+[PrimitiveIdempotent(X,j) : j in J];
  Ek := &+[PrimitiveIdempotent(X,k) : k in K];
  return hom<TensorProduct(V,V) -> Eigenspace(X,K) | [Eigenspace(X,K)!PointwiseProduct(Ei[x],Ej[y])*Ek : x,y in [1..Dimension(V)]]>;
end intrinsic;

intrinsic 'eq'(X::AssocSch,Y::AssocSch) -> BoolElt
  {Checks whether X and Y are equal.}
  return AdjacencyMatrices(X) eq AdjacencyMatrices(Y);
end intrinsic;

declare type NorAlg[NorAlgElt];
declare attributes NorAlg: X,i,Vi,proj;
declare attributes NorAlgElt: v,NA;

intrinsic NortonAlgebra(X::AssocSch,i::RngIntElt) -> NorAlg
  {Returns the i-th Norton algebra of X.}
  NA := New(NorAlg);
  NA`X := X;
  NA`i := i;
  NA`Vi := Eigenspace(X,i);
  NA`proj := PrimitiveIdempotent(X,i);
  return NA;
end intrinsic;

intrinsic Print(NA::NorAlg)
  {Prints information about the Norton algebra.}
  printf "Norton algebra with index %o of association scheme with rank %o", Index(NA),Rank(AssociationScheme(NA));
end intrinsic;

intrinsic VectorSpace(NA::NorAlg) -> ModTupRng
  {Returns the underlying vector space of the Norton algebra.}
  return NA`Vi;
end intrinsic;

intrinsic Degree(NA::NorAlg) -> RngIntElt
  {Returns the degree of the Norton algebra.}
  return Degree(NA`X);
end intrinsic;

intrinsic Dimension(NA::NorAlg) -> RngIntElt
  {Returns the dimension of the Norton algebra.}
  return Multiplicity(AssociationScheme(NA),Index(NA));
end intrinsic;

intrinsic Index(NA::NorAlg) -> RngIntElt
  {Returns the index of the Norton algebra.}
  return NA`i;
end intrinsic;

intrinsic AssociationScheme(NA::NorAlg) -> AssocSch
  {Returns the association scheme of the Norton algebra.}
  return NA`X;
end intrinsic;

intrinsic Projection(NA::NorAlg) -> Mtrx
  {Returns the projection matrix of the Norton algebra.}
  return NA`proj;
end intrinsic;

intrinsic 'eq'(NA1::NorAlg,NA2::NorAlg) -> BoolElt
  {Returns whether NA1 and NA2 are the same Norton algebras.}
  return AssociationScheme(NA1) eq AssociationScheme(NA2) and Index(NA1) eq Index(NA2);
end intrinsic;

intrinsic Parent(v::NorAlgElt) -> NorAlg
  {Returns the Norton algebra of v.}
  return v`NA;
end intrinsic

intrinsic 'in'(v::NorAlgElt,NA::NorAlg) -> BoolElt
  {Returns whether v is contained in the Norton algebra.}
  return Parent(v) eq NA;
end intrinsic;

intrinsic IsCoercible(NA::NorAlg,y::.) -> BoolElt, .
  {Returns whether y is coercible into NA and the result if so.}
  if Type(y) eq NorAlgElt then
    if y in NA then
      return true,y;
    else
      return false, "Illegal coercion";
    end if;
  else
    V := VectorSpace(NA);
    b,v := IsCoercible(V,y);
    if b then
      u := New(NorAlgElt);
      u`v := v;
      u`NA := NA;
      return true,u;
    else
      return false, "Illegal coercion";
    end if;
  end if;
end intrinsic;

intrinsic Vector(u::NorAlgElt) -> ModTupRngElt
  {Returns the underlying vector of u.}
  return u`v;
end intrinsic;

intrinsic Print(u::NorAlgElt)
  {Prints u.}
  printf "%o" , Vector(u);
end intrinsic;

intrinsic '+'(u::NorAlgElt,v::NorAlgElt) -> NorAlgElt
  {Returns u+v.}
  require Parent(u) eq Parent(v): "u and v are not contained in the same Norton algebra";
  return Parent(u)!(Vector(u) + Vector(v));
end intrinsic;

intrinsic '-'(u::NorAlgElt) -> NorAlgElt
  {Returns -u.}
  return Parent(u)!(-Vector(u));
end intrinsic;

intrinsic '-'(u::NorAlgElt,v::NorAlgElt) -> NorAlgElt
  {Returns u-v.}
  require Parent(u) eq Parent(v): "u and v are not contained in the same Norton algebra";
  return Parent(u)!(Vector(u)-Vector(v));
end intrinsic;

intrinsic '*'(a::RngElt,u::NorAlgElt) -> NorAlgElt
  {Returns a*u.}
  return Parent(u)!(a*Vector(u));
end intrinsic;

intrinsic '*'(u::NorAlgElt,a::RngElt) -> NorAlgElt
  {Returns a*u.}
  return Parent(u)!(a*Vector(u));
end intrinsic;

intrinsic '/'(u::NorAlgElt,a::RngElt) -> NorAlgElt
  {Returns u/a.}
  return Parent(u)!(Vector(u)/a);
end intrinsic;

intrinsic '*'(u::NorAlgElt,v::NorAlgElt) -> NorAlgElt
  {Returns u*v.}
  require Parent(u) eq Parent(v): "u and v are not contained in the same Norton algebra";
  NA := Parent(u);
  return NA!(PointwiseProduct(Vector(u),Vector(v))*Projection(NA));
end intrinsic;

intrinsic Idempotent(NA::NorAlg,i::RngIntElt) -> NorAlgElt
  {Returns the i-th idempotent of the Norton algebra.}
  require i le Degree(NA) : "i must be lower than or equal to the degree of NA";
  k := Index(NA);
  qkkk := KreinParameter(AssociationScheme(NA),k,k,k);
  require qkkk ne 0 : "Norton algebra is zero algebra";
  return NA!((Degree(NA)/qkkk)*(NA!Projection(NA)[i]));
end intrinsic;

intrinsic '.'(NA::NorAlg,i::RngIntElt) -> NorALgElt
  {Returns the i-th idempotent of the Norton algebra.}
  return Idempotent(NA,i);
end intrinsic;

intrinsic 'eq'(u::NorAlgElt,v::NorAlgElt) -> BoolElt
  {Returns whether u is equal to v.}
  return Parent(u) eq Parent(v) and Vector(u) eq Vector(v);
end intrinsic;
