t := Cputime();
print "STEP 1: ",Cputime(t);
R := RootDatum("D5" : Isogeny := "SC");
M := CartanMatrix(R);
F := Rationals();
M := ChangeRing(M,F);
M := M^(-1);
V := RootSpace(R);
n := Dimension(R);
roots := [r : r in Roots(R)];
coroots := [cr : cr in Coroots(R)];
r := #roots;
e := #PositiveRoots(R);

Jmatgens := [Transpose(Matrix(coroots[i]))*Matrix(roots[i]) : i in [1..e]];
Jmat := sub<KMatrixSpace(F,n,n) | Jmatgens>;
J := sub<KSpace(F,Dimension(Jmat)) | [Vector(Coordinates(Jmat,j)) : j in Jmatgens]>;
getMat := hom<J -> Jmat | Basis(Jmat)>;
getVec := hom<Jmat -> J | Basis(J)>;

Z := KSpace(F,e);

S,emJ,emZ,projJ,projZ := DirectSum(J,Z);

MS := function(a,b)
  ja := getMat(projJ(a));
  jb := getMat(projJ(b));
  za := projZ(a);
  zb := projZ(b);
  jp := getVec(1/2*(ja*jb + jb*ja));
  zp := 1/2*Parent(za)![za[i]*zb[i] : i in [1..Degree(za)]];
  return emJ(jp) + emZ(zp);
end function;

BS := function(a,b)
  ja := getMat(projJ(a));
  jb := getMat(projJ(b));
  za := projZ(a);
  zb := projZ(b);
  res := 0;
  res +:= Trace(ja*jb);
  res +:= 1/2*(za,zb);
  return res;
end function;

print "STEP 2: ",Cputime(t);
Wc := CoxeterGroup(R);
W := ActionImage(Wc,OrbitClosure(Wc,{@ Reflection(Wc,i) : i in [1..e] @}));

Attach("AssocSch.m");
X := AssociationScheme(W);
P := IntersectionNumbers(X);
dist := DistanceMatrix(X);
orbrep := [Index(Eltseq(dist[1]),i-1) : i in [1..Rank(X)]];
b := [Trace(Jmat.1*Jmat.i) : i in orbrep];
coeff := ZeroMatrix(F,Rank(X),Rank(X));
for i in [1..Rank(X)] do
  for k in [1..Rank(X)] do
    coeff[i,k] := &+[P[i,j,k]*b[j] : j in [1..Rank(X)]];
  end for;
end for;
for i in [1..Rank(X)] do
  coeff[i,i] := coeff[i,i] + 2;
end for;
con := Vector(F,Rank(X),[b[k] : k in [1..Rank(X)]]);
mu := Solution(coeff,con);

Agens := [emJ(J.i) + &+[mu[dist[i,j]+1]*(emJ(-1*J.j) + emZ(2*Z.j)) : j in [1..e] ] : i in [1..e] ];
A := sub<S | Agens>;
gensJmat := Matrix(BaseRing(J),e,Degree(J),[J.i : i in [1..e]]);
gensAmat := Matrix(BaseRing(A),e,Degree(A),[A.i : i in [1..e]]);
projAhelp := function(s)
  j := projJ(s);
  z := projZ(s);
  lincomb := Solution(gensJmat,j);
  res := A!0;
  res +:= lincomb*gensAmat;
  res +:= 1/2*z*gensAmat;
  return res;
end function;
projA := hom< S -> A | [projAhelp(s) : s in Basis(S)]>;
isomAJhelp := function(s)
  lincomb := Solution(gensAmat,projA(s));
  return lincomb*gensJmat;
end function;
isomAJ := hom< S -> J | [isomAJhelp(s) : s in Basis(S)]>;

MA := function(j1,j2)
  s1 := projA(emJ(j1));
  s2 := projA(emJ(j2));
  ms := MS(s1,s2);
  ma := projA(ms);
  return isomAJ(ma);
end function;

BA := function(j1,j2)
  s1 := projA(emJ(j1));
  s2 := projA(emJ(j2));
  return BS(s1,s2);
end function;

print "STEP 3: ",Cputime(t);
Hroot := KSpace(F,n-1);
Hrootem := [Eigenspace(J,0) : J in Jmatgens];
orthorootinv := [hom<Hroot -> V | BasisMatrix(Hrootem[i])> : i in [1..e]];
orthorootinv := orthorootinv cat orthorootinv;
orthoroot := [hom<V -> Hroot | [Vector(Coordinates(Hrootem[i],v - v*1/2*Jmat.i)) : v in Basis(V)]> : i in [1..e]];
orthoroot := orthoroot cat orthoroot;

Vlambda := KSpace(F,1);

Lambda0 := [];
chosenpairs := [];
for i,j in [1..2*e] do
  if (Root(R,i),Coroot(R,j)) eq 0 then
    lambda := Root(R,i) + Root(R,j);
    if Index(Lambda0, lambda) eq 0 then
      Append(~Lambda0,lambda);
      Append(~chosenpairs,[i,j]);
    end if;
  end if;
end for;
Nlambda := [{@{@i,j@} : i,j in [1..r] | Root(R,i) + Root(R,j) eq l@} : l in Lambda0];
nlambda := [#N : N in Nlambda];
function posrootrep(i)
  if i gt e then
    return i-e;
  else
    return i;
  end if;
end function;
jlambda := [1/(4*#N)*&+[J.(posrootrep(P[1])) + J.(posrootrep(P[2])) : P in N] : N in Nlambda];

W := [ V!0 ] cat roots cat Lambda0;
w := #W;
nl := #Lambda0;
nw := 1+r+nl;

ALG,em,proj := DirectSum([J] cat [Hroot : i in [1..2*e]] cat [Vlambda : i in [1..nl]]);

print "STEP 4: ",Cputime(t);
// Summary of different types
// type 0 : 0 and 0
// type 1 : 0 and root
// type 2 : 0 and lambda
// type 3 : root and -root
// type 4 : root and root, inner -1
// type 5 : root and root, inner 0
// type 6 : root and root, inner > 0
// type 7 : root and lambda, inner -2
// type 8 : root and lambda, inner -1 with alpha_lambda
// type 9 : root and lambda, inner -1 with beta_lambda
// type 10 : root and lambda, inner > -1
// type 11 : lambda and -lambda
// type 12 : lambda and lambda, inner -3
// type 13 : lambda and lambda, inner -2
// type 14 : lambda and lambda, inner > -2

type := ZeroMatrix(IntegerRing(),1+2*e+#Lambda0,1+2*e+#Lambda0);
sum := ZeroMatrix(IntegerRing(),1+2*e+#Lambda0,1+2*e+#Lambda0);
negative := [1];

for i in [2..1+r] do
  type[1,i] := 1;
  type[i,1] := -1;
  Append(~negative,1+Negative(R,i-1));
  for j in [2..1+r] do
    case (roots[i-1],coroots[j-1]):
      when -2:
        type[i,j] := 3;
        type[j,i] := 3;
      when -1:
        type[i,j] := 4;
        type[j,i] := 4;
      when 0:
        type[i,j] := 5;
        type[j,i] := 5;
      else:
        type[i,j] := 6;
        type[j,i] := 6;
    end case;
  end for;
  for j in [2+r..w] do
    case (Lambda0[j-1-r],coroots[i-1]):
      when -2:
        type[i,j] := 7;
        type[j,i] := -7;
      when -1:
        if (roots[i-1],coroots[chosenpairs[j-1-r][1]]) eq -1 then
          type[i,j] := 8;
          type[j,i] := -8;
        else
          type[i,j] := 9;
          type[j,i] := -9;
        end if;
      else:
        type[i,j] := 10;
        type[j,i] := -10;
    end case;
  end for;
end for;

for i in [2+r..w] do
  type[1,i] := 2;
  type[i,1] := -2;
  sum[1,i] := i;
  sum[i,1] := i;
  Append(~negative,1+r+Index(Lambda0,-Lambda0[i-1-r]));
  for j in [2+r..w] do
    case (Lambda0[i-1-r],coroots[chosenpairs[j-1-r][1]] + coroots[chosenpairs[j-1-r][2]]):
      when -4:
        type[i,j] := 11;
        type[j,i] := 11;
      when -3:
        type[i,j] := 12;
        type[j,i] := 12;
      when -2:
        type[i,j] := 13;
        type[j,i] := 13;
      else:
        type[i,j] := 14;
        type[j,i] := 14;
    end case;
  end for;
end for;

for i,j in [1..w] do
  sum[i,j] := Index(W,W[i]+W[j]);
  sum[j,i] := sum[i,j];
end for;

c := ZeroMatrix(IntegerRing(),r,r);
f := ZeroMatrix(IntegerRing(),r,r);
for i,j in [1..r] do
  if type[i+1,j+1] eq 4 then
    c[i,j] := LieConstant_N(R,i,j);
  end if;
  if type[i+1,j+1] eq 5 then
    lambda := sum[i+1,j+1]-1-r;
    if i in chosenpairs[lambda] then
      f[i,j] := 1;
    else
      f[i,j] := -LieConstant_N(R,i,Negative(R,chosenpairs[lambda][1]))/LieConstant_N(R,j,Negative(R,chosenpairs[lambda][2]));
    end if;
  end if;
end for;

dhelp := function(ri,v,j)
  case type[j,ri+1]:
    when 1:
      return 2*orthoroot[ri](-roots[ri]*getMat(v)),ri+1;
    when 3:
      vlift := Matrix(orthorootinv[j-1](v));
      return 1/2*getVec(M*Transpose(vlift)*Matrix(roots[ri]) + Transpose(Matrix(coroots[ri])) * vlift),sum[ri+1,j];
    when 4:
      rs := sum[ri+1,j]-1;
      vlift := orthorootinv[j-1](v);
      return c[ri,j-1]*orthoroot[rs](vlift + (vlift,coroots[ri])*roots[j-1]),rs+1;
    when 5:
      return -(orthorootinv[j-1](v),coroots[ri])*f[ri,j-1]*Vlambda.1,sum[ri+1,j];
    when 6:
      return 0,0;
    when -7:
      rs := sum[ri+1,j]-1;
      return f[rs,negative[1+ri]-1]*v[1]*orthoroot[rs](roots[ri]),rs+1;
    when -8:
      cp := chosenpairs[j-r-1];
      acp1 := sum[ri+1,cp[1]+1]-1;
      return c[ri,cp[1]]*f[acp1,cp[2]]*v,sum[ri+1,j];
    when -9:
      cp := chosenpairs[j-r-1];
      acp2 := sum[ri+1,cp[2]+1]-1;
      return c[ri,cp[2]]*f[cp[1],acp2]*v,sum[ri+1,j];
    when -10:
      return 0,0;
  end case;
end function;

dFAST := function(ri,v,ind)
  res := ALG!0;
  indres := {};
  for i in ind do
    r,rind := dhelp(ri,proj[i](v),i);
    if rind ne 0 then
      res +:= em[rind](r);
      Include(~indres,rind);
    end if;
  end for;
  return res,indres;
end function;

getInd := function(v)
  return { i : i in [1..w] | not IsZero(proj[i](v))};
end function;

d := function(ri,v)
  return dFAST(ri,v,getInd(v));
end function;

function mhelp(vi,i,vj,j)
  t := type[i,j];
  if t lt 0 then
    return mhelp(vj,j,vi,i);
  elif t in [6,10,14] then
    return 0,0;
  elif t eq 0 then
    return MA(vi,vj),1;
  elif t eq 1 then
    return dhelp(j-1,MA(vi,1/2*dhelp(negative[j]-1,vj,j)),1),j;
  elif t eq 2 then
    return vj[1]*BA(vi,jlambda[j-1-r])*Vlambda.1,j;
  elif t in [3,4,5,7,8,9] then
    s := sum[i,j];
    return 1/2*dhelp(i-1,mhelp(dhelp(negative[i]-1,vi,i),1,vj,j),j) - 1/2*mhelp(dhelp(negative[i]-1,vi,i),1,dhelp(i-1,vj,j),s),s;
  elif t in [11,12,13] then
    a := chosenpairs[i-1-r][1];
    v1new,i1new := dhelp(negative[a+1]-1,vi,i);
    s1 := sum[i1new,j];
    s2 := sum[a+1,j];
    ts := sum[i,j];
    if s1 ne 0 then
      if s2 ne 0 then
        v2new,i2new := dhelp(a,vj,j);
        return 1/2*dhelp(a,mhelp(v1new,i1new,vj,j),s1) - 1/2*mhelp(v1new,i1new,v2new,i2new),ts;
      else
        return 1/2*dhelp(a,mhelp(v1new,i1new,vj,j),s1),ts;
      end if;
    elif s2 ne 0 then
      v2new,i2new := dhelp(a,vj,j);
      return -1/2*mhelp(v1new,i1new,v2new,i2new),ts;
    end if;
  end if;
end function;

mFAST := function(v1,ind1,v2,ind2)
  res := ALG!0;
  for i in ind1 do
    for j in ind2 do
      m,indm := mhelp(proj[i](v1),i,proj[j](v2),j);
      if indm ne 0 then
        res +:= em[indm](m);
      end if;
    end for;
  end for;
  return res;
end function;

m := function(v1,v2)
  return mFAST(v1,getInd(v1),v2,getInd(v2));
end function;

function bhelp(vi,i,vj,j)
  t := type[i,j];
  if t lt 0 then
    return bhelp(vj,j,vi,i);
  elif t in [1,2,4,5,6,7,8,9,10,12,13,14] then
    return 0;
  elif t eq 0 then
    return BA(vi,vj);
  elif t eq 3 then
    return -1/2*bhelp(dhelp(negative[i]-1,vi,i),1,dhelp(i-1,vj,j),1);
  elif t eq 11 then
    cp := chosenpairs[i-r-1];
    return vi[1]*vj[1]*f[negative[cp[1]+1]-1,negative[cp[2]+1]-1]/(2*nlambda[i-1-r]);
  end if;
end function;

bFAST := function(v1,ind1,v2,ind2)
  res := 0;
  for i in ind1 do
    for j in ind2 do
      res +:= bhelp(proj[i](v1),i,proj[j](v2),j);
    end for;
  end for;
  return res;
end function;

b := function(v1,v2)
  return bFAST(v1,getInd(v1),v2,getInd(v2));
end function;

load "AlgebraFromSymmetricSquare.m";
test := function()
  L,S,Al,Overline,phiL,PrintElementOfS2L,MinAl,BinAl := AlgebraSLOW(R);

  VAl := VectorSpace(Al);
  ea,fa,ha := ChevalleyBasis(L);
  ea := ea cat fa;
  ha := [ea[i]*fa[i] : i in [1..e]];

  ALGgens0 := [em[1](J.i) : i in [1..e]];
  ALGgensroot := [em[1+i](orthoroot[i](Root(R,j))) : j in [1..n] , i in [1..r] ];
  ALGgenslambda := [em[1+r+i](Vlambda.1) : i in [1..nl]];
  ALGgensmat := Matrix(ALGgens0 cat ALGgensroot cat ALGgenslambda);

  Al0 := [VAl!Overline(phiL(ha[i],ha[i])) : i in [1..e]];
  Alroot := [VAl!Overline(phiL(ea[i],ha[j])) : j in [1..n] , i in [1..r]];
  Allambda := [VAl!Overline(phiL(ea[cp[1]],ea[cp[2]])) : cp in chosenpairs];
  Algensmat := Matrix(Al0 cat Alroot cat Allambda);

  ALGtoVAl := hom<ALG -> VAl | [Solution(ALGgensmat,v)*Algensmat : v in Basis(ALG)]>;
  VAltoALG := hom<VAl -> ALG | [Solution(Algensmat,v)*ALGgensmat : v in Basis(VAl)]>;

  bool1 := true;
  for i in [1..r] do
    for v in Basis(ALG) do
      if (Al!ALGtoVAl(d(i,v)) ne ((ea[i]^Al!ALGtoVAl(v)))) then
        bool1 := false;
      end if;
    end for;
  end for;
  print "di corresponds to action of ei: ", bool1;

  bool2 := true;
  for v1 in Basis(ALG) do
    for v2 in Basis(ALG) do
      bool2 := bool2 and (Al!ALGtoVAl(m(v1,v2)) eq MinAl(Al!ALGtoVAl(v1),Al!ALGtoVAl(v2)));
    end for;
  end for;
  print "multiplication is correct: ", bool2;

  bool3 := true;
  for v1 in Basis(ALG) do
    for v2 in Basis(ALG) do
      bool3 := bool3 and (b(v1,v2) eq BinAl(Al!ALGtoVAl(v1),Al!ALGtoVAl(v2)));
    end for;
  end for;
  print "bilinear form is correct: ", bool3;

  bool4 := true;
  for i in [1..10] do
    v1 := ALG![Random(500) : i in [1..Dimension(ALG)]];
    v2 := ALG![Random(500) : i in [1..Dimension(ALG)]];
    if (Al!ALGtoVAl(m(v1,v2)) ne MinAl(Al!ALGtoVAl(v1),Al!ALGtoVAl(v2))) then
      bool4 := false;
    end if;
  end for;
  print "random multiplication is correct: ", bool4;

  bool5 := true;
  for i in [1..10] do
    v1 := ALG![Random(500) : i in [1..Dimension(ALG)]];
    v2 := ALG![Random(500) : i in [1..Dimension(ALG)]];
    if (b(v1,v2) ne BinAl(Al!ALGtoVAl(v1),Al!ALGtoVAl(v2))) then
      bool5 := false;
    end if;
  end for;
  print "random bilinear form is correct: ", bool5;
  return &and[bool1,bool2,bool3,bool4,bool5];
end function;

adjoint := function(v)
  ind := getInd(v);
  M := [];
  for x in Basis(J) do
    Append(~M,mFAST(em[1](x),{1},v,ind));
  end for;
  for i in [1..r] do
    for x in Basis(Hroot) do
      Append(~M,mFAST(em[1+i](x),{1+i},v,ind));
    end for;
  end for;
  for i in [1..nl] do
    for x in Basis(Vlambda) do
      Append(~M,mFAST(em[1+r+i](x),{1+r+i},v,ind));
    end for;
  end for;
  return Matrix(F,Dimension(ALG),Dimension(ALG),M);
end function;

v := ALG![Random(0,100) : i in [1..Dimension(ALG)]];
w := ALG![Random(0,100) : i in [1..Dimension(ALG)]];
t := Cputime();
print "test ", Cputime(t);
prod := m(v,w);
print "time to compute product: ", Cputime(t);

// k := &+[1 : r in roots | (r,coroots[1]) in {1,-1}]/2;
// unit := (6+k)/2*em[1](getVec(Jmat!IdentityMatrix(F,n)));
// j1 := em[1](J.1);
// Eigenvalues(adjoint(j1));
// j2 := em[1](J.2);
// j3 := em[1](J.3);

// Solution(Matrix([em[1](j) : j in Generators(J)]), m(j1,j1));
// Solution(Matrix([em[1](j) : j in Generators(J)]), m(j1,j2));
// Solution(Matrix([em[1](j) : j in Generators(J)]), m(j1,j3));

// j20 := em[1](J.20);
// Solution(Matrix([unit,j1,j20]),m(j1,j1));
// Eigenvalues(adjoint(a1));
// print "b(a1,a1) = ", b(a1,a1);

/*
j := function(h1,h2)
  return 1/4*getVec(M*Transpose(Matrix(h1))*Matrix(h2) + M*Transpose(Matrix(h2))*Matrix(h1));
end function;

ALGV := RModule(F,Dimension(ALG));

print "STEP 5: ",Cputime(t);
L := LieAlgebra(R,F);
ea,fa,ha := ChevalleyBasis(L);
LV := VectorSpaceWithBasis([Vector(v) : v in ea cat fa cat ha]);
actionLiehelp := function(t)
  coord := Coordinates(LV,LV!t[2]);
  res := Zero(ALGV);
  for i in [1..r] do
    if coord[i] ne 0 then
      res +:= coord[i]*ALGV!d(i,ALG!t[1]);
    end if;
  end for;
  for i in [1..n] do
    if coord[r+i] ne 0 then
      res +:= coord[r+i]*ALGV!(d(i,d(e+i,ALG!t[1])) - d(e+i,d(i,ALG!t[1])));
    end if;
  end for;
  return res;
end function;

actionLie := map<CartesianProduct(ALGV,L) -> ALGV | t :-> actionLiehelp(t)>;

ALGM := Module(L,actionLie);

La := sub< L | &cat[[ea[i],fa[i]] : i in [1..e] | (Root(R,1),Coroot(R,i)) in {-2,0,2}]>;
ALGMa := SubalgebraModule(La,ALGM);
Ra := RootDatum(La);
*/

print "Finished: ",Cputime(t);

/*
print "STEP 5: ",Cputime(t);
k := &+[1 : r in roots | (r,coroots[1]) in {1,-1}]/2;
unit := (6+k)/8*em[1](getVec(Jmat!IdentityMatrix(F,n)));

JtoZ := hom<J -> Z | [4*Z![BS(emJ(j),emJ(J.i)) : i in [1..e]] : j in Basis(J)]>;

unitA := proj[1](unit);

axis := [em[1](isomAJ(emJ(J.i) + emZ(JtoZ(J.i)))) : i in [1..e]];
Eigenvalues(adjoint(axis[1]));

axisA := [isomAJ(emJ(J.i) + emZ(JtoZ(J.i))) : i in [1..e]];
AD := Matrix([MA(axisA[1],j) : j in Basis(J)]);
Eigenvalues(AD);

AD2 := Matrix([MA(J.1,j) : j in Basis(J)]);
Eigenvalues(ChangeRing(AD2,AlgebraicClosure()));

MJ := function(x,y)
  xmat := getMat(x);
  ymat := getMat(y);
  return getVec(1/2*(xmat*ymat
     + ymat*xmat));
end function;
*/
