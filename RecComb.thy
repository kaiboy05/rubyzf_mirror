theory RecComb
imports SimpComb
begin

consts
  pow :: "[i,i,i] \<Rightarrow> i"

definition powf :: "[i,i,i] \<Rightarrow> i" where
  "powf(A,n,R) == rec(n, Id(A), %x y. y ;; R`x)"

definition mapf' :: "[i,i,i,i] \<Rightarrow> i" where
  "mapf'(A,B,n,R) == rec(n, NNIL, %x y.(apr(A,x)~);;[[y,R`x]];;apr(B,x))"

definition mapf :: "[i,i] \<Rightarrow> i" where
  "mapf(n,R) == mapf'(dtyp(Union(range(R))), rtyp(Union(range(R))), n, R)"

definition tri :: "[i,i,i] \<Rightarrow> i" where
  "tri(A,n,R) == mapf(n, lam i:nat. pow(A,i,R))"

definition colf' :: "[i,i,i,i,i] \<Rightarrow> i" where
  "colf'(A,B,C,n,R) ==
    rec(n, Fst(B,NNIL) ;; cross(nlist[0]C, B),
    %x y. Fst(B,apr(A,x)~) ;; (y || (R`x)) ;; Snd(B,apr(C,x)))"

definition colf :: "[i,i,i] \<Rightarrow> i" where
  "colf(B,n,R) == colf'(ddtyp(Union(range(R))), B, rrtyp(Union(range(R))), n, R)"

definition rowf :: "[i,i,i] \<Rightarrow> i" where
  "rowf(B,n,R) == (colf(B,n,lam m:nat. ((R`m)~)))~"

syntax
  "pow" :: "[i,i,i] \<Rightarrow> i" ("(pow'(_,/ _,/ _'))" [75] 75)
  "col" :: "[i,i,i] \<Rightarrow> i" ("(col'(_,/ _,/ _'))" [75] 75)
  "row" :: "[i,i,i] \<Rightarrow> i" ("(row'(_,/ _,/ _'))" [75] 75)
  "Map" :: "[i,i] \<Rightarrow> i" ("(Map'(_,/ _'))" [75] 75)

  "powf" :: "[i,i,i] \<Rightarrow> i"
  "colf" :: "[i,i,i] \<Rightarrow> i"
  "rowf" :: "[i,i,i] \<Rightarrow> i"
  "mapf" :: "[i,i] \<Rightarrow> i"

  "Lambda" :: "[i,i] \<Rightarrow> i"
  "nat" :: "i"
translations
  "pow(A,n,R)" => "powf(A, n, Lambda(nat, %_. R))"
  "col(A,n,R)" => "colf(A, n, Lambda(nat, %_. R))"
  "row(A,n,R)" => "rowf(A, n, Lambda(nat, %_. R))"
  "Map(n,R)" => "mapf(n, Lambda(nat, %_. R))"

end