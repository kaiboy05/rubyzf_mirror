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

theorem dtypUR: "\<lbrakk> x:sig(dtyp(Union(range(R)))); R:nat\<rightarrow>A<~>B \<rbrakk> \<Longrightarrow> x:sig(A)"
apply(rule dtyp_rel[of "Union(range(R))"], simp_all)
apply(auto, drule range_type, blast+)
done

theorem rtypUR: "\<lbrakk> x:sig(rtyp(Union(range(R)))); R:nat\<rightarrow>B<~>A \<rbrakk> \<Longrightarrow> x:sig(A)"
apply(rule rtyp_rel[of "Union(range(R))"], simp_all)
apply(auto, drule range_type, blast+)
done

theorem dtyp_sigUR: 
  "\<lbrakk> <x,y>:R`n; R:nat\<rightarrow>A<~>B; n:nat; x:sig(A) \<rbrakk>
    \<Longrightarrow> x:sig(dtyp(Union(range(R))))"
apply(rule dtyp_sig)
apply(frule apply_rangeI, simp, blast+)
done

theorem rtyp_sigUR:
  "\<lbrakk> <x,y>:R`n; R:nat\<rightarrow>A<~>B; n:nat; y:sig(B) \<rbrakk>
    \<Longrightarrow> y:sig(rtyp(Union(range(R))))"
apply(rule rtyp_sig)
apply(frule apply_rangeI, simp, blast+)
done

theorem dtyp_rtyp_fun: 
  "\<lbrakk> R:nat\<rightarrow>A<~>B; m:nat \<rbrakk>
    \<Longrightarrow> R`m:(dtyp(Union(range(R))))<~>(rtyp(Union(range(R))))"
apply(auto)
apply(frule apply_funtype, auto)
apply(drule subsetD, auto)
apply(rule dtyp_sigUR, simp_all)
apply(rule rtyp_sigUR, simp_all)
done

theorem nlist_dtypUR: 
  "\<lbrakk> x:sig(nlist[n]dtyp(Union(range(R)))); R:nat\<rightarrow>A<~>B \<rbrakk>
    \<Longrightarrow> x:sig(nlist[n]A)"
apply(rule sig_sub_func, simp)
apply(drule apply_funtype, simp)
apply(subgoal_tac "dtyp(Union(range(R))) \<subseteq> A", drule nlist_mono[of _ _n], blast)
apply(auto simp add: dtyp_def)
apply(drule range_type, simp)
apply(drule PowD, drule subsetD, simp)
apply(auto, drule range_type, simp+)
done

theorem nlist_rtypUR: 
  "\<lbrakk> x:sig(nlist[n]rtyp(Union(range(R)))); R:nat\<rightarrow>A<~>B \<rbrakk>
    \<Longrightarrow> x:sig(nlist[n]B)"
apply(rule sig_sub_func, simp)
apply(drule apply_funtype, simp)
apply(subgoal_tac "rtyp(Union(range(R))) \<subseteq> B", drule nlist_mono[of _ _n], blast)
apply(auto simp add: rtyp_def)
apply(drule range_type, simp)
apply(drule PowD, drule subsetD, simp)
apply(auto, drule range_type, simp+)
done

theorem nlist_ddtypUR: 
  "\<lbrakk> a:sig(nlist[n]ddtyp(Union(range(Rf)))); Rf:nat \<rightarrow> A*B<~>B1*C \<rbrakk>
    \<Longrightarrow> a:sig(nlist[n]A)"
apply(rule sig_sub_func, simp)
apply(drule apply_funtype, simp)
apply(subgoal_tac "ddtyp(Union(range(Rf))) \<subseteq> A", drule nlist_mono[of _ _n], blast)
apply(auto simp add: dtyp_def ddtyp_def)
apply(drule range_type[of _ _ Rf], simp)
apply(drule PowD, drule subsetD, simp, auto)
apply(drule range_type, simp, blast)
done

theorem nlist_rrtypUR: 
  "\<lbrakk> a:sig(nlist[n]rrtyp(Union(range(Rf)))); Rf:nat \<rightarrow> A*B<~>B1*C \<rbrakk>
    \<Longrightarrow> a:sig(nlist[n]C)"
apply(rule sig_sub_func, simp)
apply(drule apply_funtype, simp)
apply(subgoal_tac "rrtyp(Union(range(Rf))) \<subseteq> C", drule nlist_mono[of _ _n], blast)
apply(auto simp add: rtyp_def rrtyp_def)
apply(drule range_type[of _ _ Rf], simp)
apply(drule PowD, drule subsetD, simp, auto)
apply(drule range_type, simp, blast)
done

theorem rdtypUR: 
  "\<lbrakk> b:sig(rdtyp(Union(range(Rf)))); Rf:nat\<rightarrow>A*B<~>B1*C \<rbrakk>
    \<Longrightarrow> b:sig(B)"
apply(rule sig_sub_func, simp)
apply(drule apply_funtype, simp)
apply(subgoal_tac "rdtyp(Union(range(Rf))) \<subseteq> B", blast)
apply(auto simp add: dtyp_def rdtyp_def)
apply(drule range_type[of _ _ Rf], simp) back
apply(drule PowD, drule subsetD, simp, auto)
apply(drule range_type, simp) back
apply(blast)
done




thm range_type
find_theorems "_:_\<rightarrow>_" "<_,_>:_"

end