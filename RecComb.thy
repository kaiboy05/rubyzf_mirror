theory RecComb
imports SimpComb
begin

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

theorem powf_type: "\<lbrakk> n:nat; R:nat\<rightarrow>A<~>A \<rbrakk> \<Longrightarrow> powf(A,n,R):A<~>A"
apply(unfold powf_def)
apply(induct_tac n)
apply(simp, rule PowD, typecheck)
apply(subst rec_succ, typecheck)
done

theorem powfR: "\<lbrakk> A:ChTy; n:nat; R:nat\<rightarrow>A<R>A \<rbrakk> \<Longrightarrow> powf(A,n,R):A<R>A"
apply(unfold powf_def)
apply(induct_tac n)
apply(simp, rule IdR, simp)
apply(simp, intro RubyR, simp+)
done

theorem powf_zero: "a:sig(A) \<Longrightarrow> <a,a>:powf(A,0,R)"
apply(unfold powf_def)
apply(simp)
apply(rule IdI, simp)
done

theorem powf_zero_iff: "powf(A,0,R) = Id(A)"
apply(unfold powf_def, simp)
done

theorem powf_succ: "powf(A, succ(n), R) = powf(A,n,R) ;; R`n"
apply(unfold powf_def, simp)
done

theorem powfI: "x:powf(A,n,R) ;; R`n \<Longrightarrow> x:powf(A,succ(n),R)"
apply(unfold powf_def, simp)
done

theorem powfE: "\<lbrakk> x:powf(A,succ(n),R); \<lbrakk> x:powf(A,n,R) ;; R`n \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(subst (asm) powf_succ, simp)
done

theorem mapf'_type: "\<lbrakk> n:nat; Rf:nat\<rightarrow>A<~>B \<rbrakk> \<Longrightarrow> mapf'(A,B,n,Rf):nlist[n]A<~>nlist[n]B"
apply(unfold mapf'_def)
apply(induct_tac n)
apply(simp, rule PowD, typecheck)
apply(simp, rule PowD, typecheck)
apply(simp)
done

lemma nat_dtyp_rtyp_fun: "R:nat\<rightarrow>A<~>B \<Longrightarrow> R:nat\<rightarrow>dtyp(Union(range(R)))<~>rtyp(Union(range(R)))"
apply(rule Pi_type, simp)
apply(rule dtyp_rtyp_fun, simp_all)
done

theorem mapf_type: "\<lbrakk> n:nat; Rf:nat\<rightarrow>A<~>B \<rbrakk> \<Longrightarrow> mapf(n,Rf):nlist[n]A<~>nlist[n]B"
apply(unfold mapf_def)
apply(frule nat_dtyp_rtyp_fun)
apply(frule mapf'_type, simp) back
apply(subgoal_tac "nlist[n]dtyp(\<Union>range(Rf))<~>nlist[n]rtyp(\<Union>range(Rf)) \<subseteq> nlist[n]A<~>nlist[n]B")
apply(blast)
apply(auto, drule subsetD, simp,  auto)
apply(rule nlist_dtypUR, auto)
apply(rule nlist_rtypUR, auto)
done

theorem mapf_rtyp_sigUR: 
  "\<lbrakk> <la, lb>:mapf(n,R); R:nat\<rightarrow>A<~>B; n:nat \<rbrakk>
    \<Longrightarrow> lb:sig(nlist[n]rtyp(Union(range(R))))"
apply(frule nat_dtyp_rtyp_fun)
apply(frule mapf_type[of n R "dtyp(Union(range(R)))" "rtyp(Union(range(R)))"], simp)
apply(blast)
done

theorem mapf_dtyp_sigUR: 
  "\<lbrakk> <la, lb>:mapf(n,R); R:nat\<rightarrow>A<~>B; n:nat \<rbrakk>
    \<Longrightarrow> la:sig(nlist[n]dtyp(Union(range(R))))"
apply(frule nat_dtyp_rtyp_fun)
apply(frule mapf_type[of n R "dtyp(Union(range(R)))" "rtyp(Union(range(R)))"], simp)
apply(blast)
done

theorem mapf_zero: "<snil, snil>:mapf(0, Rf)"
apply(unfold mapf_def mapf'_def)
apply(simp)
apply(rule NNILI)
done

theorem mapf_zero_ifft: "mapf(0, Rf) = NNIL"
apply(unfold mapf_def mapf'_def)
apply(simp)
done

theorem mapf'_zero_ifft: "mapf'(A,B,0, Rf) = NNIL"
apply(unfold mapf'_def)
apply(simp)
done

theorem mapf_succ_ifft:
  "mapf(succ(n), Rf) =
    (apr(dtyp(Union(range(Rf))), n)~);;[[mapf(n,Rf), Rf`n]];;
    apr(rtyp(Union(range(Rf))), n)"
apply(unfold mapf_def mapf'_def)
apply(simp)
done

theorem mapf_succ:
  "\<lbrakk> n:nat; Rf:nat\<rightarrow>A<~>B; a:sig(A); b:sig(B);
    la:sig(nlist[n]A); lb:sig(nlist[n]B) \<rbrakk>
    \<Longrightarrow> <[la<@a|n], [lb<@b|n]>:mapf(succ(n), Rf)
        \<longleftrightarrow> (<a,b>:Rf`n & <la, lb>:mapf(n, Rf))"
apply(subst mapf_succ_ifft)
apply(auto)
apply((drule nat_dtyp_rtyp_fun,
      elim compE, typecheck add: mapf_type,
      elim sig_pairE, simp,
      elim invE, typecheck,
      elim RubyE, simp_all)+)
apply(intro RubyI)
apply(subgoal_tac "<<la#a>, [la<@a|n]>:apr(dtyp(\<Union>range(Rf)), n)", simp)
apply(rule aprI)
apply(rule dtyp_sigUR, simp_all)
apply(rule mapf_dtyp_sigUR, simp_all)
apply(subgoal_tac "<<la#a>, <lb#b>>:[[mapf(n, Rf),Rf ` n]]", simp)
apply(intro RubyI, simp_all)
apply(intro RubyI)
apply(rule rtyp_sigUR, simp_all)
apply(rule mapf_rtyp_sigUR, simp_all)
done

lemma mapf'_succ_ifft:
  "mapf'(A,B,succ(n), Rf) =
    (apr(A, n)~);;[[mapf'(A,B,n,Rf), Rf`n]];;apr(B, n)"
apply(unfold mapf'_def, simp)
done

theorem mapf'_succ:
  "\<lbrakk> n:nat; Rf:nat\<rightarrow>A<~>B; a:sig(A); b:sig(B);
    la:sig(nlist[n]A); lb:sig(nlist[n]B) \<rbrakk>
    \<Longrightarrow> <[la<@a|n], [lb<@b|n]>:mapf'(A,B,succ(n),Rf)
        \<longleftrightarrow> (<a,b>:Rf`n & <la, lb>:mapf'(A,B,n,Rf))"
apply(subst mapf'_succ_ifft)
apply(auto)
apply((elim compE, typecheck add: mapf'_type,
      elim sig_pairE, simp,
      elim invE, typecheck,
      elim RubyE, simp_all)+)
apply(intro RubyI)
apply(subgoal_tac "<<la#a>, [la<@a|n]>:apr(A, n)", simp)
apply(rule aprI, simp_all)
apply(subgoal_tac "<<la#a>, <lb#b>>:[[mapf'(A,B,n, Rf),Rf ` n]]", simp)
apply(intro RubyI, simp_all)
apply(intro RubyI, simp_all)
done

theorem mapf_mapf'_iff: 
  "\<lbrakk> n:nat; R:nat\<rightarrow>A<~>B \<rbrakk> \<Longrightarrow> mapf(n,R) = mapf'(A,B,n,R)"
apply(induct_tac n)
apply(subst mapf'_zero_ifft, subst mapf_zero_ifft, simp)
apply(rule, auto)
apply(frule mapf_type[of "succ(_)", OF nat_succI], simp+)
apply(drule subsetD, simp, safe)
apply(elim sig_ssnocE, simp)
apply(subst (asm) mapf_succ, simp_all)
apply(erule conjE)
apply(subst mapf'_succ, simp_all)
apply(frule mapf'_type[of "succ(_)", OF nat_succI], simp+)
apply(drule subsetD, simp, safe)
apply(elim sig_ssnocE, simp)
apply(subst (asm) mapf'_succ, simp_all)
apply(erule conjE)
apply(subst mapf_succ, simp_all)
done

theorem mapf_zero_iff: "mapf(0,R) = NNIL"
apply(rule mapf_zero_ifft)
done

theorem mapf_zero_iff2: "R:nat\<rightarrow>A<~>B \<Longrightarrow> mapf(0,R) = NNIL"
apply(rule mapf_zero_ifft)
done

theorem mapf_succ_iff: 
  "\<lbrakk> n:nat; R:nat\<rightarrow>A<~>B \<rbrakk> 
  \<Longrightarrow> mapf(succ(n),R) = (apr(A,n)~);;[[mapf(n,R), R`n]];;apr(B,n)"
apply((subst mapf_mapf'_iff, simp_all)+)
apply(unfold mapf'_def, simp)
done

theorem mapf_succE: 
  "\<lbrakk> <[la<@a|n], [lb<@b|n]>:mapf(succ(n), Rf);
    \<lbrakk> <a,b>:Rf`n; <la,lb>:mapf(n,Rf) \<rbrakk> \<Longrightarrow> P;
    n:nat; Rf:nat\<rightarrow>A<~>B; a:sig(A); b:sig(B);
    la:sig(nlist[n]A); lb:sig(nlist[n]B) \<rbrakk> \<Longrightarrow> P"
apply(subst (asm) mapf_succ, simp_all)
done

theorem mapfR: 
  "\<lbrakk> A:ChTy; B:ChTy; n:nat; Rf:nat\<rightarrow>A<R>B \<rbrakk>
    \<Longrightarrow> mapf(n,Rf):nlist[n]A<R>nlist[n]B"
apply(induct_tac n)
apply(subst mapf_zero_iff)
apply(intro RubyR, simp+)
apply(subst mapf_succ_iff, simp)
apply(rule fun_weaken_type[OF _ ruby_sub_sig], simp)
apply(intro RubyR)
apply(rule aprR, simp)
apply(rule parR, simp, simp)
apply(rule aprR, simp)
done

theorem tri_type: "\<lbrakk> n:nat; R:A<~>A \<rbrakk> \<Longrightarrow> tri(A,n,R):nlist[n]A<~>nlist[n]A"
apply(unfold tri_def)
apply(typecheck add: mapf_type powf_type)
done

theorem tri_zero: "<snil, snil>: tri(A,0,R)"
apply(unfold tri_def)
apply(rule mapf_zero)
done

theorem tri_zero_iff: "tri(A,0,Rf) = NNIL"
apply(unfold tri_def)
apply(rule mapf_zero_iff)
done

theorem tri_succ_iff:
  "\<lbrakk> n:nat; R:A<~>A \<rbrakk>
    \<Longrightarrow> tri(A, succ(n), R) = 
    (apr(A,n)~);;[[tri(A,n,R), pow(A,n,R)]];;apr(A,n)"
apply(unfold tri_def)
apply(subst mapf_succ_iff, simp)
apply(typecheck add: powf_type)
apply(simp)
done

theorem tri_succ:
  "\<lbrakk> n:nat; R:A<~>A; a:sig(A); b:sig(A);
    la:sig(nlist[n]A); lb:sig(nlist[n]A) \<rbrakk> \<Longrightarrow>
    <[la<@a|n], [lb<@b|n]>:tri(A, succ(n), R) \<longleftrightarrow>
    (<a,b>:pow(A,n,R) & <la,lb>:tri(A,n,R))"
apply(unfold tri_def)
apply(subst mapf_succ, typecheck add: powf_type, simp_all)
done

theorem tri_succE:
  "\<lbrakk> <[la<@a|n], [lb<@b|n]>:tri(A, succ(n), R);
    \<lbrakk> <a,b>:pow(A,n,R); <la,lb>:tri(A,n,R) \<rbrakk> \<Longrightarrow> P;
    n:nat; R:A<~>A; a:sig(A); b:sig(A);
    la:sig(nlist[n]A); lb:sig(nlist[n]A) \<rbrakk> \<Longrightarrow> P"
apply(subst (asm) tri_succ, simp_all)
done

theorem colf'_type: 
  "\<lbrakk> n:nat; Rf:nat\<rightarrow>A*B<~>B*C \<rbrakk>
    \<Longrightarrow> colf'(A,B,C,n,Rf):nlist[n]A*B<~>B*nlist[n]C"
apply(unfold colf'_def)
apply(induct_tac n)
apply(simp, rule PowD, typecheck)
apply(simp, rule PowD)
apply(typecheck, simp)
done

theorem colf_type:
  "\<lbrakk> n:nat; Rf:nat\<rightarrow>A*B<~>B*C \<rbrakk> \<Longrightarrow>
    colf(B,n,Rf):nlist[n]A*B<~>B*nlist[n]C"
apply(unfold colf_def)
oops





thm range_type
find_theorems "dtyp(Union(range(_)))"
find_theorems "_:_\<rightarrow>_" "_\<subseteq>_"

end