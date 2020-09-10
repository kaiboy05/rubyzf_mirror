theory RubyEquality
imports RecComb
begin

lemma comp_right_eq: "A = B \<Longrightarrow> A;;C = B;;C"
apply(auto)
done

lemma comp_left_eq: "A = B \<Longrightarrow> C;;A = C;;B"
apply(auto)
done

lemmas comp_eq = comp_right_eq comp_left_eq

lemma beside_right_eq: "A = B \<Longrightarrow> A || C = B || C"
apply(auto)
done

lemma beside_left_eq: "A = B \<Longrightarrow> C || A = C || B"
apply(auto)
done

lemmas beside_eq = beside_right_eq beside_left_eq

theorem comp_assoc: "\<lbrakk> R:A<~>B; S:B<~>C; T:C<~>D \<rbrakk> \<Longrightarrow> (R;;S);;T = R;;(S;;T)"
apply(rule, auto)
apply(subgoal_tac "R ;; S ;; T : A<~>D", typecheck, simp_all)
apply(drule subsetD, simp, safe)
apply(elim compE, typecheck, simp_all)
apply(intro RubyI, simp_all)
apply(subgoal_tac "R ;; (S ;; T) : A<~>D", typecheck, simp_all)
apply(drule subsetD, simp, safe)
apply(elim compE, typecheck, simp_all)
apply(intro RubyI, simp_all)
done

theorem Id_left[simp]: "R:A<~>B \<Longrightarrow> Id(A) ;; R = R"
apply(rule, auto)
apply(subgoal_tac "Id(A) ;; R : A<~>B", typecheck)
apply(simp, drule subsetD, simp, safe)
apply(erule compE, typecheck, simp)
apply(elim RubyE, simp, blast)
apply(drule subsetD, simp, safe)
apply(intro RubyI)
defer
apply(simp, rule IdI, simp)
done

theorem Id_right[simp]: "R:B<~>A \<Longrightarrow> R ;; Id(A) = R"
apply(rule, auto)
apply(subgoal_tac "R ;; Id(A) : B<~>A", typecheck)
apply(simp, drule subsetD, simp, safe)
apply(erule compE, typecheck, simp)
apply(elim RubyE, simp, blast)
apply(drule subsetD, simp, safe)
apply(intro RubyI, simp, rule IdI, simp)
done

theorem Id_inv: "Id(A)~ = Id(A)"
apply(rule, auto)
apply(subgoal_tac "Id(A)~ : A<~>A", typecheck)
apply(simp, drule subsetD, simp, safe)
apply(elim RubyE, typecheck, simp, rule IdI, simp)
apply(insert Id_type[of A], simp, drule subsetD, simp, safe)
apply(elim RubyE, simp, intro RubyI, simp+)
done

theorem powf_succ2: "\<lbrakk> n:nat; R:A<~>A \<rbrakk> \<Longrightarrow> pow(A,succ(n), R) = R ;; pow(A,n,R)"
apply(induct_tac n)
apply(subst powf_succ)
apply((subst powf_zero_iff)+)
apply(simp)
apply(subst powf_succ, simp)
apply(subst (asm) powf_succ, simp)
apply(subst comp_assoc, simp_all)
apply(rule PowD, rule powf_type, simp, typecheck, simp)
done

lemma pow_disturb_lemma:
  "\<lbrakk> Q:A<~>A; R:A<~>A; n:nat; Q;;R = R;;Q \<rbrakk> 
  \<Longrightarrow> Q ;; pow(A,n,R) = pow(A,n,R) ;; Q"
apply(induct_tac n)
apply(simp add: powf_zero_iff)
apply(subst powf_succ, simp)
apply(subst comp_assoc[THEN sym])
apply(typecheck, simp+)
apply(subst comp_assoc, typecheck, simp+)
apply(subst comp_assoc[THEN sym], typecheck, simp+)
apply(subst powf_succ, simp)
done

theorem pow_distrib:
  "\<lbrakk> Q:A<~>A; R:A<~>A; n:nat; Q;;R = R;;Q \<rbrakk> 
  \<Longrightarrow> pow(A,n,Q) ;; pow(A,n,R) = pow(A,n,(Q;;R))"
apply(induct_tac n)
apply((subst powf_zero_iff)+)
apply(rule Id_left, typecheck)
apply(subst powf_succ, simp)
apply(subst comp_assoc, typecheck, simp+)
apply(subst powf_succ, simp)
apply(subst comp_assoc[of Q _ _ "powf(A, _, \<lambda>_\<in>nat. R)" _ R, THEN sym])
apply(typecheck, simp+)
apply(subst pow_disturb_lemma, simp_all)
apply(subst comp_assoc[THEN sym])
apply(typecheck, simp+)
apply(subst comp_assoc[THEN sym])
apply(typecheck, simp+)
apply(subst comp_assoc)
apply(typecheck, simp+)
apply(subst powf_succ, simp)
done

theorem compinv: "\<lbrakk> R:A<~>B; S:B<~>C \<rbrakk> \<Longrightarrow> (R ;; S)~ = S~ ;; R~"
apply(rule, rule)
apply(subgoal_tac "(R;;S)~ : C<~>A", typecheck)
apply(simp, drule subsetD, simp, safe)
apply(elim RubyE, typecheck, simp+)
apply(intro RubyI, typecheck)
apply(subgoal_tac "S~ ;; R~ : C<~>A", typecheck, simp_all)
apply(drule subsetD, simp+, safe)
apply(elim RubyE, typecheck, simp+)
apply(intro RubyI, simp+)
done

theorem invinv[simp]: "R:A<~>B \<Longrightarrow> (R~)~ = R"
apply(rule, auto)
apply(subgoal_tac "R~~ : A<~>B", typecheck, simp_all)
apply(drule subsetD, simp, safe)
apply(elim RubyE, typecheck, simp_all)
apply(drule subsetD, simp, safe)
apply(intro RubyI, simp_all)
done

theorem Id_comp_left: "R:A<~>B \<Longrightarrow> Id(A) ;; R = R"
apply(simp)
done

theorem NNILinv: "NNIL~ = NNIL"
apply(rule, auto)
apply(insert NNIL_type[of A B])
apply(drule inv_type[of NNIL], simp)
apply(drule subsetD, simp, safe)
apply(elim RubyE, typecheck, simp+)
apply(intro RubyI)
apply(drule subsetD, simp, safe)
apply(elim RubyE, simp+)
apply(intro RubyI, simp+)
done

theorem crossover:
  "\<lbrakk> R:A<~>B; S:C<~>D \<rbrakk> \<Longrightarrow> 
    [[R,S]] ;; cross(B,D) = cross(A,C) ;; [[S,R]]"
apply(rule, auto)
apply(subgoal_tac "[[R,S]];;cross(B,D) : A*C<~>D*B", typecheck, simp_all)
apply(drule subsetD, simp, safe)
apply(elim sig_pairE, simp)
apply(elim compE, typecheck, simp_all)
apply(elim sig_pairE, simp, elim RubyE, simp_all)
apply(intro RubyI, rule crossI, simp+)
apply(intro RubyI, simp_all)
apply(subgoal_tac "cross(A,C) ;; [[S,R]] : A*C<~>D*B", typecheck, simp_all)
apply(drule subsetD, simp, safe)
apply(elim sig_pairE, simp)
apply(elim compE, typecheck, simp_all)
apply(elim sig_pairE, simp, elim RubyE, simp_all)
apply(intro RubyI)
defer
apply(rule crossI, simp_all)
apply(rule parI, simp_all)
done

theorem fstsndpar[simp]: "\<lbrakk> R:A<~>B; S:C<~>D \<rbrakk> \<Longrightarrow> Fst(C,R) ;; Snd(B,S) = [[R,S]]"
apply(rule, safe)
apply(subgoal_tac "Fst(C,R);;Snd(B,S):A*C<~>B*D", typecheck, simp_all)
apply(drule subsetD, simp, safe, elim sig_pairE, simp)
apply(elim compE, typecheck, simp_all)
apply(elim sig_pairE, simp, elim RubyE, simp+)
apply(intro RubyI, simp_all)
apply(insert par_type[of R A B S C D], simp)
apply(drule subsetD, simp, safe, elim sig_pairE, simp)
apply(elim RubyE, simp_all)
apply(intro RubyI, rule parI, simp, rule IdI, simp_all)
apply(intro RubyI, simp+)
done

theorem par_inv_distrib: "\<lbrakk> R:A<~>B; S:C<~>D \<rbrakk> \<Longrightarrow> [[R,S]]~ = [[R~,S~]]"
apply(rule, auto)
apply(subgoal_tac "[[R,S]]~ : B*D<~>A*C", typecheck, simp_all)
apply(drule subsetD, simp)
apply(safe, elim sig_pairE, simp)
apply(elim RubyE, typecheck, simp_all)
apply(intro RubyI, simp_all)
apply(subgoal_tac "[[R~,S~]] : B*D<~>A*C", typecheck, simp_all)
apply(drule subsetD, simp)
apply(safe, elim sig_pairE, simp)
apply(elim RubyE, typecheck, simp_all)
apply(intro RubyI, simp_all)
done

theorem par_comb: 
  "\<lbrakk> R:A<~>B; S:B<~>C; T:D<~>E; U:E<~>F \<rbrakk> 
    \<Longrightarrow> [[R,T]] ;; [[S,U]] = [[R;;S, T;;U]]"
apply(rule, auto)
apply(subgoal_tac "[[R,T]] ;; [[S,U]] : A*D<~>C*F", typecheck, simp_all)
apply(drule subsetD, simp)
apply(safe, elim sig_pairE, simp)
apply(elim compE, typecheck, simp_all)
apply(elim sig_pairE, simp)
apply(elim RubyE, simp_all)
apply(intro RubyI, simp_all)
apply(subgoal_tac "[[R;;S,T;;U]] : A*D<~>C*F", typecheck, simp_all)
apply(drule subsetD, simp)
apply(safe, elim sig_pairE, simp)
apply(elim RubyE, simp_all)
apply(intro RubyI)
apply(subgoal_tac "\<langle><a#b>, <ya#yb>\<rangle> \<in> [[R,T]]", simp)
apply((intro RubyI, simp_all)+)
done

lemma B_not_zero: "B \<noteq> 0 \<Longrightarrow> sig(B) \<noteq> 0"
apply(blast)
done

theorem p1id: "B \<noteq> 0 \<Longrightarrow> p1(A,B)~ ;; p1(A,B) = Id(A)"
apply(rule, auto)
apply(subgoal_tac "p1(A,B)~ ;; p1(A,B) : A<~>A", typecheck)
apply(simp, drule subsetD, simp, safe)
apply(elim RubyE, typecheck, simp)
apply(elim sig_pairE, simp, elim RubyE, simp_all)
apply(intro RubyI, simp)
apply(insert Id_type[of A], simp)
apply(drule subsetD, simp, safe)
apply(elim RubyE, simp)
apply(drule B_not_zero)
apply(drule Choose_def)
apply(intro RubyI)
apply(rule p1I, simp+)
apply(rule p1I, simp+)
done

theorem comp_inv: "\<lbrakk> R:A<~>B; S:B<~>C \<rbrakk> \<Longrightarrow> (R;;S)~ = S~;;R~"
apply(rule, auto)
apply(subgoal_tac "(R ;; S)~ : C<~>A", typecheck)
apply(simp, drule subsetD, simp, simp_all, safe)
apply(elim RubyE, typecheck, simp+)
apply(intro RubyI, simp+)
apply(subgoal_tac "S~ ;; R~ : C<~>A", typecheck)
apply(simp, drule subsetD, simp, simp_all, safe)
apply(elim RubyE, typecheck, simp+)
apply(intro RubyI, simp+)
done

theorem par_Id: "[[Id(A), Id(B)]] = Id(A*B)"
apply(rule, auto)
apply(subgoal_tac "[[Id(A), Id(B)]] : _<~>_", typecheck)
apply(simp, drule subsetD, simp)
apply(safe, elim sig_pairE, simp)
apply(elim RubyE, typecheck, simp+)
apply(intro RubyI, simp)
apply(subgoal_tac "Id(A*B):_<~>_", typecheck)
apply(simp, drule subsetD, simp)
apply(safe, elim sig_pairE, simp+)
apply(elim RubyE, typecheck, simp+)
apply(intro RubyI, simp+)
done

theorem apr_apr_inv_Id: "apr(A,x) ;; apr(A,x)~ = Id(nlist[x]A \<times> A)"
apply(rule, auto)
apply(subgoal_tac "apr(A,x);;apr(A,x)~ : _<~>_", typecheck)
apply(simp, drule subsetD, simp, safe, elim sig_pairE, simp)
apply(elim compE, typecheck, elim sig_ssnocE, simp)
apply(elim aprE, simp+)
apply(elim RubyE, typecheck, simp, intro IdI, simp)
apply(subgoal_tac "Id(nlist[x]A*A):_<~>_", typecheck)
apply(simp, drule subsetD, simp, safe, elim sig_pairE, simp)
apply(elim RubyE, simp+)
apply(intro RubyI, simp+)
apply((rule aprI, simp+)+)
done

theorem reorg_reorg_inv_Id: "reorg(A,B,C) ;; reorg(A,B,C)~ = Id((A*B)*C)"
apply(rule, auto)
apply(subgoal_tac "reorg(A,B,C) ;; reorg(A,B,C)~ : _<~>_", typecheck)
apply(simp, drule subsetD, simp, safe, elim sig_pairE, simp)
apply(elim compE, typecheck, elim sig_pairE, simp)
apply(elim RubyE, typecheck, simp)
apply(intro IdI, simp)
apply(subgoal_tac "Id((A*B)*C):_<~>_", typecheck)
apply(simp, drule subsetD, simp, safe, elim sig_pairE, simp)
apply(elim RubyE, simp+)
apply(intro RubyI, simp+)
apply((rule reorgI, simp+)+)
done

theorem reorg_reorg_inv_Id2: "reorg(A,B,C)~ ;; reorg(A,B,C) = Id(A*B*C)"
apply(rule, auto)
apply(subgoal_tac "reorg(A,B,C)~ ;; reorg(A,B,C) : _<~>_", typecheck)
apply(simp, drule subsetD, simp, safe, elim sig_pairE, simp)
apply(elim compE, typecheck, elim sig_pairE, simp)
apply(elim RubyE, typecheck, simp)
apply(intro IdI, simp)
apply(subgoal_tac "Id(A*B*C):_<~>_", typecheck)
apply(simp, drule subsetD, simp, safe, elim sig_pairE, simp)
apply(elim RubyE, simp+)
apply(intro RubyI, simp+)
apply((rule reorgI, simp+)+)
done

theorem Fst_par_comp: "\<lbrakk> R:C<~>D; S:D<~>E; T:A<~>B \<rbrakk> \<Longrightarrow> Fst(A,R);;[[S,T]] = [[R;;S,T]]"
apply(subst Id_left[of T A B, THEN sym], simp) back
apply(subst par_comb[THEN sym], typecheck)
apply(intro comp_eq)
apply(subst Fst_def, simp)
done

theorem Snd_par_comp: "\<lbrakk> R:C<~>D; S:D<~>E; T:A<~>B \<rbrakk> \<Longrightarrow> Snd(A,R);;[[T,S]] = [[T,R;;S]]"
apply(subst Id_left[of T A B, THEN sym], simp) back
apply(subst par_comb[THEN sym], typecheck)
apply(intro comp_eq)
apply(subst Snd_def, simp)
done

theorem par_reorg_assoc: 
  "\<lbrakk> R:A<~>B; S:C<~>D; T:E<~>F \<rbrakk> 
    \<Longrightarrow> [[R,[[S,T]]]] = reorg(A,C,E)~ ;; [[[[R,S]],T]] ;; reorg(B,D,F)"
apply(rule, auto)
apply(subgoal_tac "[[R,[[S,T]]]] : _<~>_", typecheck, simp_all)
apply(drule subsetD, simp, safe, elim sig_pairE, simp)
apply(elim RubyE, typecheck)
apply(intro RubyI)
apply(rule reorgI, simp+)
apply(subgoal_tac "<<<a#ab>#bb>, <<aa#ac>#bc>> : [[[[R,S]],T]]", simp)
apply(intro RubyI, simp+)
apply(rule reorgI, simp+)
apply(subgoal_tac "reorg(A, C, E)~ ;; [[[[R,S]],T]] ;; reorg(B, D, F) : _<~>_", typecheck, simp_all)
apply(drule subsetD, simp, safe, elim sig_pairE, simp)
apply(elim compE, typecheck, simp_all)
apply(elim sig_pairE, simp)
apply(elim RubyE, typecheck, simp)
apply(intro RubyI, simp+)
done

theorem par_reorg_assoc2: 
  "\<lbrakk> R:A<~>B; S:C<~>D; T:E<~>F \<rbrakk> 
    \<Longrightarrow> [[[[R,S]],T]] = reorg(A,C,E) ;; [[R,[[S,T]]]] ;; reorg(B,D,F)~"
apply(subst par_reorg_assoc, simp_all)
apply((subst comp_assoc, typecheck, simp+)+)
apply(subst reorg_reorg_inv_Id)
apply(subst Id_right, typecheck, simp_all)
apply((subst comp_assoc[THEN sym], typecheck, simp+)+)
apply(subst reorg_reorg_inv_Id)
apply(subst Id_left, typecheck, simp_all)
done

theorem Fst_distrib: "\<lbrakk> R:A<~>B; S:B<~>C \<rbrakk> \<Longrightarrow> Fst(D, R;;S) = Fst(D,R) ;; Fst(D,S)"
apply((subst Fst_def)+)
apply(subst par_comb, typecheck)
apply(subst Id_left, typecheck, simp)
done

theorem comp_p1_inv: "R:A<~>A \<Longrightarrow> R;;p1(A,B)~ = p1(A,B)~;;Fst(B,R)"
apply(rule, auto)
apply(subgoal_tac "R;;p1(A,B)~ : _<~>_", typecheck, simp_all)
apply(drule subsetD, simp, safe, elim sig_pairE, simp)
apply(elim compE, typecheck, simp+)
apply(elim RubyE, typecheck, simp)
apply(intro RubyI, rule p1I, simp+, rule parI, simp+, rule IdI, simp+)
apply(subgoal_tac "p1(A,B)~;;Fst(B,R):_<~>_", typecheck, simp_all)
apply(drule subsetD, simp, safe, elim sig_pairE, simp)
apply(elim compE, typecheck, simp+, elim sig_pairE, simp)
apply(elim RubyE, typecheck, simp)
apply(intro RubyI, simp, rule p1I, simp+)
done

theorem par_Fst_reorg_inv:
  " \<lbrakk> R:A<~>C; S:B<~>D \<rbrakk> \<Longrightarrow>
    [[R,Fst(F,S)]];;reorg(C,D,F)~ = reorg(A,B,F)~ ;; Fst(F, [[R,S]])"
apply(rule, auto)
apply(subgoal_tac "[[R,Fst(F, S)]] ;; reorg(C, D, F)~ : _<~>_", typecheck, simp_all)
apply(drule subsetD, simp, safe, elim sig_pairE, simp)
apply(elim compE, typecheck, simp+, elim sig_pairE, simp)
apply(erule invE, typecheck, erule reorgE, typecheck, simp)
apply(erule parE, simp+, erule FstE, erule parE, simp+, erule IdE, simp)
apply(intro RubyI, rule reorgI, simp+)
apply(intro RubyI, simp+)
apply(subgoal_tac "reorg(A, B, F)~ ;; Fst(F, [[R,S]]) : _<~>_", typecheck, simp_all)
apply(drule subsetD, simp, safe, elim sig_pairE, simp)
apply(elim compE, typecheck, simp+, elim sig_pairE, simp)
apply(erule invE, typecheck, erule reorgE, typecheck, simp)
apply(erule FstE, erule parE, simp+, elim RubyE, simp+)
apply(intro RubyI)
defer
apply(rule reorgI, simp+, intro RubyI, simp+)
done


find_theorems "reorg"
find_theorems "_ : domain(_)"
find_theorems "_ = _" "_ ;; _ = _;; _"

end