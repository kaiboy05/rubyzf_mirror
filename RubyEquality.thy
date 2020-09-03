theory RubyEquality
imports RecComb
begin

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

end