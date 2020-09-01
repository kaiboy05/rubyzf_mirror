theory RubyUsefulTheorems
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
apply(typecheck add: powf_type, simp+)
apply(subst comp_assoc, typecheck add: powf_type, simp+)
apply(subst comp_assoc[THEN sym], typecheck add: powf_type, simp+)
apply(subst powf_succ, simp)
done

theorem pow_distrib:
  "\<lbrakk> Q:A<~>A; R:A<~>A; n:nat; Q;;R = R;;Q \<rbrakk> 
  \<Longrightarrow> pow(A,n,Q) ;; pow(A,n,R) = pow(A,n,(Q;;R))"
apply(induct_tac n)
apply((subst powf_zero_iff)+)
apply(rule Id_left, typecheck)
apply(subst powf_succ, simp)
apply(subst comp_assoc, typecheck add: powf_type, simp+)
apply(subst powf_succ, simp)
apply(subst comp_assoc[of Q _ _ "powf(A, _, \<lambda>_\<in>nat. R)" _ R, THEN sym])
apply(typecheck add: powf_type, simp+)
apply(subst pow_disturb_lemma, simp_all)
apply(subst comp_assoc[THEN sym])
apply(typecheck add: powf_type, simp+)
apply(subst comp_assoc[THEN sym])
apply(typecheck add: powf_type, simp+)
apply(subst comp_assoc)
apply(typecheck add: powf_type, simp+)
apply(subst powf_succ, simp)
done

find_theorems powf

end