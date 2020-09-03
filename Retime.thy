theory Retime
imports RubyEquality
begin

definition retime :: "[i,i,i] \<Rightarrow> o" where
  "retime(A,B,R) == (R = (D(A) ;; R ;; D(B)~))"

theorem D_invD_lemma: "t:int \<Longrightarrow> a`t = (lam x:int. a`(x $- $#1)) ` (t $+ $#1)"
apply(simp)
done

theorem invD_D_lemma: "t:int \<Longrightarrow> (lam x:int. a`(x $+ $#1))`t = a`(t $+ $#1)"
apply(simp)
done

theorem delay_Id_1: "\<lbrakk> <x,y>:Id(A) \<rbrakk> \<Longrightarrow> <x,y>: D(A);;D(A)~"
apply(insert Id_type[of A], simp, drule subsetD, simp)
apply(elim RubyE, simp)
apply(intro RubyI)
apply(rule)
apply(rule D_invD_lemma, simp+)
done

theorem delay_Id: "D(A) ;; D(A)~ = Id(A)"
apply(rule, auto)
apply(subgoal_tac "D(A) ;; D(A)~ : A<~>A", typecheck, simp)
apply(drule subsetD, simp, safe)
apply(elim RubyE, typecheck)
apply(subgoal_tac "xa = y", simp)
apply(rule IdI, simp)
apply(rule fun_extension, simp_all)
apply((drule bspec, simp)+, simp)
apply(insert Id_type[of A], simp, drule subsetD, simp, safe)
apply(erule delay_Id_1)
done

theorem delay_Id_inv1: "\<lbrakk> <x,y>:Id(A) \<rbrakk> \<Longrightarrow> <x,y>:D(A)~ ;; D(A)"
apply(insert Id_type[of A], simp, drule subsetD, simp)
apply(elim RubyE, simp)
apply(intro RubyI, rule)
apply(rule invD_D_lemma, simp+)
done

lemma ball_int_minus1: "\<forall>t\<in>int. ya ` t = y ` (t $+ $# 1) \<Longrightarrow> \<forall>t\<in>int. ya ` (t $- $#1) = y ` t"
apply(auto)
done

lemma sig_fun_extension_lemma:
  "\<lbrakk> \<forall>t\<in>int. ya ` t = y ` (t $+ $# 1); 
    \<forall>t\<in>int. ya ` t = xa ` (t $+ $# 1); xa:sig(A); y:sig(A) \<rbrakk> \<Longrightarrow>
    xa = y"
apply(drule ball_int_minus1, drule ball_int_minus1)
apply(rule fun_extension, simp, simp)
apply(drule bspec, simp, drule bspec, simp, simp)
done

theorem delay_Id_inv: "D(A)~ ;; D(A) = Id(A)"
apply(rule, auto)
apply(subgoal_tac "D(A)~ ;; D(A) : A<~>A", typecheck, simp)
apply(drule subsetD, simp, safe)
apply(elim RubyE, typecheck)
apply(subgoal_tac "xa = y", simp)
apply(rule IdI, simp)
apply(rule sig_fun_extension_lemma, blast+)
apply(insert Id_type[of A], simp, drule subsetD, simp)
apply(safe, erule delay_Id_inv1)
done

theorem retime_delay: "retime(A,A,D(A))"
apply(unfold retime_def)
apply(subst comp_assoc, typecheck)
apply(subst delay_Id)
apply(insert delay_type[of A], simp)
done

lemma R_to_type: "R:A<R>B \<Longrightarrow> R:A<~>B"
apply(insert ruby_sub_sig[of A B], blast)
done

theorem retime_comp: 
  "\<lbrakk> R:A<R>B; S:B<R>C ; retime(A,B,R); retime(B,C,S) \<rbrakk> \<Longrightarrow> retime(A,C,R;;S)"
apply(unfold retime_def)
apply(subgoal_tac "(D(A) ;; R ;; D(B)~) ;; (D(B) ;; S ;; D(C)~) = D(A) ;; (R ;; S) ;; D(C)~")
apply(simp)
apply(subst comp_assoc[of "D(A) ;; R" A B "D(B)~" B "D(B) ;; S ;; D(C)~" C])
apply(typecheck, (erule R_to_type)+)
apply(subst comp_assoc[of "D(B)~" B B "D(B) ;; S" C "D(C)~" C, THEN sym])
apply(typecheck, (erule R_to_type)+)
apply(subst comp_assoc[of "D(B)~" B B "D(B)" B "S" C, THEN sym])
apply(typecheck, (erule R_to_type)+)
apply(subst delay_Id_inv)
apply(insert Id_left[of S B C, OF R_to_type], simp)
apply(subst comp_assoc[of "D(A) ;; R" A B "S" C "D(C)~" C, THEN sym])
apply(typecheck, (erule R_to_type)+)
apply(subst comp_assoc[of "D(A)" A A "R" B "S" C, THEN sym])
apply(typecheck, (erule R_to_type)+, simp)
done

theorem retime_spread: "f:A~B \<Longrightarrow> retime(A,B,spread(f))"
apply(unfold retime_def)
apply(rule, auto)
apply(insert spread_type[of f A B], simp, drule subsetD, simp)
apply(safe, erule spreadE)
apply(rule compI)
apply(subgoal_tac "\<langle>xa, (lam t:int. y`(t $- $#1))\<rangle> \<in> D(A) ;; spread(f)", simp)
apply(intro RubyI)
apply(rule, rule D_invD_lemma, simp+)
apply(intro RubyI)
apply(rule, simp+)
apply(thin_tac "spread(f) \<subseteq> (sig(A)) \<times> (sig(B))")
apply(subgoal_tac " D(A) ;; spread(f) ;; D(B)~ : A<~>B", typecheck, simp_all)
apply(drule subsetD, simp, safe)
apply(elim RubyE, typecheck, simp_all)
apply(intro RubyI, typecheck, simp_all)
done

theorem D_eq_parD: "[[D(A), D(B)]] = D(A*B)"
apply(rule, auto)
apply(subgoal_tac "[[D(A), D(B)]]:A*B<~>A*B", typecheck)
apply(simp, drule subsetD, simp)
apply(safe, elim sig_pairE, simp)
apply(elim RubyE, simp_all)
apply(intro RubyI, simp_all)
apply(rule, (subst spair_apply_time, simp)+, simp)
apply(insert delay_type[of "A*B"], simp, drule subsetD, simp)
apply(safe, elim sig_pairE, simp)
apply(elim RubyE)
apply(intro RubyI)
apply(rule, drule bspec, simp)
apply((subst (asm) spair_apply_time, simp)+, simp_all)
apply(rule, drule bspec, simp)
apply((subst (asm) spair_apply_time, simp)+, simp_all)
done

theorem retime_par: 
  "\<lbrakk> R:A<R>B; S:C<R>E; retime(A,B,R); retime(C,E,S) \<rbrakk>
    \<Longrightarrow> retime(A*C, B*E, [[R,S]])"
apply(unfold retime_def)
apply((subst D_eq_parD[THEN sym])+)
apply(subst par_inv_distrib, typecheck)
apply(subst par_comb, typecheck, (erule R_to_type)+)
apply(subst par_comb, typecheck, (erule R_to_type)+)
apply(simp)
done

theorem retime: "R:A<R>B \<Longrightarrow> retime(A,B,R)"
apply(erule ruby_induct)
apply(rule retime_spread, simp_all)
apply(rule retime_delay)
apply(rule retime_comp, simp_all)
apply(rule retime_par, simp_all)
done

theorem retime_eq: "R:A<R>B \<Longrightarrow> D(A) ;; R ;; D(B)~ = R"
apply(drule retime)
apply(unfold retime_def, simp)
done

theorem retime_D_comm: "R:A<R>B \<Longrightarrow> D(A) ;; R = R ;; D(B)"
apply(frule retime)
apply(unfold retime_def)
apply(subgoal_tac "R ;; D(B) = D(A) ;; R ;; D(B)~ ;; D(B)")
apply(thin_tac "R = D(A) ;; R ;; D(B)~")
apply(subst (asm) comp_assoc[of "D(A);;R" A B "D(B)~" B "D(B)" B])
apply(typecheck, (erule R_to_type)+)
apply(subst (asm) delay_Id_inv)
apply(subst (asm) Id_right, typecheck, (erule R_to_type)+)
apply(simp+)
done

end