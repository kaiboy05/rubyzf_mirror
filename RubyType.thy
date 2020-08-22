theory RubyType
imports PureRuby
begin

consts
  pure :: "i"

inductive
  domains "pure" <= "(ChEl <~> ChEl) * ChTy * ChTy"
  intros
    spread: "\<lbrakk> A:ChTy; B:ChTy; f:A~B \<rbrakk> \<Longrightarrow> <spread(f), A, B>:pure"
    delay: "A:ChTy \<Longrightarrow> <D(A), A, A>:pure"
    comp: "\<lbrakk> <R, A, B>:pure; <S, B, C>:pure \<rbrakk> \<Longrightarrow> <R;;S, A, C>:pure"
    par: "\<lbrakk> <R, A1, B1>:pure; <S, A2, B2>:pure \<rbrakk> \<Longrightarrow> <[[R,S]], A1*A2, B1*B2>:pure"
  type_intros spread_chel_rel D_chel_rel comp_type par_chel_rel prod_in_chty

definition rrel :: "[i, i] \<Rightarrow> i" ("(_<R>/_)" [73, 72] 72) where
  "A<R>B == {r:A<~>B. <r, A, B>:pure}"

theorem pure_induct: 
  "\<lbrakk> <x3, x2, x1>:pure;
    \<And> A B f. \<lbrakk> A:ChTy; B:ChTy; f:A~B \<rbrakk> \<Longrightarrow> P_pure4(spread(f), A, B);
    \<And> A. A:ChTy \<Longrightarrow> P_pure4(D(A), A, A);
    \<And> A B C R S. \<lbrakk> <R, A, B>:pure; <S, B, C>:pure; 
      P_pure4(R, A, B); P_pure4(S, B, C) \<rbrakk> \<Longrightarrow> P_pure4(R ;; S, A, C);
    \<And> A1 A2 B1 B2 R S. \<lbrakk> <R, A1, B1>:pure; <S, A2, B2>:pure;
      P_pure4(R, A1, B1); P_pure4(S, A2, B2) \<rbrakk> \<Longrightarrow> P_pure4([[R,S]], A1*A2, B1*B2) \<rbrakk> 
  \<Longrightarrow> P_pure4(x3, x2, x1)"
apply(rule pure.induct, simp_all)
done

theorem pure_rel: "<R, A, B>:pure \<Longrightarrow> R:A<~>B"
apply(rule pure.induct, simp)
apply(erule spread_type)
apply(rule delay_type)
apply(rule comp_type, simp, simp)
apply(rule par_type, simp+)
done

theorem ruby_induct:
  "\<lbrakk> R: A<R>B;
    \<And> f A B. f:A~B \<Longrightarrow> P(A, B, spread(f));
    \<And> A. P(A, A, D(A));
    \<And> R S A B C.
      \<lbrakk> R:A<R>B; S:B<R>C; P(A, B, R); P(B, C, S) \<rbrakk>
      \<Longrightarrow> P(A, C, R;;S);
    \<And> R S A1 A2 B1 B2.
      \<lbrakk> R:A1<R>B1; S:A2<R>B2; P(A1, B1, R); P(A2, B2, S) \<rbrakk>
      \<Longrightarrow> P(A1*A2, B1*B2, [[R,S]]) \<rbrakk> \<Longrightarrow> P(A, B, R)"
apply(auto simp add: rrel_def)
apply(rule pure_induct, simp+)
apply(frule pure_rel) back
apply(frule pure_rel) back back
apply(simp)
apply(frule pure_rel) back
apply(frule pure_rel) back back
apply(simp)
done

theorem ruby_sub_sig: "A<R>B \<subseteq> A<~>B"
apply(auto simp add: rrel_def)
done

theorem spreadR: "\<lbrakk> A:ChTy; B:ChTy; f:A~B \<rbrakk> \<Longrightarrow> spread(f):A<R>B"
apply(auto simp add: rrel_def)
apply(insert spread_type[of f A B], blast)
apply(rule pure.spread, simp+)
done

theorem delayR: "A:ChTy \<Longrightarrow> D(A):A<R>A"
apply(auto simp add: rrel_def)
apply(insert delay_type[of A], blast)
apply(rule pure.delay, simp+)
done

theorem compR: "\<lbrakk> R:A<R>C; S:C<R>B \<rbrakk> \<Longrightarrow> R;;S:A<R>B"
apply(auto simp add: rrel_def)
apply(insert comp_type[of R "sig(A)" "sig(C)" S "sig(B)"], blast)
apply(rule pure.comp, simp+)
done

theorem parR: "\<lbrakk> R:A1<R>B1; S:A2<R>B2 \<rbrakk> \<Longrightarrow> [[R,S]]:A1*A2<R>B1*B2"
apply(auto simp add: rrel_def)
apply(insert par_type[of R A1 B1 S A2 B2], blast)
apply(rule pure.par, simp+)
done

theorem rrelD1: "R:A<R>B \<Longrightarrow> A:ChTy"
apply(auto simp add: rrel_def)
apply(insert dom_subset, blast)
done

theorem rrelD2: "R:A<R>B \<Longrightarrow> B:ChTy"
apply(auto simp add: rrel_def)
apply(insert dom_subset, auto)
done

lemmas RubyR =
  spreadR delayR compR parR

lemmas Ruby_ch =
  Ruby_ch rrelD1 rrelD2

end