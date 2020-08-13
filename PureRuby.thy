theory PureRuby
imports Relation
begin

definition comp :: "[i, i] \<Rightarrow> i" ("(_ ;;/ _)" [60, 61] 60) where
  "R ;; S == {xz:domain(R) * range(S). EX x z y. xz = <x, z> & <x, y>:R & <y, z>:S}"

definition par :: "[i, i] \<Rightarrow> i" ("([[_,/_]])") where
  "[[R, S]] == {xy:((sig(dtyp(R) * dtyp(S)))) * (sig(rtyp(R) * rtyp(S))).
                EX x y. xy = <x, y> & <pri(x), pri(y)>:R & <sec(x), sec(y)>:S}"

definition delay :: "i \<Rightarrow> i" ("(D'(_'))") where
  "D(A) == {xy:(sig(A)) * (sig(A)). EX x y. xy = <x, y> & (ALL t:int. x`t = y`(t $+ $#1))}"

definition spread :: "i \<Rightarrow> i" where
  "spread(f) == {xy:(sig(domain(f))) * (sig(range(f))). 
                  EX x y. xy = <x, y> & (ALL t:int. <x`t, y`t>:f)}"

theorem comp_type: "\<lbrakk> r:A~B; s:B~C \<rbrakk> \<Longrightarrow> (r ;; s):A~C"
apply(auto simp add: comp_def)
done

theorem comp_type2: "\<lbrakk> r:A~B; s:C~E \<rbrakk> \<Longrightarrow> (r ;; s):A~E"
apply(auto simp add: comp_def)
done

theorem compI: "\<lbrakk> <x,y>:R; <y,z>:S \<rbrakk> \<Longrightarrow> <x,z>:(R ;; S)"
apply(auto simp add: comp_def)
done

theorem compE: "\<lbrakk> <x, z>:(R ;; S); R:A~B; S:B~C;
                  \<And>y. \<lbrakk> y:B; <x, y>:R; <y, z>:S \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(auto simp add: comp_def)
done

theorem compE2: "\<lbrakk> <x, z>:(R ;; S); R:A~B; S:C~E;
                  \<And>y. \<lbrakk> y:B; y:C; <x, y>:R; <y, z>:S \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(auto simp add: comp_def)
done

theorem comp_iff: "\<lbrakk> R:A<~>B; S:B<~>C; x:sig(A); z:sig(C) \<rbrakk> 
                  \<Longrightarrow> <x, z>:(R ;; S) \<longleftrightarrow> (EX y:sig(B). <x, y>:R & <y, z>:S)"
apply(auto simp add: comp_def)
done

theorem par_type: "\<lbrakk> r:A<~>B; s:C<~>E \<rbrakk> \<Longrightarrow> [[r, s]]:((A*C) <~> (B*E))"
apply(auto simp add: par_def)
apply(elim sig_pairE, auto, rule signal_types)
apply((rule dtyp_rel, simp+)+)
apply(elim sig_pairE, auto, rule signal_types)
apply((rule rtyp_rel, simp+)+)
done

theorem parI: "\<lbrakk> <x1, y1>:R; <x2, y2>:S; x1:sig(A); x2:sig(B); y1:sig(C); y2:sig(E) \<rbrakk> 
                \<Longrightarrow> <<x1#x2>, <y1#y2>>:[[R, S]]"
apply(auto simp add: par_def signal_simps)
apply(rule signal_types, (rule dtyp_sig, simp+)+)
apply(rule signal_types, (rule rtyp_sig, simp+)+)
done

theorem parE: "\<lbrakk> <<x1#x2>, <y1#y2>>:[[R, S]]; x1:sig(A); x2:sig(B); y1:sig(C); y2:sig(E);
              \<lbrakk> <x1, y1>:R; <x2, y2>:S \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(auto simp add: par_def signal_simps)
done

theorem delay_type: "D(A): A<~>A"
apply(auto simp add: delay_def)
done

theorem delayI: "\<lbrakk> ALL t:int. x`t = y`(t $+ $#1); x:sig(A); y:sig(A) \<rbrakk> \<Longrightarrow> <x, y>:D(A)"
apply(auto simp add: delay_def)
done

theorem delayE: "\<lbrakk> <x, y>:D(A); \<lbrakk> ALL t:int. x`t = y`(t $+ $#1) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(auto simp add: delay_def)
done

theorem spread_type: "\<lbrakk> f:A~B \<rbrakk> \<Longrightarrow> spread(f):A<~>B"
apply(simp add: spread_def)
apply(insert domain_rel_subset[of f A "%x. B"], simp)
apply(insert range_rel_subset[of f A B], simp)
apply(auto)
apply((erule sig_sub_func, blast)+)
done

theorem spreadI: "\<lbrakk> ALL t:int. <x`t, y`t>:f; f:A~B; x:sig(A); y:sig(B) \<rbrakk> \<Longrightarrow> <x, y>:spread(f)"
apply(auto simp add: spread_def)
apply((rule sig_sub_func, auto)+)
done

theorem spreadE: "\<lbrakk> <x,y>:spread(f); \<lbrakk> ALL t:int. <x`t, y`t>:f \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(auto simp add: spread_def)
done

theorem D_chel_rel: "A:ChTy \<Longrightarrow> D(A):ChEl<~>ChEl"
apply(auto simp add: delay_def ChEl_def ChTy_def)
apply((rule sig_sub_func, auto)+)
done

theorem spread_chel_rel: "\<lbrakk> A:ChTy; B:ChTy; f:A~B \<rbrakk> \<Longrightarrow> spread(f):ChEl<~>ChEl"
apply(rule spread_type)
apply(auto simp add: ChEl_def ChTy_def)
done

theorem par_chel_rel: "\<lbrakk> S:ChEl<~>ChEl; R:ChEl<~>ChEl \<rbrakk> \<Longrightarrow> [[R, S]]:ChEl<~>ChEl"
apply(insert par_type[of R ChEl ChEl S ChEl ChEl], simp)
apply(subgoal_tac "(sig(ChEl * ChEl)) \<subseteq> sig(ChEl)")
apply(auto)
apply(rule sig_sub_func, simp)
apply(subgoal_tac "(ChEl * ChEl) \<subseteq> ChEl")
apply(auto simp add: ChEl_def)
apply(rule Pair_in_univ, simp+)
done

theorem assoc_comp: "\<lbrakk> R:A<~>B; S:B<~>C; T:C<~>E \<rbrakk> \<Longrightarrow> (R ;; S) ;; T = R ;; (S ;; T)"
apply(auto simp add: comp_def)
apply(rule, rule)
apply(blast+)
done

theorem par_comp_dist: 
  "\<lbrakk> R:A<~>B; S:C<~>G; T:B<~>E; W:G<~>F \<rbrakk> \<Longrightarrow> [[R,S]] ;; [[T,W]] = [[(R ;; T), (S ;; W)]]"
apply(rule, rule)
apply(insert par_type[of R A B S C G], simp)
apply(insert par_type[of T B E W G F], simp)
apply(insert comp_type[of "[[R,S]]" "(sig(A \<times> C))" "(sig(B \<times> G))" "[[T, W]]" "(sig(E \<times> F))"], simp)
apply(frule rev_subsetD, simp)
apply(erule SigmaE, simp)
apply(elim parE compE sig_pairE, simp_all)
apply(erule sig_pairE, simp)
apply(intro parI compI spreadI, simp_all)
apply(elim parE, simp_all)
apply(erule parE, simp_all) back
apply(erule parE, simp_all)
apply(erule parE, simp_all) back
apply(rule)
apply(insert par_type[of "R;;T" A E "S;;W" C F])
apply(insert comp_type[of R "sig(A)" "sig(B)" T "sig(E)"], simp)
apply(insert comp_type[of S "sig(C)" "sig(G)" W "sig(F)"], simp)
apply(frule rev_subsetD, simp)
apply(erule SigmaE, simp)
apply(elim parE compE sig_pairE, simp_all)
apply(erule parE, simp_all)
apply(elim compE, simp_all)
apply(rule compI)
apply(subgoal_tac "<<a#b>, <ya#yb>>:[[R,S]]", simp)
apply(rule parI, simp_all)
apply(rule parI, simp_all)
done

theorem spread_comp_lem: "\<lbrakk> R:A1<~>B1; S:A2<~>B2; T:B1<~>C1; W:B2<~>C2 \<rbrakk> 
                          \<Longrightarrow> [[R,S]] ;; [[T,W]] = [[(R ;; T), (S ;; W)]]"
apply(rule par_comp_dist, simp_all)
done

theorem spread_comp: "\<lbrakk> f:A~B; g:B~C \<rbrakk> \<Longrightarrow> spread(f);;spread(g) = spread(f ;; g)"
apply(rule, rule)
apply(frule comp_type, simp)
apply(drule spread_type)
apply(drule spread_type)
apply(frule comp_type, simp) back
apply(frule rev_subsetD, simp)
apply(erule SigmaE, simp)
apply(rule spreadI, simp_all)
apply(erule compE, simp_all)
apply(elim spreadE)
apply(rule, rule compI, auto)
apply(drule PowI)
apply(drule PowI)
apply(frule comp_type, simp)
apply(frule spread_type) back back
apply(frule rev_subsetD, simp)
apply(erule SigmaE, simp)
apply(erule spreadE)
apply(subgoal_tac "\<forall>t\<in>int. EX z:B. (\<langle>xa ` t, z\<rangle> \<in> f & <z, y`t> : g)")
apply(subst (asm) skolem_intro[of int B])
apply(erule bexE)
apply(subst (asm) ball_conj_distrib[of int])
apply(erule conjE)
apply(rule compI)
apply(rule spreadI, blast)
apply(auto)
apply(rule spreadI, simp_all)
apply(frule rev_bspec[of _ int "%x. _ : f;;g"], blast)
apply(erule compE, simp_all)
apply(blast)
done

end