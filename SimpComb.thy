theory SimpComb
imports Wiring
begin

definition inv' :: "[i, i, i] \<Rightarrow> i" where
  "inv'(A,B,R) == lwir(B,A) ;; [[Id(B), [[R,Id(A)]]]] ;; rwir(B,A)"

definition "inv" :: "i \<Rightarrow> i" ("(_~)" [70] 70) where
  "R~ == inv'(dtyp(R), rtyp(R), R)"

definition Conj :: "[i, i] \<Rightarrow> i" where
  "Conj(R,S) == S ;; R ;; (S~)"

definition Fst :: "[i, i] \<Rightarrow> i" where
  "Fst(A,R) == [[R, Id(A)]]"

definition Snd :: "[i, i] \<Rightarrow> i" where
  "Snd(A,R) == [[Id(A), R]]"

definition below' :: "[i, i, i, i, i, i, i, i, i] \<Rightarrow> i" where
  "below'(A,B,C,De, E, F, G, R, S) ==
    reorg(A,E,F) ;; Snd(A,S) ;; (reorg(A,B,G)~) ;;
    Fst(G,R) ;; reorg(C, De, G)"

definition below :: "[i, i] \<Rightarrow> i" ("(_ ||/ _)" [67, 66] 66) where
  "R || S == below'(ddtyp(R), rdtyp(R), drtyp(R), rrtyp(R),
                    ddtyp(S), rdtyp(S), rrtyp(S), R, S)"

definition beside :: "[i, i] \<Rightarrow> i" ("(_ <~~>/ _)" [67, 66] 66) where
  "(R <~~> S) == ((R)~ || (S)~)~"

definition loop2' :: "[i, i, i, i] \<Rightarrow> i" where
  "loop2'(A,B,C,R) == 
    lwir(A,B) ;; (reorg(A,B,B)~) ;; Fst(B,R) ;; reorg(C,B,B) ;; (lwir(C,B)~)"

definition loop2 :: "i \<Rightarrow> i" where
  "loop2(R) == loop2'(ddtyp(R), rdtyp(R), drtyp(R), R)"

definition loop4' :: "[i, i, i, i, i, i] \<Rightarrow> i" where
  "loop4'(A,B,C,De, E, R) ==
    cross(A,C) ;; loop2(reorg(C,A,B) ;; cross(C,A*B) ;; R ;; (reorg(De, E, B)~))"

definition loop4 :: "i \<Rightarrow> i" where
  "loop4(R) == loop4'(domain(ddtyp(R)), range(ddtyp(R)),
                      rdtyp(R), drtyp(R), domain(rrtyp(R)), R)"

lemma inv_inv'_iff_typ_rel: "\<lbrakk>R:A<~>B; x:R~; R~ :rtyp(R)<~>dtyp(R)\<rbrakk> \<Longrightarrow> x \<in> inv'(A, B, R)"
apply(auto, drule subsetD, simp, safe)
apply(unfold inv_def inv'_def)
apply(erule compE, typecheck, rule sub_dtyp_rtyp, simp)
apply(elim sig_pairE, simp)
apply(erule rwirE, simp)
apply(erule compE, typecheck, rule sub_dtyp_rtyp, simp)
apply(elim sig_pairE, simp)
apply(elim parE IdE lwirE, simp_all)
apply(intro RubyI)
apply(subgoal_tac "<aa, <aa#<y#y>>>:lwir(B,A)", simp)
apply(intro RubyI, simp_all, blast, blast)
apply(subgoal_tac "<<aa#<y#y>>, <aa#<aa#y>>>:[[Id(B), [[R, Id(A)]]]]", simp)
apply(intro RubyI, simp_all, blast, blast)
apply(intro RubyI, blast, blast)
done

lemma inv_inv'_iff_typ_sig: "\<lbrakk>R:A<~>B; x:inv'(A, B, R); inv'(A, B, R):B<~>A\<rbrakk> \<Longrightarrow> x \<in> R~"
apply(auto, drule subsetD, simp, safe)
apply(unfold inv_def inv'_def)
apply(erule compE, typecheck, simp)
apply(elim sig_pairE, simp)
apply(erule rwirE, simp)
apply(erule compE, typecheck, simp)
apply(elim sig_pairE, simp)
apply(elim parE IdE lwirE, simp_all)
apply(intro RubyI)
apply(subgoal_tac "<aa, <aa#<y#y>>>:lwir(rtyp(R), dtyp(R))", simp)
apply(intro RubyI, simp_all add: rtyp_sig dtyp_sig)
apply(subgoal_tac "<<aa#<y#y>>, <aa#<aa#y>>>:[[Id(rtyp(R)),[[R,Id(dtyp(R))]]]]", simp)
apply(intro RubyI, simp_all add: rtyp_sig dtyp_sig)
apply(intro RubyI, simp_all add: rtyp_sig dtyp_sig)
done

theorem inv_inv'_iff: "R:A<~>B \<Longrightarrow> R~ = inv'(A,B,R)"
apply(rule, auto)
apply(subgoal_tac "R~ : rtyp(R)<~>dtyp(R)")
apply(rule inv_inv'_iff_typ_rel, blast+)
defer
apply(subgoal_tac "inv'(A,B,R) : B<~>A")
apply(rule inv_inv'_iff_typ_sig, blast+)
apply(unfold inv_def inv'_def)
apply(typecheck, simp_all)
done

theorem inv_type: "R:A<~>B \<Longrightarrow> R~ : B<~>A"
apply(subst inv_inv'_iff, simp)
apply(unfold inv'_def, typecheck)
done

theorem invR: "\<lbrakk> R:A<R>B \<rbrakk> \<Longrightarrow> R~ : B<R>A"
apply(subst inv_inv'_iff)
apply(insert ruby_sub_sig[of A B], blast)
apply(drule subsetD, simp)
apply(unfold inv'_def)
apply(intro RubyR)
apply(subgoal_tac "lwir(B, A) \<in> B<R>B*A*A", simp)
prefer 2
apply(subgoal_tac "[[Id(B),[[R,Id(A)]]]] \<in> B \<times> A \<times> A<R> B*B*A", simp)
apply((intro RubyR, simp_all add: Ruby_ch)+)
done

lemma dtyp_sig_rev: "\<lbrakk>x:sig(A); \<langle>x, y\<rangle> \<in> R\<rbrakk> \<Longrightarrow> x \<in> sig(dtyp(R))"
apply(rule dtyp_sig, simp_all)
done

lemma rtyp_sig_rev: "\<lbrakk>y:sig(B); \<langle>x, y\<rangle> \<in> R\<rbrakk> \<Longrightarrow> y \<in> sig(rtyp(R))"
apply(rule rtyp_sig, simp_all)
done

theorem invI: "\<lbrakk> <b,a>:R; a:sig(A); b:sig(B) \<rbrakk> \<Longrightarrow> <a,b>:R~"
apply(drule rtyp_sig_rev, simp, drule dtyp_sig_rev, simp)
apply(unfold inv_def inv'_def)
apply(intro RubyI)
apply(subgoal_tac "<a, <a#<b#b>>>:lwir(rtyp(R), dtyp(R))", simp)
apply(intro RubyI, simp_all)
apply(subgoal_tac "\<langle><a#<b#b>>, <a#<a#b>>\<rangle>:[[Id(rtyp(R)),[[R,Id(dtyp(R))]]]]", simp)
apply((intro RubyI, simp_all)+)
done

theorem invE: "\<lbrakk> <a,b>:R~; R:A<~>B; \<lbrakk> <b,a>:R \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(frule inv_type)
apply(frule mem_rel_dtype, simp)
apply(frule mem_rel_rtype, simp)
apply(subgoal_tac "<b,a>:R", simp)
apply(subst (asm) inv_inv'_iff, simp, unfold inv'_def)
apply(erule compE, typecheck)
apply(elim sig_pairE, simp)
apply(erule rwirE, simp_all)
apply(erule compE, typecheck, simp)
apply(elim sig_pairE, simp)
apply(elim parE, simp_all)
apply(elim IdE lwirE, simp_all)
done

theorem inv_iff: "R:A<~>B \<Longrightarrow> <a,b>:R~ \<longleftrightarrow> <b,a>:R"
apply(rule)
apply(erule invE, simp, simp)
apply(frule mem_rel_dtype, simp)
apply(frule mem_rel_rtype, simp)
apply(rule invI, simp_all)
done

theorem Conj_type: "\<lbrakk> R:A<~>A; S:B<~>A \<rbrakk> \<Longrightarrow> Conj(R,S):B<~>B"
apply(unfold Conj_def)
apply(typecheck add: inv_type)
done

theorem conjR: "\<lbrakk> R:A<R>A; S:B<R>A \<rbrakk> \<Longrightarrow> Conj(R,S):B<R>B"
apply(unfold Conj_def)
apply(intro RubyR invR, simp_all)
done

theorem ConjI: "\<lbrakk> x:(S ;; R ;; (S~)) \<rbrakk> \<Longrightarrow> x:Conj(R,S)"
apply(unfold Conj_def, simp)
done

theorem ConjE: "\<lbrakk> x:Conj(R,S); x:(S;;R;;(S~)) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(unfold Conj_def, simp)
done

theorem Fst_type: "\<lbrakk> R:A<~>B \<rbrakk> \<Longrightarrow> Fst(C,R):A*C<~>B*C"
apply(unfold Fst_def, typecheck)
done

theorem FstR: "\<lbrakk> R:A<R>B; C:ChTy \<rbrakk> \<Longrightarrow> Fst(C,R):A*C<R>B*C"
apply(unfold Fst_def)
apply(intro RubyR, simp_all)
done

theorem FstI: "\<lbrakk> x:[[R, Id(A)]] \<rbrakk> \<Longrightarrow> x:Fst(A,R)"
apply(unfold Fst_def, simp)
done

theorem FstE: "\<lbrakk> x:Fst(A,R); x:[[R,Id(A)]] \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(unfold Fst_def, simp)
done

theorem Snd_type: "\<lbrakk> R:A<~>B \<rbrakk> \<Longrightarrow> Snd(C,R):C*A<~>C*B"
apply(unfold Snd_def, typecheck)
done

theorem SndR: "\<lbrakk> R:A<R>B; C:ChTy \<rbrakk> \<Longrightarrow> Snd(C,R):C*A<R>C*B"
apply(unfold Snd_def)
apply(intro RubyR, simp_all)
done

theorem SndI: "\<lbrakk> x:[[Id(A), R]] \<rbrakk> \<Longrightarrow> x:Snd(A,R)"
apply(unfold Snd_def, simp)
done

theorem SndE: "\<lbrakk> x:Snd(A,R); x:[[Id(A), R]] \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(unfold Snd_def, simp)
done

lemma sig_pair_type_sub: "sig(A) \<subseteq> sig(C) \<Longrightarrow> sig(A*B) \<subseteq> sig(C*B)"
apply(rule)
apply(erule sig_pairE, simp)
apply(drule subsetD, simp+)
done

lemma sigma_sub_subset1: "\<lbrakk> A \<subseteq> B; D \<subseteq> C * A \<rbrakk> \<Longrightarrow> D \<subseteq> C * B"
apply(blast)
done

lemma sigma_sub_subset2: "\<lbrakk> A \<subseteq> B; D \<subseteq> A * C \<rbrakk> \<Longrightarrow> D \<subseteq> B * C"
apply(blast)
done

lemma below_below'_typ_rel_S_help: 
  "\<lbrakk> R:A*B<~>C*D; S:E*F<~>B*G \<rbrakk> \<Longrightarrow> S:ddtyp(S)*rdtyp(S)<~>rdtyp(R)*rrtyp(S)"
apply(rule, auto)
apply(frule subsetD, simp, auto)
apply(rule sig_sub_func, simp)
apply(simp add: ddtyp_def rdtyp_def)
apply(rule domain_time_range_extension, simp)
apply(frule dtyp_sig, simp, simp)
apply(rule sig_sub_func, simp)
apply(drule apply_funtype, simp) back
apply(auto)
apply(simp add: rdtyp_def dtyp_def)
oops

find_theorems "_:range(_)"

lemma below_below'_typ_rel:
  "\<lbrakk>R \<in> A \<times> B<~>C \<times> De; S \<in> E \<times> F<~>B \<times> G; x \<in> R || S; 
    R || S \<in> (ddtyp(R) \<times> ddtyp(S)) \<times> rdtyp(S)<~>drtyp(R) \<times> rrtyp(R) \<times> rrtyp(S)\<rbrakk>
    \<Longrightarrow> x \<in> below'(A, B, C, De, E, F, G, R, S)"
apply(auto, drule subsetD, simp, safe)
apply(elim sig_pairE, simp)
apply(unfold below_def below'_def)
apply(erule compE, typecheck add: Fst_type Snd_type inv_type, simp)
apply(rule sub_ddtyp_rrtyp, simp)
apply(erule compE, typecheck add: Fst_type Snd_type inv_type, simp)
apply(rule sub_ddtyp_rrtyp, simp)
apply(erule compE2, typecheck add: Fst_type Snd_type inv_type, simp)
apply(erule compE, typecheck add: Fst_type Snd_type inv_type, simp)
apply(rule PowD, rule sub_ddtyp_rrtyp, simp)
apply(thin_tac "yc \<in> sig(ddtyp(R) \<times> rdtyp(R) \<times> rrtyp(S))")
apply(elim sig_pairE, simp)
apply(erule reorgE, simp)
apply(erule FstE, simp_all, erule parE, simp_all)
apply(erule invE, erule reorgE, simp_all)
apply(rule PowD, typecheck)
apply(erule reorgE, simp_all)
apply(erule reorgE, simp_all)
apply(erule SndE, erule parE, simp_all)
apply(elim IdE, simp_all)
apply(intro compI)
apply(rule reorgI, simp_all)
apply(rule ddtyp_rel, simp_all)
apply(rule ddtyp_rel, simp_all)
apply(rule rdtyp_rel, simp_all)
apply(subgoal_tac "<<af#<ak#bk>>,<af#<aj#bc>>>:Snd(A,S)", simp)
apply(rule SndI, rule parI, rule IdI)
apply(rule ddtyp_rel, simp_all)
apply(subgoal_tac "<<af#<aj#bc>>, <<af#aj>#bc>>:reorg(A,B,G)~", simp)
apply(rule invI, rule reorgI)
apply(rule ddtyp_rel, simp_all)
apply(subgoal_tac "<<<af#aj>#bc>,<<aa#ac>#bc>>:Fst(G,R)", simp)
apply(rule FstI, rule parI, simp_all)
apply(rule IdI, simp_all)
apply(rule reorgI, simp_all)
apply(rule drtyp_rel, simp_all)
apply(rule rrtyp_rel, simp_all)
done

lemma below_below'_typ_sig:
  "\<lbrakk>R \<in> A \<times> B<~>C \<times> De; S \<in> E \<times> F<~>B \<times> G; x \<in> below'(A, B, C, De, E, F, G, R, S); 
    below'(A, B, C, De, E, F, G, R, S) \<in> (A \<times> E) \<times> F<~>C \<times> De \<times> G\<rbrakk>
    \<Longrightarrow> x \<in> R || S"
apply(auto, drule subsetD, simp, safe)
apply(elim sig_pairE, simp)
apply(unfold below_def below'_def)
apply(elim compE, typecheck add: Fst_type Snd_type inv_type, simp_all)
apply(elim sig_pairE, simp)
apply(elim RubyE, simp_all)
apply(elim FstE SndE invE, typecheck)
apply(elim reorgE, simp_all)
apply(elim parE, simp_all)
apply(elim IdE, simp_all)
apply(intro RubyI)
apply(subgoal_tac "\<langle><<af#ak>#bk>,<af#<ak#bk>>\<rangle>:reorg(ddtyp(R), ddtyp(S), rdtyp(S))", simp)
apply(rule reorgI, simp_all add: typ_sigs)
apply(subgoal_tac "\<langle><af#<ak#bk>>,<af#<aj#bc>>\<rangle>:Snd(ddtyp(R), S)", simp)
apply(rule SndI, rule parI, rule IdI, simp_all add: typ_sigs)
apply(subgoal_tac "\<langle><af#<aj#bc>>,<<af#aj>#bc>\<rangle>:reorg(ddtyp(R), rdtyp(R), rrtyp(S))~", simp)
apply(rule invI, rule reorgI, simp_all add: typ_sigs)
apply(subgoal_tac "\<langle><<af#aj>#bc>, <<aa#ac>#bc>\<rangle> \<in> Fst(rrtyp(S), R)", simp)
apply(rule FstI, rule parI, simp_all add: typ_sigs, rule IdI, simp_all add: typ_sigs)
apply(rule reorgI, simp_all add: typ_sigs)
done

theorem below_below'_iff: 
  "\<lbrakk> R:A*B<~>C*De; S:E*F<~>B*G \<rbrakk> \<Longrightarrow> R||S = below'(A,B,C,De,E,F,G,R,S)"
apply(rule, rule)
apply(subgoal_tac "R || S:((ddtyp(R)*ddtyp(S))*rdtyp(S))<~>(drtyp(R)*rrtyp(R)*rrtyp(S))")
apply(rule below_below'_typ_rel, blast+) 
defer
apply(rule)
apply(subgoal_tac "below'(A, B, C, De, E, F, G, R, S) \<in> (A \<times> E) \<times> F<~>C \<times> De \<times> G")
apply(rule below_below'_typ_sig, blast+)
apply(unfold below_def below'_def)
apply(typecheck add: Fst_type Snd_type inv_type)
done

theorem below_iff2:
  "\<lbrakk> R:A*B<~>C*De; S:E*F<~>B*G \<rbrakk>
    \<Longrightarrow> R||S = reorg(A,E,F);;Snd(A,S);;(reorg(A,B,G)~);;Fst(G,R);;reorg(C,De,G)"
apply(subst below_below'_iff, simp_all)
apply(unfold below'_def, simp)
done

theorem below_type: 
  "\<lbrakk> R:A*B<~>C*De; S:E*F<~>B*G \<rbrakk> \<Longrightarrow> R||S:(A*E)*F<~>C*(De*G)"
apply(subst below_below'_iff, blast+)
apply(unfold below'_def, typecheck add: Fst_type Snd_type inv_type)
done

lemma "A \<subseteq> B \<Longrightarrow> C \<subseteq> D \<Longrightarrow> A<~>C \<subseteq> C<~>D"
apply(rule, rule, rule)
oops

lemma sig_pair_type_sub2: "\<lbrakk> sig(A) \<subseteq> sig(C); sig(B) \<subseteq> sig(D) \<rbrakk> \<Longrightarrow> sig(A*B) \<subseteq> sig(C*D)"
apply(rule)
apply(erule sig_pairE, drule subsetD, simp, drule subsetD, simp)
apply(simp)
done

theorem below_type2:
  "\<lbrakk> R:A*B<~>C*De; S:E*F<~>H*G \<rbrakk> \<Longrightarrow> R||S:(A*E)*F<~>C*(De*G)"
apply(unfold below_def below'_def)
apply(typecheck)
apply(subgoal_tac 
      "(ddtyp(R) \<times> ddtyp(S)) \<times> rdtyp(S)<~>ddtyp(R) \<times> ddtyp(S) \<times> rdtyp(S) 
        \<subseteq> (A \<times> E) \<times> F<~>A \<times> E \<times> F")
apply(rule subsetD, simp, typecheck)
apply(rule Pow_mono)
apply((intro Sigma_mono sig_pair_type_sub2)+)
apply((rule, elim typ_rels, simp)+)
apply(typecheck add: Snd_type)
apply(typecheck add: inv_type)
apply(typecheck add: Fst_type)
apply(subgoal_tac 
      "(drtyp(R) \<times> rrtyp(R)) \<times> rrtyp(S)<~>drtyp(R) \<times> rrtyp(R) \<times> rrtyp(S) 
        \<subseteq> (C \<times> De) \<times> G<~>C \<times> De \<times> G")
apply(rule subsetD, simp, typecheck)
apply(rule Pow_mono)
apply((intro Sigma_mono sig_pair_type_sub2)+)
apply((rule, elim typ_rels, simp)+)
done

theorem belowR: 
  "\<lbrakk> A:ChTy; B:ChTy; C:ChTy; De:ChTy; E:ChTy; F:ChTy; G:ChTy;
    R:A*B<R>C*De; S:E*F<R>B*G \<rbrakk> \<Longrightarrow> R || S:(A*E)*F<R>C*(De*G)"
apply(subst below_below'_iff)
apply(frule rev_subsetD[of R], rule ruby_sub_sig, simp)
apply(frule rev_subsetD[of S], rule ruby_sub_sig, simp)
apply(unfold below'_def)
apply(intro RubyR FstR SndR invR)
apply(((rule RubyR)?, (rule FstR)?, (rule SndR)?, blast+)+)
done

theorem belowI: 
  "\<lbrakk> a:sig(A); b:sig(B); c:sig(C); d:sig(De); e:sig(E); f:sig(F);
    g:sig(G); <<a#b>,<c#d>>:R; <<e#f>,<b#g>>:S \<rbrakk>
    \<Longrightarrow> <<<a#e>#f>, <c#<d#g>>>:R||S"
apply(unfold below_def below'_def)
apply(intro RubyI)
apply(subgoal_tac "\<langle><<a#e>#f>, <a#<e#f>>\<rangle> \<in> reorg(ddtyp(R), ddtyp(S), rdtyp(S))", simp)
apply(rule RubyI, simp_all add: typ_sigs)
apply(subgoal_tac "\<langle><a#<e#f>>, <a#<b#g>>\<rangle> \<in> Snd(ddtyp(R),S)", simp)
apply(rule SndI, rule parI, rule IdI, simp_all add: typ_sigs)
apply(subgoal_tac "\<langle><a#<b#g>>, <<a#b>#g>\<rangle> \<in> reorg(ddtyp(R), rdtyp(R), rrtyp(S))~", simp)
apply(rule invI, rule reorgI, simp_all add: typ_sigs)
apply(subgoal_tac "\<langle><<a#b>#g>, <<c#d>#g>\<rangle> \<in> Fst(rrtyp(S), R)", simp)
apply(rule FstI, rule parI, simp_all add: typ_sigs, rule IdI, simp add: typ_sigs)
apply(rule reorgI, simp_all add: typ_sigs)
done

theorem belowE2:
  "\<lbrakk> <<<a#e>#f>,<c#<d#g>>>:R||S;
    \<And>b. \<lbrakk> <<a#b>,<c#d>>:R; <<e#f>,<b#g>>:S; b:sig(B); b:sig(G) \<rbrakk> \<Longrightarrow> P;
    R:A*B<~>C*De; S:E*F<~>G*H;
    a:sig(A'); c:sig(C'); d:sig(De'); e:sig(E'); f:sig(F'); g:sig(G') \<rbrakk> \<Longrightarrow> P"
apply(frule sub_ddtyp_rrtyp)
apply(frule sub_ddtyp_rrtyp) back
apply(rotate_tac 10)
apply(unfold below_def below'_def)
apply(erule compE, typecheck add: Fst_type Snd_type inv_type)
apply(elim sig_pairE, simp)
apply(erule reorgE, typecheck add: Fst_type Snd_type inv_type)
apply(erule compE, typecheck add: Fst_type Snd_type inv_type, simp+)
apply(erule FstE, elim sig_pairE, simp, erule parE, simp_all, erule IdE, simp_all)
apply(erule compE2, typecheck add: Fst_type Snd_type inv_type, simp+)
apply(elim sig_pairE, simp)
apply(erule spair_inject, simp_all)
apply(erule spair_inject, simp_all)
apply((drule PowI)+)
apply(erule invE, typecheck)
apply(elim compE, typecheck add: Snd_type)
apply(elim sig_pairE, simp)
apply(elim SndE reorgE, simp_all)
apply(erule parE, simp_all)
apply(erule IdE, simp)
apply(subgoal_tac "af:sig(B)" "af:sig(G)", simp)
apply(elim typ_rels, simp)
apply(rule rdtyp_rel, simp+)
done

lemma spair_type_rev: "\<lbrakk> <a#b>:sig(A*B); a:sig(A'); b:sig(B') \<rbrakk> \<Longrightarrow> a:sig(A) & b:sig(B)"
apply(elim sig_pairE)
apply(erule spair_inject, simp_all)
done

theorem belowE: 
  "\<lbrakk> <<<a#e>#f>,<c#<d#g>>>:R||S; 
    \<And>b. \<lbrakk> <<a#b>,<c#d>>:R; <<e#f>,<b#g>>:S; b:sig(B) \<rbrakk> \<Longrightarrow> P;
    R:A*B<~>C*De; S:E*F<~>B*H;
    a:sig(A'); c:sig(C'); d:sig(De'); e:sig(E'); f:sig(F'); g:sig(G')\<rbrakk> \<Longrightarrow> P"
apply(subst (asm) below_below'_iff, blast+)
apply(unfold below'_def)
apply(elim compE, typecheck add: Fst_type Snd_type inv_type)
apply(elim sig_pairE, simp)
apply(elim invE, typecheck)
apply(elim RubyE, typecheck)
apply(elim FstE SndE, elim parE, simp_all, elim IdE, simp)
done

theorem below_iff: 
  "\<lbrakk> a:sig(A'); c:sig(C'); d:sig(De'); e:sig(E'); f:sig(F'); g:sig(G');
    R:A*B<~>C*De; S:E*F<~>B*G \<rbrakk> \<Longrightarrow>
    <<<a#e>#f>,<c#<d#g>>>:R||S \<longleftrightarrow> 
    (EX b:sig(B). <<a#b>,<c#d>>:R & <<e#f>,<b#g>>:S)"
apply(rule)
apply(erule belowE, simp_all)
apply(erule rev_bexI, simp)
apply(erule bexE, rotate_tac 8)
apply(erule conjE)
apply(rule belowI, simp_all)
done

find_theorems "_\<rightarrow>_ \<subseteq> _\<rightarrow>_"
find_theorems name: spair
find_theorems name: bex
find_theorems rwir name: Wiring.RubyI
find_theorems name: Relation
find_theorems name: lwir -name: Ruby

find_theorems comp






end