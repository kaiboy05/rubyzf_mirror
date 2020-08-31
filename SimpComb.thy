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

theorem ConjR: "\<lbrakk> R:A<R>A; S:B<R>A \<rbrakk> \<Longrightarrow> Conj(R,S):B<R>B"
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

theorem beside_type: 
  "\<lbrakk> R:A*B<~>C*De; S:De*E<~>F*G \<rbrakk> \<Longrightarrow> R <~~> S:A*B*E<~>(C*F)*G"
apply(unfold beside_def)
apply(typecheck add: inv_type below_type)
done

theorem beside_type2:
  "\<lbrakk> R:A*B<~>C*De; S:H*E<~>F*G \<rbrakk> \<Longrightarrow> R <~~> S:A*B*E<~>(C*F)*G"
apply(unfold beside_def)
apply(typecheck add: inv_type below_type2)
done

theorem besideR:
  "\<lbrakk> A:ChTy; B:ChTy; C:ChTy; De:ChTy; E:ChTy; E:ChTy; F:ChTy; G:ChTy;
    R:A*B<R>C*De; S:De*E<R>F*G \<rbrakk> \<Longrightarrow> R<~~>S:A*B*E<R>(C*F)*G"
apply(unfold beside_def)
apply(intro invR belowR, simp_all)
done

theorem besideI:
  "\<lbrakk> d:sig(De); a:sig(A); b:sig(B); c:sig(C); e:sig(E); f:sig(F); g:sig(G);
    <<a#b>,<c#d>>:R; <<d#e>,<f#g>>:S \<rbrakk> \<Longrightarrow> <<a#<b#e>>,<<c#f>#g>>:R<~~>S"
apply(unfold beside_def)
apply(intro invI belowI, simp_all)
done

theorem besideE:
  "\<lbrakk> <<a#<b#e>>, <<c#f>#g>>:R<~~>S;
    \<And>d. \<lbrakk> <<a#b>,<c#d>>:R; <<d#e>,<f#g>>:S; d:sig(De) \<rbrakk> \<Longrightarrow> P;
    R:A*B<~>C*De; S:De*E<~>F*G;
    a:sig(A'); b:sig(B'); c:sig(C'); e:sig(E'); f:sig(F'); g:sig(G') \<rbrakk> \<Longrightarrow> P"
apply(unfold beside_def)
apply(elim invE belowE, typecheck add: below_type inv_type, simp)
done

theorem besideE2:
  "\<lbrakk> <<a#<b#e>>, <<c#f>#g>>:R<~~>S;
    \<And>d. \<lbrakk> <<a#b>,<c#d>>:R; <<d#e>,<f#g>>:S; d:sig(De) \<rbrakk> \<Longrightarrow> P;
    R:A*B<~>C*De; S:H*E<~>F*G;
    a:sig(A'); b:sig(B'); c:sig(C'); e:sig(E'); f:sig(F'); g:sig(G') \<rbrakk> \<Longrightarrow> P"
apply(unfold beside_def)
apply(elim invE belowE2, typecheck add: below_type2 inv_type, simp)
done

theorem beside_iff:
  "\<lbrakk> a:sig(A); b:sig(B); c:sig(C); e:sig(E); f:sig(F); g:sig(G);
    R:A*B<~>C*De; S:De*E<~>F*G \<rbrakk> \<Longrightarrow>
    <<a#<b#e>>,<<c#f>#g>>:R<~~>S \<longleftrightarrow> 
    (EX d:sig(De). <<a#b>, <c#d>>:R & <<d#e>, <f#g>>:S)"
apply(rule)
apply(unfold beside_def)
apply(elim invE belowE, typecheck add: inv_type below_type, blast)
apply(erule bexE, rotate_tac 8)
apply(intro invI belowI, simp_all)
done

lemma loop2_loop2'_iff_typ_rel: 
  "\<lbrakk> R:A*B<~>C*B; loop2(R):ddtyp(R)<~>drtyp(R); x:loop2(R) \<rbrakk> \<Longrightarrow> x:loop2'(A,B,C,R)"
apply(auto, drule subsetD, simp, safe)
apply(unfold loop2_def loop2'_def)
apply(elim compE2, typecheck add: inv_type Fst_type, simp_all)
apply(thin_tac "yb \<in> sig((C \<times> B) \<times> rdtyp(R))", thin_tac "yc \<in> sig((A \<times> B) \<times> rdtyp(R))")
apply(elim invE FstE, typecheck)
apply(elim sig_pairE, simp)
apply(elim reorgE, simp_all, elim lwirE, simp_all)
apply(elim parE, simp_all, elim IdE, simp)
apply(intro compI)
apply(subgoal_tac "<ac, <ac#<bd#bd>>>:lwir(A,B)", simp)
apply(rule lwirI, (elim typ_rels, simp)+)
apply(rule invI, subgoal_tac "<<<ac#bd>#bd>, <ac#<bd#bd>>>:reorg(A,B,B)", simp)
apply(rule reorgI, (elim typ_rels, simp)+, simp_all)
apply(subgoal_tac "\<langle><<ac#bd>#bd>,<<a#bd>#bd>\<rangle> \<in> Fst(B, R)", simp)
apply(rule FstI, rule parI, simp_all, rule IdI, (elim typ_rels, simp)+)
apply(subgoal_tac "\<langle><<a#bd>#bd>,<a#<bd#bd>>\<rangle> \<in> reorg(C, B, B)", simp)
apply(rule reorgI, (elim typ_rels, simp)+)
apply(rule invI, rule lwirI, (elim typ_rels, simp)+, simp_all)
done

lemma loop2_loop2'_iff_typ_sig: 
  "\<lbrakk> R:A*B<~>C*B; loop2'(A,B,C,R):A<~>C; x:loop2'(A,B,C,R) \<rbrakk> \<Longrightarrow> x:loop2(R)"
apply(auto, drule subsetD, simp, safe)
apply(unfold loop2_def loop2'_def)
apply(elim compE, typecheck add: inv_type Fst_type, simp_all)
apply(elim invE, typecheck)
apply(elim sig_pairE, simp)
apply(elim reorgE, simp_all)
apply(elim lwirE, simp_all)
apply(elim FstE parE, simp_all, elim IdE, simp)
apply(intro compI)
apply(subgoal_tac "<ac, <ac#<bd#bd>>>:lwir(ddtyp(R), rdtyp(R))", simp)
apply(rule lwirI, simp_all add: typ_sigs)
apply(rule invI, subgoal_tac "<<<ac#bd>#bd>, <ac#<bd#bd>>>:reorg(ddtyp(R), rdtyp(R), rdtyp(R))", simp)
apply(rule reorgI, simp_all add: typ_sigs)
apply(subgoal_tac "\<langle><<ac#bd>#bd>,<<a#bd>#bd>\<rangle> \<in> Fst(rdtyp(R), R)", simp)
apply(rule FstI, rule parI, simp_all, rule IdI, simp_all add: typ_sigs)
apply(subgoal_tac "\<langle><<a#bd>#bd>,<a#<bd#bd>>\<rangle> \<in> reorg(drtyp(R), rdtyp(R), rdtyp(R))", simp)
apply(rule reorgI, simp_all add: typ_sigs)
apply(rule invI, rule lwirI, simp_all add: typ_sigs)
done

theorem loop2_loop2'_iff: "R:A*B<~>C*B \<Longrightarrow> loop2(R) = loop2'(A,B,C,R)"
apply(rule, rule)
apply(subgoal_tac "loop2(R):ddtyp(R)<~>drtyp(R)")
apply(rule loop2_loop2'_iff_typ_rel, blast+)
defer
apply(rule)
apply(subgoal_tac "loop2'(A,B,C,R):A<~>C")
apply(rule loop2_loop2'_iff_typ_sig, blast+)
apply(unfold loop2'_def loop2_def)
apply(typecheck add: inv_type Fst_type)
done

theorem loop2_type: "\<lbrakk> R:A*B<~>C*B \<rbrakk> \<Longrightarrow> loop2(R):A<~>C"
apply(subst loop2_loop2'_iff, simp)
apply(unfold loop2'_def)
apply(typecheck add: inv_type Fst_type)
done

theorem loop2R: "\<lbrakk> A:ChTy; B:ChTy; C:ChTy; R:A*B<R>C*B \<rbrakk> \<Longrightarrow> loop2(R):A<R>C"
apply(subst loop2_loop2'_iff)
apply(frule rev_subsetD[of R], rule ruby_sub_sig, simp)
apply(unfold loop2'_def)
apply(intro RubyR FstR invR)
apply(((rule lwirR | rule reorgR | rule FstR), simp+)+)
done

theorem loop2_iff: 
  "\<lbrakk> R:A*B<~>C*B; a:sig(A'); c:sig(C') \<rbrakk>
    \<Longrightarrow> <a,c>:loop2(R) \<longleftrightarrow> (EX b:sig(B). <<a#b>, <c#b>>:R)"
apply(subst loop2_loop2'_iff, simp, unfold loop2'_def)
apply(rule)
apply(elim compE, typecheck add: inv_type Fst_type, simp_all)
apply(elim invE, typecheck)
apply(elim sig_pairE, simp)
apply(elim reorgE, simp_all)
apply(elim lwirE, simp_all)
apply(elim FstE parE, simp_all, elim IdE, simp)
apply(rule, simp, simp)
apply(erule bexE)
apply(frule mem_rel_type, simp, erule conjE)
apply(drule spair_type_rev, simp, simp)
apply(drule spair_type_rev, simp)
apply(erule conjE, simp, erule conjE)
apply(intro compI)
apply(subgoal_tac "<a, <a#<b#b>>>:lwir(A,B)", simp)
apply(rule lwirI, simp+)
apply(rule invI, subgoal_tac "<<<a#b>#b>, <a#<b#b>>>:reorg(A,B,B)", simp)
apply(rule reorgI, simp_all)
apply(subgoal_tac "\<langle><<a#b>#b>,<<c#b>#b>\<rangle> \<in> Fst(B, R)", simp)
apply(rule FstI, rule parI, simp_all, rule IdI, simp)
apply(subgoal_tac "\<langle><<c#b>#b>,<c#<b#b>>\<rangle> \<in> reorg(C, B, B)", simp)
apply(rule reorgI, simp_all)
apply(rule invI, rule lwirI, simp_all)
done

theorem loop2I: 
"\<lbrakk> <<a#b>, <c#b>>:R; R:A*B<~>C*B; 
  a:sig(A'); b:sig(B); c:sig(C') \<rbrakk> \<Longrightarrow> <a,c>:loop2(R)"
apply(drule loop2_iff[of _ _ _ _ a _ c _], auto)
done

theorem loop2E: 
  "\<lbrakk> <a,c>:loop2(R);
    \<And>b. \<lbrakk> b:sig(B); <<a#b>,<c#b>>:R \<rbrakk> \<Longrightarrow> P;
    R:A*B<~>C*B; a:sig(A'); c:sig(C') \<rbrakk> \<Longrightarrow> P"
apply(drule loop2_iff[of _ _ _ _ a _ c _], auto)
done

lemma loop4_loop4'_iff_typ_rel:
  "\<lbrakk> R:(A*B)*C<~>De*(E*B); loop4(R):domain(ddtyp(R))*rdtyp(R)<~>drtyp(R)*domain(rrtyp(R));
    x:loop4(R) \<rbrakk> \<Longrightarrow> x:loop4'(A,B,C,De,E,R)"
apply(auto, drule subsetD, simp, safe)
apply(unfold loop4_def loop4'_def)
apply(elim compE, typecheck add: loop2_type inv_type, simp_all)
apply(elim sig_pairE, simp)
apply(erule crossE, simp_all)
apply(erule loop2E, typecheck add: inv_type, simp_all)
apply(erule compE2, typecheck add: inv_type, simp_all)
apply(thin_tac "yb \<in> sig(De \<times> E \<times> B)")
apply(erule invE, typecheck)
apply(elim sig_pairE, simp, erule reorgE, simp_all)
apply(erule compE2, typecheck, simp)
apply(elim sig_pairE, simp)
apply(elim RubyE, typecheck)
apply(elim sig_pairE, simp, elim RubyE, simp_all)
apply(intro RubyI)
apply(subgoal_tac "<<ag#bf>, <bf#ag>>:cross(A, C)", simp)
apply(rule crossI, (elim typ_rels, simp)+, simp)
apply(rule loop2I, typecheck add: inv_type, simp_all)
apply(subgoal_tac 
      "\<langle><<bf#ag>#bh>,<<ac#ad>#bh>\<rangle> \<in> reorg(C, A, B);;cross(C, A \<times> B);;R;;reorg(De, E, B)~", simp)
apply(intro RubyI invI)
apply(subgoal_tac "\<langle><<bf#ag>#bh>,<bf#<ag#bh>>\<rangle> \<in> reorg(C, A, B)", simp)
apply(rule reorgI, (elim typ_rels, simp)+, simp+)
apply(subgoal_tac "\<langle><bf#<ag#bh>>,<<ag#bh>#bf>\<rangle> \<in> cross(C, A \<times> B)", simp)
apply(rule crossI, (elim typ_rels, simp)+, simp+)
apply(rule reorgI, (elim typ_rels, simp)+, simp+)
done

lemma loop4_loop4'_iff_typ_sig:
  "\<lbrakk> R:(A*B)*C<~>De*(E*B); loop4'(A,B,C,De,E,R):A*C<~>De*E;
    x:loop4'(A,B,C,De,E,R) \<rbrakk> \<Longrightarrow> x:loop4(R)"
apply(auto, drule subsetD, simp, safe)
apply(elim sig_pairE, simp)
apply(unfold loop4_def loop4'_def)
apply(elim compE, typecheck add: inv_type loop2_type, simp_all)
apply(elim sig_pairE, simp, elim crossE, simp_all)
apply(elim loop2E, typecheck add: inv_type, simp_all)
apply(erule compE, typecheck add: inv_type, simp)
apply(erule invE, typecheck, elim sig_pairE, simp, erule reorgE, simp_all)
apply(erule compE, typecheck, simp, elim sig_pairE, simp)
apply(erule compE, typecheck, elim sig_pairE, simp, erule crossE, simp_all)
apply(erule reorgE, simp_all)
apply(intro RubyI)
apply(subgoal_tac "<<af#bf>, <bf#af>>:cross(domain(ddtyp(R)), rdtyp(R))", simp)
apply(rule crossI, simp_all add: typ_sigs)
apply(rule loop2I, typecheck add: inv_type, simp_all)
apply(subgoal_tac 
      "\<langle><<bf#af>#bg>,<<ac#ad>#bg>\<rangle> \<in> 
            reorg(rdtyp(R), domain(ddtyp(R)), range(ddtyp(R))) ;; 
            cross(rdtyp(R), domain(ddtyp(R)) \<times> range(ddtyp(R))) ;;
            R ;;
            reorg(drtyp(R), domain(rrtyp(R)), range(ddtyp(R)))~", simp)
apply(intro RubyI invI)
apply(subgoal_tac "\<langle><<bf#af>#bg>,<bf#<af#bg>>\<rangle> \<in> reorg(rdtyp(R), domain(ddtyp(R)), range(ddtyp(R)))", simp)
apply(rule reorgI, (simp add: typ_sigs)+)
apply(subgoal_tac "\<langle><bf#<af#bg>>,<<af#bg>#bf>\<rangle> \<in> cross(rdtyp(R), domain(ddtyp(R)) \<times> range(ddtyp(R)))", simp)
apply(rule crossI, (simp add: typ_sigs)+)
apply(typecheck, (simp add: typ_sigs)+)
apply(rule reorgI, simp_all add: typ_sigs)
done

theorem loop4_loop4'_iff: 
  "R:(A*B)*C<~>De*(E*B) \<Longrightarrow> loop4(R) = loop4'(A,B,C,De,E,R)"
apply(rule, rule)
apply(subgoal_tac "loop4(R):domain(ddtyp(R))*rdtyp(R)<~>drtyp(R)*domain(rrtyp(R))")
apply(rule loop4_loop4'_iff_typ_rel, blast+)
defer
apply(rule)
apply(subgoal_tac "loop4'(A,B,C,De,E,R):A*C<~>De*E")
apply(rule loop4_loop4'_iff_typ_sig, blast+)
apply(unfold loop4'_def loop4_def)
apply(typecheck add: loop2_type inv_type)
done

theorem loop4_type: "\<lbrakk> R:(A*B)*C<~>De*(E*B) \<rbrakk> \<Longrightarrow> loop4(R):A*C<~>De*E"
apply(subst loop4_loop4'_iff, simp)
apply(unfold loop4'_def, typecheck add: inv_type loop2_type)
done

theorem loop4R: 
  "\<lbrakk> A:ChTy; B:ChTy; C:ChTy; De:ChTy; E:ChTy; 
    R:(A*B)*C<R>De*(E*B) \<rbrakk> \<Longrightarrow> loop4(R):A*C<R>De*E"
apply(subst loop4_loop4'_iff)
apply(frule rev_subsetD[of R], rule ruby_sub_sig, simp)
apply(unfold loop4'_def)
apply(intro RubyR loop2R[of _ B])
apply(((rule crossR | rule reorgR | rule invR), simp_all add: prod_in_chty)+)
apply(rule invR, rule reorgR, simp+)
done

theorem loop4_iff:
  "\<lbrakk> R:(A*B)*C<~>De*(E*B); a:sig(A'); c:sig(C'); d:sig(De'); e:sig(E') \<rbrakk>
    \<Longrightarrow> <<a#c>,<d#e>>:loop4(R) \<longleftrightarrow> (EX b:sig(B). <<<a#b>#c>,<d#<e#b>>>:R)"
apply(rule)
apply(unfold loop4_def loop4'_def)
apply(elim compE, typecheck add: loop2_type inv_type, simp_all)
apply(elim sig_pairE, simp)
apply(erule crossE, simp_all)
apply(erule loop2E, typecheck add: inv_type, simp_all)
apply(erule compE2, typecheck add: inv_type, simp_all)
apply(erule invE, typecheck)
apply(elim sig_pairE, simp, erule reorgE, simp_all)
apply(erule compE2, typecheck, simp)
apply(elim sig_pairE, simp)
apply(elim RubyE, typecheck)
apply(elim sig_pairE, simp, elim RubyE, simp_all)
apply(blast)
apply(erule bexE)
apply(intro RubyI)
apply(subgoal_tac "<<a#c>, <c#a>>:cross(domain(ddtyp(R)), rdtyp(R))", simp)
apply(rule crossI, simp_all add: typ_sigs)
apply(rule loop2I, typecheck add: inv_type, simp_all)
apply(subgoal_tac 
      "\<langle><<c#a>#b>,<<d#e>#b>\<rangle> \<in> 
            reorg(rdtyp(R), domain(ddtyp(R)), range(ddtyp(R))) ;; 
            cross(rdtyp(R), domain(ddtyp(R)) \<times> range(ddtyp(R))) ;;
            R ;;
            reorg(drtyp(R), domain(rrtyp(R)), range(ddtyp(R)))~", simp)
apply(intro RubyI invI)
apply(subgoal_tac "\<langle><<c#a>#b>,<c#<a#b>>\<rangle> \<in> reorg(rdtyp(R), domain(ddtyp(R)), range(ddtyp(R)))", simp)
apply(rule reorgI, (simp add: typ_sigs)+)
apply(subgoal_tac "\<langle><c#<a#b>>,<<a#b>#c>\<rangle> \<in> cross(rdtyp(R), domain(ddtyp(R)) \<times> range(ddtyp(R)))", simp)
apply(rule crossI, (simp add: typ_sigs)+)
apply(typecheck, (simp add: typ_sigs)+)
apply(rule reorgI, simp_all add: typ_sigs)
done

theorem loop4I: 
  "\<lbrakk> R:(A*B)*C<~>De*(E*B); a:sig(A'); b:sig(B); c:sig(C');
    d:sig(De'); e:sig(E'); <<<a#b>#c>,<d#<e#b>>>:R \<rbrakk>
    \<Longrightarrow> <<a#c>,<d#e>>:loop4(R)"
apply(drule loop4_iff[of _ _ _ _ _ _ a _ c _ d _ e], auto)
done

theorem loop4E: 
  "\<lbrakk> <<a#c>,<d#e>>:loop4(R);
    R:(A*B)*C<~>De*(E*B); a:sig(A'); c:sig(C'); d:sig(De'); e:sig(E'); 
    \<And>b. \<lbrakk> b:sig(B); <<<a#b>#c>,<d#<e#b>>>:R \<rbrakk> \<Longrightarrow> P \<rbrakk>
    \<Longrightarrow> P"
apply(drule loop4_iff[of _ _ _ _ _ _ a _ c _ d _ e], auto)
done

lemmas SimpComb_type = 
  inv_type Conj_type Fst_type Snd_type
  below_type below_type2 beside_type beside_type2 loop2_type loop4_type

lemmas Ruby_type = Ruby_type SimpComb_type

declare SimpComb_type [TC]

lemmas RubyR = RubyR
  invR ConjR FstR SndR belowR besideR loop2R loop4R

lemmas RubyI = RubyI
  invI ConjI FstI SndI belowI besideI loop2I loop4I

lemmas RubyE = RubyE
  invE ConjE FstE SndE belowE besideE loop2E loop4E

lemmas RubyE2 =
  compE2 belowE2 besideE2


end