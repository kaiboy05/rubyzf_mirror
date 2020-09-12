theory Convolution
imports Retime
begin

definition rdrf :: "[i,i,i] \<Rightarrow> i" where
  "rdrf(B,n,R) == 
    colf(B,n,lam m:nat. (R`m ;; p1(B,nat)~)) ;; p1(B, nlist[n]nat)"

definition sig0 :: "i" where
  "sig0 == (lam t:int. 0)"

definition fork :: "[i,i] \<Rightarrow> i" where
  "fork(A,n) == p1(A, nlist[n]nat)~ ;; row(A,n,p1(A,nat);;dub(A)) ;; p1(nlist[n]A, A)"

theorem rdrf_type: 
  "\<lbrakk> n:nat; R:nat\<rightarrow>A*B<~>B \<rbrakk> \<Longrightarrow> rdrf(B,n,R):nlist[n]A*B<~>B"
apply(unfold rdrf_def)
apply(typecheck)
done

theorem nat_sig: "EX s. s:sig(nat)"
apply(subgoal_tac "sig(nat) \<noteq> 0")
apply(drule Choose_def, rule, simp)
apply(blast)
done

theorem rdrf_zero_iff: 
  "rdrf(B,0,R) = 
    Fst(B,NNIL);;
    cross(nlist[0]rrtyp(\<Union>range(\<lambda>m\<in>nat. R ` m ;; p1(B, nat)~)),B);;
    p1(B,nlist[0]nat)"
apply(unfold rdrf_def)
apply(subst colf_zero_iff, simp)
done

theorem rdrf_zero_iff2:
  "R:nat\<rightarrow>A*B<~>B \<Longrightarrow> rdrf(B,0,R) = 
    Fst(B,NNIL);;cross(nlist[0]nat,B);;p1(B,nlist[0]nat)"
apply(subst rdrf_zero_iff)
apply(intro comp_eq)
apply(rule, auto)
apply(insert cross_type[of "nlist[0]rrtyp(\<Union>range(\<lambda>m\<in>nat. R ` m ;; p1(B, nat)~))" B])
apply(simp, drule subsetD, simp, safe)
apply(elim sig_pairE, simp)
apply(erule crossE, simp_all)
apply(rule crossI, simp_all)
apply(rule nlist_rrtypUR, simp)
apply(typecheck)
apply(insert cross_type[of "nlist[0]nat" B])
apply(simp, drule subsetD, simp, safe)
apply(elim sig_pairE, simp)
apply(erule crossE, simp_all)
apply(rule crossI, simp_all)
apply(elim sig_nlist0E, simp)
done

theorem rdrf_zero: "a:sig(A) \<Longrightarrow> <<snil#a>,a>:rdrf(A,0,Rf)"
apply(subst rdrf_zero_iff)
apply(intro RubyI)
apply(rule parI, rule NNILI)
apply(simp_all, rule IdI, simp_all)
apply(rule crossI, simp_all)
apply(rule p1I, simp_all)
done

theorem rdrf_zeroE: 
  "\<lbrakk> <<snil#a>,b>:rdrf(A,0,Rf); \<lbrakk> a=b \<rbrakk> \<Longrightarrow> P;
    a:sig(A); b:sig(A); Rf:nat\<rightarrow>B*A<~>A \<rbrakk> \<Longrightarrow> P"
apply(subst (asm) rdrf_zero_iff2, typecheck)
apply(elim compE, typecheck)
apply(elim sig_pairE sig_nlist0E, simp)
apply(elim RubyE, typecheck, simp)
done


theorem rdrf_iff:
  "rdrf(B,n,R) = colf(B,n,lam m:nat. (R`m;;p1(B,nat)~));;p1(B,nlist[n]nat)"
apply(unfold rdrf_def, simp)
done

theorem sig0_type[TC]: "sig0 : sig(nat)"
apply(unfold sig0_def, typecheck)
done

theorem rdrf_succ: 
  "\<lbrakk> n:nat; Rf:nat\<rightarrow>A*B<~>B; 
    a:sig(A); bs:sig(B); b0:sig(B); la:sig(nlist[n]A);
    EX bn:sig(B). (<<a#bs>,bn>:Rf`n & <<la#bn>,b0>:rdrf(B,n,Rf)) \<rbrakk>
    \<Longrightarrow> <<[la<@a|n]#bs>,b0>:rdrf(B,succ(n),Rf)"
apply(subst rdrf_iff)
apply(erule bexE, erule conjE)
apply(subst (asm) rdrf_iff)
apply(erule compE, typecheck)
apply(elim sig_pairE, simp)
apply(elim RubyE, typecheck)
apply(intro RubyI)
apply(subgoal_tac "\<langle><[la<@a|n]#bs>, <aa#[b<@sig0|n]>\<rangle> \<in> colf(B, succ(n), \<lambda>m\<in>nat. Rf ` m ;; p1(B, nat)~)")
apply(simp)
apply(subst colf_succ, typecheck, simp)
apply(subgoal_tac "\<langle><a#bs>, <bn#sig0>\<rangle> \<in> Rf ` n ;; p1(B, nat)~")
apply(blast)
apply(intro RubyI, simp)
apply(rule p1I, simp+)
apply(rule p1I, simp+)
done

theorem p1_Snd_lemma: 
  "n:nat \<Longrightarrow> 
    Snd(B,apr(A,n));;p1(B,nlist[succ(n)]A) = p1(B,nlist[n]A*A)"
apply(rule, auto)
apply(subgoal_tac "Snd(B, apr(A, n)) ;; p1(B, nlist[succ(n)]A):B*(nlist[n]A*A)<~>B")
apply(typecheck)
apply(simp, drule subsetD, simp)
apply(safe, elim sig_pairE, simp)
apply(erule compE, typecheck)
apply(elim sig_pairE, simp)
apply(elim RubyE, typecheck, simp_all)
apply(intro RubyI, simp+)
apply(subgoal_tac "p1(B, nlist[n]A \<times> A) : B*(nlist[n]A*A)<~>B")
apply(typecheck)
apply(simp, drule subsetD, simp)
apply(safe, elim sig_pairE, simp)
apply(intro RubyI)
apply(subgoal_tac "\<langle><a#<aa#ba>>, <a#[aa<@ba|n]>\<rangle>:[[Id(B),apr(A, n)]]", simp)
apply(intro RubyI, simp+)
apply(erule p1E, typecheck, simp, rule p1I, simp+)
done

theorem p2_Snd_lemma: 
  "n:nat \<Longrightarrow> 
    Snd(B,p2(nlist[n]A,A) ;; p2(nlist[n]A,A)~) ;;
    p1(B,nlist[n]A*A) = p1(B,nlist[n]A*A)"
apply(rule, auto)
apply(subgoal_tac 
      " Snd(B, p2(nlist[n]A, A);; p2(nlist[n]A, A)~);;
        p1(B, nlist[n]A \<times> A) : B*(nlist[n]A*A)<~>B", typecheck)
apply(simp, drule subsetD, simp)
apply(safe, elim sig_pairE, simp)
apply(elim compE, typecheck)
apply(elim sig_pairE, simp)
apply(erule SndE, erule parE, simp+)
apply(elim RubyE, typecheck, simp)
apply(rule p1I, simp+)
apply(subgoal_tac "p1(B, nlist[n]A \<times> A):B*(nlist[n]A*A)<~>B", typecheck)
apply(simp, drule subsetD, simp)
apply(safe, elim sig_pairE, simp)
apply(erule p1E, typecheck, simp)
apply(intro RubyI)
apply(rule parI, rule IdI, simp)
apply(subgoal_tac "\<langle><aa#ba>, <aa#ba>\<rangle> \<in> p2(nlist[n]A, A) ;; p2(nlist[n]A, A)~")
apply(simp, intro RubyI)
apply((rule p2I, simp+)+)
apply(rule p1I, simp+)
done

theorem rdrf_succ_iff: 
  "\<lbrakk> n:nat; Rf:nat\<rightarrow>A*B<~>B \<rbrakk> \<Longrightarrow>
    rdrf(B,succ(n),Rf) =
    Fst(B,apr(A,n)~) ;; 
    ((rdrf(B,n,Rf);;p1(B,nlist[n]nat)~) || (Rf`n;;p1(B,nat)~)) ;;
    p1(B,nlist[n]nat*nat)"
apply(unfold rdrf_iff)
apply(subst colf_succ_iff, simp+)
apply((subst comp_assoc, typecheck)+)
apply(intro comp_eq)
apply(subst p1_Snd_lemma, simp)
apply(rule, auto)
apply(subgoal_tac 
      "colf(B, n, \<lambda>m\<in>nat. Rf ` m ;; p1(B, nat)~) ||
      (Rf ` n ;; p1(B, nat)~) ;; p1(B, nlist[n]nat \<times> nat) : _<~>B")
apply(typecheck, simp, drule subsetD, simp)
apply(safe, elim sig_pairE, simp)
apply(elim compE, typecheck)
apply(safe, elim sig_pairE, simp)
apply(erule belowE, typecheck)
apply(elim p1E, typecheck)
apply(intro RubyI)
apply(subgoal_tac "\<langle><<aa#ba>#b>,<y#<ac#bc>>\<rangle> \<in>
        (colf(B, n, \<lambda>m\<in>nat. Rf ` m ;; p1(B, nat)~) ;;
        (p1(B, nlist[n]nat) ;; p1(B, nlist[n]nat)~)) ||
        (Rf ` n ;; p1(B, nat)~)", simp)
apply(rule belowI, simp, rotate_tac 13, simp+)
apply(intro RubyI, simp, rule p1I, simp+)
apply(rule p1I, simp+, rule p1I, simp+)
apply(subgoal_tac 
      "(colf(B, n, \<lambda>m\<in>nat. Rf ` m ;; p1(B, nat)~);;
      (p1(B, nlist[n]nat);;p1(B, nlist[n]nat)~)) ||
      (Rf ` n ;; p1(B, nat)~) ;; p1(B, nlist[n]nat \<times> nat) : _<~>B")
apply(typecheck, simp, drule subsetD, simp)
apply(safe, elim sig_pairE, simp)
apply(elim compE, typecheck)
apply(safe, elim sig_pairE, simp)
apply(erule belowE, typecheck)
apply(elim compE, typecheck)
apply(elim sig_pairE, simp)
apply(elim invE, typecheck, elim p1E, typecheck)
apply(intro RubyI)
apply(subgoal_tac "\<langle><<aa#ba>#b>,<y#<be#bc>>\<rangle> \<in>
           colf(B, n, \<lambda>m\<in>nat. Rf ` m ;; p1(B, nat)~) ||
           (Rf ` n ;; p1(B, nat)~)", simp)
apply(rule belowI, simp, rotate_tac 11, simp+)
apply(intro RubyI, simp+)
apply((rule p1I, simp+)+)
done

theorem parId_left: "R:A*B<~>C \<Longrightarrow> [[Id(A), Id(B)]];;R = R"
apply(subst par_Id)
apply(simp)
done

theorem pow_commute_F:
  "\<lbrakk> ALL n:nat. ([[R,R]];;F`n = F`n;;R); 
    R:A<~>A; F:nat\<rightarrow>(A*A)<~>A; n:nat; m:nat \<rbrakk>
  \<Longrightarrow> [[pow(A,n,R), pow(A,n,R)]] ;; F`m = F`m ;; pow(A,n,R)"
apply(induct_tac n)
apply((subst powf_zero_iff)+, simp)
apply(subst Id_right, typecheck)
apply(rule parId_left, typecheck)
apply((subst powf_succ2, simp_all)+)
apply(subst par_comb[THEN sym], typecheck, simp_all)
apply(subst comp_assoc, typecheck, simp_all)
apply(subst comp_assoc[THEN sym], typecheck, simp_all)
apply(subst comp_assoc, typecheck, simp_all)
done

lemma hornerf_zero:
  "\<lbrakk> R \<in> A<~>A; F \<in> nat \<rightarrow> A \<times> A<~>A \<rbrakk> \<Longrightarrow>
    [[tri(A, 0, R),powf(A, 0, \<lambda>_\<in>nat. R)]] ;; rdrf(A, 0, F) =
    rdrf(A, 0, \<lambda>k\<in>nat. Snd(A, R) ;; F ` k)"
apply(subst tri_zero_iff, subst powf_zero_iff)
apply(rule, auto)
apply(subgoal_tac "[[NNIL,Id(A)]] ;; rdrf(A, 0, F) : _<~>_")
apply(typecheck add: rdrf_type, simp, drule subsetD, simp)
apply(safe, elim sig_pairE, simp)
apply(elim compE, typecheck add: rdrf_type)
apply(elim sig_pairE sig_nlist0E, simp)
apply(erule parE, simp+, erule IdE, simp)
apply(elim rdrf_zeroE, simp_all)
apply(rule rdrf_zero, simp)
apply(subgoal_tac "rdrf(A, 0, \<lambda>k\<in>nat. Snd(A, R) ;; F ` k):_<~>_")
apply(typecheck add: rdrf_type, simp, drule subsetD, simp, simp_all)
apply(safe, elim sig_pairE sig_nlist0E, simp)
apply(elim rdrf_zeroE, typecheck, simp_all)
apply(intro RubyI, rule parI, rule NNILI, rule IdI, simp+)
apply(rule rdrf_zero, simp)
done

theorem hornerf: 
  "\<lbrakk> R:A<~>A; F:nat\<rightarrow>(A*A)<~>A; n:nat;
    ALL n:nat. ([[R,R]];;F`n = F`n;;R) \<rbrakk> \<Longrightarrow>
    [[tri(A,n,R), pow(A,n,R)]];;rdrf(A,n,F) =
    rdrf(A,n,lam k:nat.(Snd(A,R);;(F`k)))"
apply(induct_tac n)
apply(rule hornerf_zero, simp+)
apply(drule pow_commute_F, simp+)
apply(subst tri_succ_iff, simp+)
apply(subst rdrf_succ_iff, simp+)
apply(subst Fst_def)
apply((subst comp_assoc[THEN sym], typecheck add: rdrf_type, simp+)+)
apply(subst par_comb, typecheck, simp+)
apply(subst comp_assoc, typecheck, simp+)
apply(subst comp_assoc, typecheck, simp+)
apply(subst comp_assoc, typecheck, simp+)
apply(subst apr_apr_inv_Id)
apply((subst Id_right, typecheck, simp+)+)
apply(subst Fst_par_comp[THEN sym], typecheck, simp+)
apply(subst par_reorg_assoc2, typecheck, simp_all)
apply(subst below_iff2, typecheck add: rdrf_type)
apply(subst rdrf_succ_iff, typecheck, simp+, rule comp_eq)
apply((subst comp_assoc, typecheck add: rdrf_type, simp+)+, rule comp_eq)
apply(subst below_iff2, typecheck add: rdrf_type, simp+)
apply((subst comp_assoc, typecheck add: rdrf_type, simp+)+, rule comp_eq)
apply((subst comp_assoc[THEN sym], typecheck add: rdrf_type, simp+)+, rule comp_eq)
apply(subst Fst_distrib, typecheck add: rdrf_type, simp+)
apply(subst Fst_distrib, typecheck add: rdrf_type)
apply((subst comp_assoc[THEN sym], typecheck add: rdrf_type, simp+)+, rule comp_eq)
apply(subgoal_tac 
      "[[tri(A, x, R),[[powf(A, x, \<lambda>_\<in>nat. R),powf(A, succ(x), \<lambda>_\<in>nat. R)]]]] ;; 
        reorg(nlist[x]A, A, A)~ ;; reorg(nlist[x]A, A, A) =
      [[tri(A, x, R),[[powf(A, x, \<lambda>_\<in>nat. R),powf(A, succ(x), \<lambda>_\<in>nat. R)]]]]", simp,
      thin_tac "[[tri(A, x, R),[[powf(A, x, \<lambda>_\<in>nat. R),powf(A, succ(x), \<lambda>_\<in>nat. R)]]]] ;; 
        reorg(nlist[x]A, A, A)~ ;; reorg(nlist[x]A, A, A) =
      [[tri(A, x, R),[[powf(A, x, \<lambda>_\<in>nat. R),powf(A, succ(x), \<lambda>_\<in>nat. R)]]]]")
apply(subst Snd_def, subst par_comb, typecheck, simp+)
apply(subst Id_right, typecheck, simp+)
apply(subst comp_assoc[of 
        "[[powf(A, _, \<lambda>_\<in>nat. R),powf(A, succ(_), \<lambda>_\<in>nat. R)]]" _ _
        "F`_" _ "p1(A, nat)~", THEN sym], typecheck, simp+)
apply(subst powf_succ2, simp+)
apply(subst Snd_par_comp[of R _ _ "powf(A, _, \<lambda>_\<in>nat. R)" _ "powf(A, _, \<lambda>_\<in>nat. R)",THEN sym],
      typecheck, simp+)
apply(subst comp_assoc[of 
        "Snd(A, R)" _ _ 
        "[[powf(A, _, \<lambda>_\<in>nat. R),powf(A, _, \<lambda>_\<in>nat. R)]]" _
        "F`_"], typecheck, simp+)
apply(subst comp_assoc[of "Snd(A, R)" _ _ "F`_ ;; powf(A, _, \<lambda>_\<in>nat. R)" _ "p1(A, nat)~"],
      typecheck, simp+)
apply(subst comp_assoc[of "F`_" _ _ "powf(A, _, \<lambda>_\<in>nat. R)" _ "p1(A, nat)~"],
      typecheck, simp+)
apply(subst comp_p1_inv, typecheck, simp+)
apply(subst comp_assoc[THEN sym], typecheck, simp+)
apply(subst comp_assoc[THEN sym], typecheck, simp+)
apply(subst Snd_par_comp[THEN sym], typecheck, simp+)
apply((subst comp_assoc, typecheck add: rdrf_type, simp+)+, rule comp_eq)
apply(subst comp_assoc[THEN sym], typecheck add: rdrf_type, simp+)
apply(subst par_Fst_reorg_inv, typecheck, simp+)
apply(subst comp_assoc, typecheck add: rdrf_type, simp+, rule comp_eq)
apply(subst Fst_distrib[THEN sym], typecheck add: rdrf_type, simp+)
apply(subst comp_assoc, typecheck add: rdrf_type, simp+)
apply(subst reorg_reorg_inv_Id2, subst Id_right, typecheck, simp+)
done

theorem map_tri_comm1: 
  "\<lbrakk> R:A<~>A; S:A<~>A; n:nat; R;;S=S;;R \<rbrakk> \<Longrightarrow> tri(A,n,R);;Map(n,S) = Map(n,S);;tri(A,n,R)"
apply(induct_tac n)
apply((subst tri_zero_iff, subst mapf_zero_iff)+, simp)
apply(subst tri_succ_iff, simp+, subst mapf_succ_iff, typecheck, simp+)
apply((subst comp_assoc[THEN sym], typecheck, simp+)+)
apply(subst comp_assoc, typecheck, simp+)
apply(subst comp_assoc, typecheck, simp+)
apply(subst comp_assoc, typecheck, simp+)
apply(subst apr_apr_inv_Id, subst Id_right, typecheck, simp+)
apply(subst comp_assoc, typecheck, simp+)
apply(subst par_comb, typecheck, simp+)
apply(subst tri_succ_iff, simp+, subst mapf_succ_iff, typecheck, simp+)
apply((subst comp_assoc[THEN sym], typecheck, simp+)+, rule comp_eq)
apply((subst comp_assoc, typecheck, simp+)+, rule comp_eq)
apply(subst comp_assoc[THEN sym], typecheck, simp+)
apply(subst comp_assoc[THEN sym], typecheck, simp+)
apply(subst comp_assoc, typecheck, simp+)
apply(subst apr_apr_inv_Id, subst Id_right, typecheck, simp+)
apply(subst par_comb, typecheck, simp+)
apply(subst pow_disturb_lemma, simp+)
done

theorem fork_type: "\<lbrakk> n:nat \<rbrakk> \<Longrightarrow> fork(A,n):A<~>nlist[n]A"
apply(unfold fork_def, typecheck)
done

theorem nat_nlist_sig: "n:nat \<Longrightarrow> EX s. s:sig(nlist[n]nat)"
apply(induct_tac n)
apply(insert snil_type[of nat], blast)
apply(erule exE)
apply(frule ssnoc_type[of _ sig0 nat], simp+, blast)
done

lemma nat_nlist_sig_choose: 
  "n:nat \<Longrightarrow> Choose(sig(nlist[n]nat)):sig(nlist[n]nat)"
apply(drule nat_nlist_sig)
apply(subgoal_tac "sig(nlist[n]nat) \<noteq> 0")
apply(subst Choose_def, auto)
done

theorem row_eq_lemma: 
  "\<lbrakk> n:nat; a:sig(A); b:sig(A) \<rbrakk> \<Longrightarrow>
    ALL l:sig(nlist[n]A). ALL la:sig(nlist[n]nat).
    (<<a#la>,<l#b>>: row(A,n,p1(A,nat);;dub(A)) \<longrightarrow> a = b)"
apply(induct_tac n)
apply(rule, rule, rule)
apply(elim sig_nlist0E, simp, erule rowf_zeroE, 
      simp, simp, simp, simp)
apply(rule, rule, rule)
apply(elim sig_ssnocE, drule bspec, simp, drule bspec, simp+)
apply(elim rowf_succE, typecheck, simp)
apply(elim compE, typecheck)
apply(elim RubyE, typecheck, simp)
done

lemma fork_succ_rowf_lemma:
  "\<lbrakk> a:sig(A); b \<in> sig(A); n:nat \<rbrakk> \<Longrightarrow>
  ALL ba:sig(nlist[n]nat). ALL l:sig(nlist[n]A). 
  \<langle><a#ba>, <l#b>\<rangle> \<in> rowf(A, n, \<lambda>_\<in>nat. p1(A, nat) ;; dub(A)) \<longrightarrow> a = b"
apply(induct_tac n, rule, rule, rule)
apply(elim sig_nlist0E, simp)
apply(erule rowf_zeroE, typecheck)
apply(rule, rule, rule, elim sig_ssnocE)
apply(drule bspec, simp, drule bspec, simp+)
apply(elim rowf_succE, typecheck, simp)
apply(elim RubyE, typecheck, simp)
done

theorem fork_succI:
  "\<lbrakk> <a,l>:fork(A,n); n:nat; l:sig(nlist[n]A); a:sig(A) \<rbrakk> \<Longrightarrow>
    <a,[l<@a|n]>:fork(A,succ(n))"
apply(unfold fork_def)
apply(elim compE, typecheck, elim sig_pairE, simp)
apply(elim RubyE, typecheck, simp+)
apply(intro RubyI, typecheck)
apply(rule p1I, simp)
apply(subgoal_tac "[ba<@sig0|n]:sig(nlist[succ(n)]nat)", simp+)
apply(subst rowf_succ, simp+)
apply(subgoal_tac "\<langle><b#sig0>, <a#a>\<rangle> \<in> p1(A, nat) ;; dub(A)", blast)
apply(subgoal_tac "a = b", simp)
apply(intro RubyI, rule p1I, simp+, rule dubI, simp)
apply(frule row_eq_lemma[of n a A], simp, rotate_tac 5, simp)
apply(drule bspec, simp, drule bspec, simp+)
apply(rule p1I, simp+)
done

theorem fork_succE:
  "\<lbrakk> <a,[l<@b|n]>:fork(A,succ(n)); \<lbrakk> <a,l>:fork(A,n); a=b \<rbrakk> \<Longrightarrow> P;
    n:nat; l:sig(nlist[n]A); a:sig(A); b:sig(A) \<rbrakk> \<Longrightarrow> P"
apply(subst (asm) fork_def)
apply(elim compE, typecheck)
apply(elim sig_pairE, simp)
apply(elim invE p1E, typecheck, simp)
apply(elim sig_ssnocE, simp, elim rowf_succE, typecheck, simp)
apply(elim RubyE, typecheck)
apply(frule row_eq_lemma[of n a A b], simp, simp)
apply(drule bspec, simp, drule bspec, simp, simp)
apply(subgoal_tac "\<langle>ab, la\<rangle> \<in> fork(A, n)", simp)
apply(subst fork_def)
apply(intro RubyI)
prefer 4
apply(simp, rule p1I, simp+)
apply(intro RubyI, simp+)
done

theorem fork_succ_iff: 
  "\<lbrakk> n:nat \<rbrakk> \<Longrightarrow>
    fork(A,succ(n)) = dub(A);;Fst(A,fork(A,n));;apr(A,n)"
apply(rule, auto)
apply(subgoal_tac "fork(A,succ(n)):_<~>_", typecheck add: fork_type, simp)
apply(drule subsetD, simp, safe, elim sig_ssnocE, simp)
apply(elim fork_succE, typecheck, simp)
apply(intro RubyI, rule dubI, simp)
apply(rule parI, simp, rule IdI, simp+, rule aprI, simp+)
apply(subgoal_tac "dub(A) ;; Fst(A, fork(A, n)) ;; apr(A, n):_<~>_")
apply(typecheck add: fork_type, simp, drule subsetD, simp, safe)
apply(elim sig_ssnocE, simp)
apply(elim compE, typecheck add: fork_type, elim sig_pairE, simp)
apply(elim RubyE, typecheck, simp)
apply(rule fork_succI, simp+)
done

lemma fork_zeroE: "<a,b> : fork(A,0) \<Longrightarrow> b = snil"
apply(subgoal_tac "fork(A,0):_<~>_", typecheck add: fork_type)
apply(simp, drule subsetD, simp, safe)
apply(elim sig_nlist0E, simp)
done

lemma fork_zeroI: "a:sig(A) \<Longrightarrow> <a,snil>:fork(A,0)"
apply(unfold fork_def, intro RubyI)
apply(rule p1I, simp, rule snil_type, simp+)
apply(subst rowf_zero, simp+)
apply(intro p1I, simp+)
done

lemma fork_map_lemma:
  "R:A<~>B \<Longrightarrow> R ;; fork(B, 1) = fork(A, 1) ;; mapf(1, \<lambda>_\<in>nat. R)"
apply(rule, auto)
apply(subgoal_tac "R ;; fork(B, 1) : _<~>_", typecheck add: fork_type, simp_all)
apply(drule subsetD, simp, safe)
apply(elim compE, typecheck add: fork_type, simp)
apply(elim sig_ssnocE sig_nlist0E, simp)
apply(elim fork_succE fork_zeroE, simp_all)
apply(intro RubyI, rule fork_succI, rule fork_zeroI, simp+)
apply(subst mapf_succ, typecheck, simp+, rule mapf_zero)
apply(subgoal_tac "fork(A, 1) ;; mapf(1, \<lambda>_\<in>nat. R) : _<~>_",
      typecheck add: fork_type, simp_all)
apply(drule subsetD, simp, safe, elim sig_ssnocE sig_nlist0E, simp)
apply(elim compE, typecheck add: fork_type, simp_all)
apply(elim sig_ssnocE sig_nlist0E, simp)
apply(elim fork_succE, typecheck, simp)
apply(elim mapf_succE, typecheck, simp_all)
apply(intro RubyI, simp)
apply(rule fork_succI, rule fork_zeroI, simp+)
done

theorem fork_map: 
  "\<lbrakk> n:nat; R:A<~>B; function(R) \<rbrakk>
    \<Longrightarrow> 0 < n \<longrightarrow> R;;fork(B,n) = fork(A,n);;Map(n,R)"
apply(case_tac n, simp+)
apply(induct_tac x)
apply(rule fork_map_lemma, simp+)
apply(subst fork_succ_iff, simp)
apply(subst fork_succ_iff, simp) back
apply(subst mapf_succ_iff, typecheck, simp+)
apply((subst comp_assoc[THEN sym], typecheck add: fork_type, simp+)+)
apply(rule comp_eq)
apply(subgoal_tac 
      "dub(A) ;; Fst(A, fork(A, succ(xa))) ;;
       apr(A, succ(xa)) ;; apr(A, succ(xa))~ ;; [[mapf(succ(xa), \<lambda>_\<in>nat. R),R]] =
       dub(A) ;; Fst(A, fork(A, succ(xa))) ;; [[mapf(succ(xa), \<lambda>_\<in>nat. R),R]]", simp)
apply((subst comp_assoc, typecheck add: fork_type, simp+)+)
apply(subst Fst_par_comp, typecheck add: fork_type, simp+)
apply(subgoal_tac 
      "fork(A, succ(xa)) ;; mapf(succ(xa), \<lambda>_\<in>nat. R) = R ;; fork(B, succ(xa))", simp)
apply(subst Fst_par_comp2[THEN sym], typecheck add: fork_type, simp+)
apply((subst comp_assoc[THEN sym], typecheck add: fork_type, simp+)+, rule comp_eq)
apply(rule duplicate, simp+)
apply(subst comp_assoc, typecheck add: fork_type, simp_all)
apply(subst comp_assoc, typecheck add: fork_type, simp_all)
apply(subst comp_assoc[of "apr(A, succ(_))" _ _ "apr(A, succ(_))~", THEN sym],
      typecheck, simp+)
apply(subst apr_apr_inv_Id, subst Id_left, typecheck, simp+)
done

theorem Comp_fE: 
  "\<lbrakk> <x,z>:R;;S; \<And>y. \<lbrakk> <x,y>:R; <y,z>:S \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(unfold comp_def, blast)
done

theorem delayE2: 
  "\<lbrakk> <x,y>:D(A);
    \<And> A. \<lbrakk> ALL t:time. x`t = y`(t $+ $#1); x:sig(A); y:sig(A) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(unfold delay_def, blast)
done

theorem comp_function: 
  "\<lbrakk> function(R); function(S) \<rbrakk> \<Longrightarrow> function(R;;S)"
apply(subst function_def, rule, rule, rule, rule, rule)
apply(elim Comp_fE)
apply((drule function_apply_equality, simp)+, simp)
done

theorem D_function: "function(D(A))"
apply(subst function_def, safe)
apply(elim delayE2)
apply((drule ball_int_minus1)+)
apply(rule fun_extension, simp+)
done

theorem Id_function: "function(Id(A))"
apply(subst function_def, safe)
apply(elim RubyE, simp)
done

theorem pow_function: "\<lbrakk> n:nat; function(R) \<rbrakk> \<Longrightarrow> function(pow(A,n,R))"
apply(induct_tac n)
apply(subst powf_zero_iff, rule Id_function)
apply(subst powf_succ, simp)
apply(rule comp_function, simp+)
done

theorem Conv_cond1:
  "\<lbrakk> r:nat; w:nat \<rbrakk> \<Longrightarrow>
    function(pow(A,r,D(A)) ;; pow(A,r,(pow(A,w,D(A)))))"
apply(rule comp_function)
apply(rule pow_function, simp, rule D_function)
apply(rule pow_function, simp, rule pow_function, simp, rule D_function)
done

theorem Conv_cond2: "\<lbrakk> r:nat \<rbrakk> \<Longrightarrow> function(pow(A,r,D(A)))"
apply(rule pow_function, simp, rule D_function)
done

theorem Conv_cond3: 
  "\<lbrakk> r:nat; w:nat \<rbrakk> \<Longrightarrow>
    pow(A,r,D(A));;pow(A,w,D(A)) = pow(A,w,D(A)) ;; pow(A,r,D(A))"
apply(rule pow_pow_comp_comm, typecheck)
done

theorem Conv_cond4: "D(A) ;; D(A)~ = Id(A)"
apply(rule delay_Id)
done

theorem Conv_cond5: "w:nat \<Longrightarrow> pow(A,w,D(A)) ;; (pow(A,w,D(A)))~ = Id(A)"
apply(induct_tac w)
apply((subst powf_zero_iff)+)
apply(subst Id_inv, rule Id_right, typecheck)
apply((subst powf_succ, simp)+)
apply(subst compinv, typecheck)
apply(subst comp_assoc, typecheck)
apply(subst comp_assoc[of "D(A)" _ _ "D(A)~", THEN sym], typecheck)
apply(subst Conv_cond4, subst Id_left, typecheck)
done

theorem Conv_cond6:
  "\<lbrakk> m:nat; k:nat; Q:nat\<rightarrow>nat\<rightarrow>A*C<~>C \<rbrakk> \<Longrightarrow>
    Q:nat\<rightarrow>nat\<rightarrow>A*C<R>C \<longrightarrow> [[D(A),D(C)]] ;; (Q`k`m) = (Q`k`m);;D(C)"
apply(rule)
apply(subgoal_tac "Q`k`m : A*C<R>C", simp_all)
apply(subst D_eq_parD)
apply(erule retime_D_comm)
done

theorem Conv_cond7:
  "\<lbrakk> w:nat; m:nat; k:nat; Q:nat\<rightarrow>nat\<rightarrow>A*C<~>C; C:ChTy \<rbrakk> \<Longrightarrow>
    Q:nat\<rightarrow>nat\<rightarrow>A*C<R>C \<longrightarrow>
    [[pow(A,w,D(A)), pow(C,w,D(C))]] ;; (Q`k`m) =
    (Q`k`m) ;; pow(C,w,D(C))"
apply(induct_tac w, safe)
apply((subst powf_zero_iff)+)
apply(subst par_Id, subst Id_left, typecheck, 
      subst Id_right, typecheck, simp)
apply(subst powf_succ2, typecheck)
apply(subst powf_succ2, typecheck)
apply(subst par_comb[THEN sym], typecheck)
apply(subst comp_assoc, typecheck, simp)
apply(subst powf_succ, simp)
apply(subst comp_assoc[THEN sym], typecheck) back
apply(subst D_eq_parD)
apply(rule retime_D_comm)
apply(intro RubyR, simp)
apply(rule powfR, simp+)
apply(rule lam_type, intro RubyR, simp)
done

end