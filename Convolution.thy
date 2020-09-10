theory Convolution
imports Retime
begin

definition rdrf :: "[i,i,i] \<Rightarrow> i" where
  "rdrf(B,n,R) == 
    colf(B,n,lam m:nat. (R`m ;; p1(B,nat)~)) ;; p1(B, nlist[n]nat)"

definition sig0 :: "i" where
  "sig0 == (lam t:int. 0)"

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



find_theorems name: comp_right_eq

end