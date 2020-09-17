theory ExpComb
imports Convolution
begin

consts power :: "[i,i] \<Rightarrow> i" (infixr "#'^" 69)
primrec
  "a #^ 0 = 1"
  "a #^ (succ(b)) = a #* (a #^ b)"

theorem power_type[TC]: "b:nat \<Longrightarrow> a #^ b : nat"
apply(induct_tac b)
apply(simp+)
done

theorem power_distrib: "\<lbrakk> b:nat; c:nat \<rbrakk> \<Longrightarrow> a #^ (b #+ c) = (a #^ b) #* (a #^ c)"
apply(induct_tac c)
apply(simp)
apply(subst add_succ_right, simp)
done

definition half :: "[i,i] \<Rightarrow> i" where
  "half(A, n) == rapp(A, 2 #^ n, 2 #^ n)~"

lemma napp_iff_lemma: 
  "\<lbrakk> m:nat; n:nat \<rbrakk> \<Longrightarrow> 
    ALL la:nlist[m]A. ALL lb:nlist[n]A. 
    ALL la':nlist[m]A. ALL lb':nlist[n]A. 
    napp(m,n,la,lb) = napp(m,n,la',lb') \<longrightarrow> la = la' & lb = lb'"
apply(induct_tac m)
apply(rule, rule, rule, rule, rule)
apply(elim zero_nlist, simp)
apply(rule, rule, rule, rule, rule)
apply(elim succ_nlist, simp)
apply(drule bspec, simp)
apply(drule bspec, simp)
apply(drule bspec, rotate_tac 9, simp)
apply(drule bspec, rotate_tac 3, simp)
apply(erule ncons_inject, simp+)
done

theorem napp_iff: 
  "\<lbrakk> napp(m,n,la,lb) = napp(m,n,la',lb'); 
    la:nlist[m]A; lb:nlist[n]A; la':nlist[m]A; lb':nlist[n]A \<rbrakk> \<Longrightarrow> la = la' & lb = lb'"
apply(frule nlist_nat[of _ m], frule nlist_nat[of _ n])
apply(drule napp_iff_lemma, simp, blast)
done

theorem rapp_type[TC]: "rapp(A,m,n) : nlist[m]A*nlist[n]A <~>nlist[m #+ n]A"
apply(unfold rapp_def)
apply(typecheck, blast)
done

theorem rappR: "A:ChTy \<Longrightarrow> rapp(A,m,n) : nlist[m]A*nlist[n]A <R> nlist[m #+ n]A"
apply(unfold rapp_def)
apply(rule spreadR)
apply(intro prod_in_chty nlist_in_chty, simp+)
apply(rule nlist_in_chty, simp, blast)
done

theorem rappI: 
  "\<lbrakk> la:sig(nlist[m]A); lb:sig(nlist[n]A) \<rbrakk> \<Longrightarrow> 
    <<la#lb>, sapp(m,n,la,lb)>:rapp(A,m,n)"
apply(unfold rapp_def sapp_def)
apply(rule spreadI, rule+, typecheck, simp)
apply(subgoal_tac "<la#lb>`t = <la`t, lb`t>", simp)
apply(erule spair_apply_time)
apply(blast)
done

theorem rappE:
  "\<lbrakk> <<la#lb>, sapp(m,n,la',lb')>:rapp(A,m,n);
    la:sig(nlist[m]A); lb:sig(nlist[n]A); 
    la':sig(nlist[m]A); lb':sig(nlist[n]A);
    \<lbrakk> la = la'; lb = lb' \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(unfold sapp_def rapp_def)
apply(erule spreadE, simp)
apply(subgoal_tac "la=la' & lb=lb'", simp, rule conjI)
apply((rule fun_extension, simp, simp,
      drule bspec, simp,
      (subst (asm) spair_apply_time, simp)+, simp, elim conjE,
      drule napp_iff, typecheck, simp)+)
done

theorem half_type: 
  "half(A,n) : nlist[2#^(succ(n))]A <~> nlist[2#^n]A * nlist[2#^n]A"
apply(unfold half_def)
apply(typecheck)
apply(insert rapp_type[of A "2 #^ n" "2 #^ n"])
apply(simp)
done

theorem halfR:
  "A:ChTy \<Longrightarrow> half(A,n) : nlist[2#^(succ(n))]A <R> nlist[2#^n]A * nlist[2#^n]A"
apply(unfold half_def)
apply(intro RubyR)
apply(insert rappR[of A "2 #^ n" "2 #^ n"], simp)
done

theorem halfI:
  "\<lbrakk> n:nat; la:sig(nlist[2#^n]A); lb:sig(nlist[2#^n]A) \<rbrakk> \<Longrightarrow> 
    <sapp(2#^n, 2#^n, la, lb), <la#lb>>:half(A,n)"
apply(unfold half_def)
apply(intro invI rappI, typecheck)
done

theorem halfE:
  "\<lbrakk> <sapp(2#^n, 2#^n, la, lb), <la'#lb'>>:half(A,n);
    la:sig(nlist[2#^n]A); lb:sig(nlist[2#^n]A);
    la':sig(nlist[2#^n]A); lb':sig(nlist[2#^n]A);
    \<lbrakk> la = la'; lb = lb' \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(unfold half_def)
apply(elim invE rappE, typecheck, simp)
done

end