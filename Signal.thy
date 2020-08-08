theory Signal
imports Nlist IntExt Hilbert ZF.Univ
begin

consts
  "time" :: "i"
  "sig" :: "i \<Rightarrow> i"
  "BaseChTy" :: "i"

syntax
  "time" :: "i"
translations
  "time"=> "CONST int"

syntax
  "sig" :: "i \<Rightarrow> i"        ("(sig'(_'))" [75] 75)
translations
  "sig(A)" \<rightleftharpoons> "CONST int \<rightarrow> A"

axiomatization where
  nat_in_base: "nat:BaseChTy"

definition ChEl :: "i" where
  "ChEl == univ(Union(BaseChTy))"

definition ChTy :: "i" where
  "ChTy == Pow(ChEl)"

definition spair :: "[i, i] \<Rightarrow> i" ("(<_#/_>)") where
  "<a # b> == (lam t:time. <a`t, b`t>)"

definition scons :: "[i, i, i] \<Rightarrow> i" ("([_@>_|/_])") where
  "[a @> l | n] == (lam t:time. ncons(n, a`t, l`t))"

definition snil :: "i" where
  "snil == (lam t:time. nnil)"

definition sapp :: "[i, i, i, i] \<Rightarrow> i" where
  "sapp(n1, n2, l1, l2) == (lam t:time. napp(n1, n2, l1`t, l2`t))"

definition ssnoc :: "[i, i, i] \<Rightarrow> i" ("([_<@_|/_])") where
  "[l <@ a | n] == (lam t:time. nsnoc(n, l`t, a`t))"

definition pri :: "i \<Rightarrow> i" where
  "pri(a) == (lam t:time. fst(a`t))"

definition sec :: "i \<Rightarrow> i" where
  "sec(a) == (lam t:time. snd(a`t))"

theorem sig_mono: "\<lbrakk> A \<subseteq> B \<rbrakk> \<Longrightarrow> sig(A) \<subseteq> sig(B)"
apply(drule Pi_mono)
apply(simp)
done

theorem sig_sub_func: "\<lbrakk> x:(time \<rightarrow> A); \<And>t. t:int \<Longrightarrow> x`t:B \<rbrakk> \<Longrightarrow> x:(time \<rightarrow> B)"
apply(rule Pi_type, simp+)
done

theorem nlist_in_chty: "\<lbrakk> A:ChTy \<rbrakk> \<Longrightarrow> nlist[n]A:ChTy"
apply(simp add: ChTy_def ChEl_def)
apply(auto simp add: nlist_into_univ)
done

theorem prod_in_chty: "\<lbrakk> A:ChTy; B:ChTy \<rbrakk> \<Longrightarrow> A*B:ChTy"
apply(simp add: ChTy_def ChEl_def)
apply(subgoal_tac "A * B \<subseteq> univ(\<Union>BaseChTy) * univ(\<Union>BaseChTy)")
apply(insert product_univ[of "\<Union>BaseChTy"])
apply(simp add: subset_trans)
apply(auto)
done

theorem spair_chel: "\<lbrakk> a:sig(ChEl); b:sig(ChEl) \<rbrakk> \<Longrightarrow> <a # b>:sig(ChEl)"
apply(simp add: spair_def)
apply(subgoal_tac "(\<lambda>t\<in>time. \<langle>a ` t, b ` t\<rangle>) \<in> sig({\<langle>a ` x, b ` x\<rangle> . x \<in> time})")
apply(subgoal_tac "{\<langle>a ` x, b ` x\<rangle> . x \<in> time} \<subseteq> ChEl")
apply(drule sig_mono)
apply(drule subsetD, simp+)
apply(rule RepFun_subset)
apply(subgoal_tac "a`x : ChEl" "b`x : ChEl")
apply(simp add: ChEl_def Pair_in_univ)
apply((simp add: apply_funtype)+)
apply(rule lam_funtype)
done

theorem spair_type: "\<lbrakk> a:sig(A); b:sig(B) \<rbrakk> \<Longrightarrow> <a # b>:sig(A*B)"
apply(simp add: spair_def)
done

theorem scons_type: "\<lbrakk> a:sig(A); l:sig(nlist[n]A) \<rbrakk> \<Longrightarrow> [a @> l|n]:sig(nlist[succ(n)]A)"
apply(simp add: scons_def)
apply(subgoal_tac "(\<lambda>t\<in>time. ncons(n, a ` t, l ` t)) : sig({ncons(n, a ` t, l ` t) . t \<in> time})")
apply(subgoal_tac "{ncons(n, a ` t, l ` t) . t \<in> time} \<subseteq> nlist[succ(n)]A")
apply(drule sig_mono, drule subsetD, simp+)
apply(rule RepFun_subset, simp)
apply(rule lam_funtype)
done

theorem snil_type: "snil:sig(nlist[0]A)"
apply(simp add: snil_def)
apply(subgoal_tac "(\<lambda>t\<in>time. nnil) : sig({nnil . t \<in> time})")
apply(erule sig_sub_func, simp)
apply(rule lam_funtype)
done

theorem sapp_type: 
  "\<lbrakk> n1:nat; n2:nat; l1:sig(nlist[n1]A); l2:sig(nlist[n2]A) \<rbrakk> \<Longrightarrow> sapp(n1, n2, l1, l2):sig(nlist[n1 #+ n2]A)"
apply(simp add: sapp_def)
apply(subgoal_tac "(\<lambda>t\<in>time. napp(n1, n2, l1 ` t, l2 ` t)) : sig({napp(n1, n2, l1 ` t, l2 ` t) . t \<in> time})")
apply(subgoal_tac "{napp(n1, n2, l1 ` t, l2 ` t) . t \<in> time} \<subseteq> nlist[n1 #+ n2]A")
apply(drule sig_mono, drule subsetD, simp+)
apply(rule RepFun_subset, simp)
apply(rule lam_funtype)
done

theorem ssnoc_type: "\<lbrakk>  n:nat; a:sig(A); l:sig(nlist[n]A) \<rbrakk> \<Longrightarrow> [l <@ a|n]:sig(nlist[succ(n)]A)"
apply(simp add: ssnoc_def)
apply(subgoal_tac "(\<lambda>t\<in>time. nsnoc(n, l ` t, a ` t)) : sig({nsnoc(n, l ` t, a ` t) . t \<in> time})")
apply(subgoal_tac "{nsnoc(n, l ` t, a ` t) . t \<in> time} \<subseteq> nlist[succ(n)]A")
apply(drule sig_mono, drule subsetD, simp+)
apply(rule RepFun_subset, simp)
apply(rule lam_funtype)
done

theorem ssnoc_is_app: "[l <@ a|n] = sapp(n, 1, l, [a @> snil|0])"
apply(simp add: sapp_def ssnoc_def scons_def snil_def)
apply(rule lam_cong, simp)
apply(simp add: ncons_def nnil_def nsnoc_def)
done

theorem spair_iff: 
  "\<lbrakk> x1:sig(A); x2:sig(B); x1a:sig(C); x2a:sig(D) \<rbrakk> 
    \<Longrightarrow> <x1 # x2> = <x1a # x2a> \<longleftrightarrow> x1 = x1a & x2 = x2a"
apply(auto)
apply(simp add: spair_def)
apply(rule fun_extension, simp+)
apply(subgoal_tac "\<langle>x1 ` x, x2 ` x\<rangle> = \<langle>x1a ` x, x2a ` x\<rangle>", simp)
prefer 2
apply(rule fun_extension, simp+)
apply(simp add: spair_def)
apply(subgoal_tac "\<langle>x1 ` x, x2 ` x\<rangle> = \<langle>x1a ` x, x2a ` x\<rangle>", simp)
apply((drule lam_eqE, simp+)+)
done

theorem spairD: 
  "\<lbrakk> <x1 # x2> = <x1a # x2a>; x1:sig(A); x2:sig(B); x1a:sig(C); x2a:sig(D) \<rbrakk> 
    \<Longrightarrow> x1 = x1a & x2 = x2a"
apply(insert spair_iff, simp)
done

theorem spair_inject: 
  "\<lbrakk> <x1 # x2> = <x1a # x2a>; x1:sig(A); x2:sig(B); x1a:sig(C); x2a:sig(D);
    \<lbrakk> x1 = x1a; x2 = x2a \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(drule spairD, simp+)
done

theorem func_nhd_ntl: 
  "\<lbrakk> l:sig(nlist[succ(n)]A) \<rbrakk> 
    \<Longrightarrow> l = (lam t:time. ncons(n, (lam t1:time. nhd(l ` t1)) ` t, 
                                  (lam t1:time. ntl(succ(n), l`t1))`t ))"
apply(rule fun_extension, simp+)
apply(rule nhd_ntl, simp)
done

lemma napp1_to_nsnoc: "napp(n, 1, l, ncons(0, a, nnil)) = nsnoc(n, l, a)"
apply(simp add: nsnoc_def)
done

theorem func_nfront_nlast: 
  "\<lbrakk> l:sig(nlist[succ(n)]A) \<rbrakk> 
    \<Longrightarrow> l = sapp(n, 1, (lam t:time. nfront(succ(n), l`t)), [(lam t:time. nlast(l`t)) @> snil |0])"
apply(rule fun_extension, simp)
apply((simp add: snil_def scons_def sapp_def)+)
apply(subst napp1_to_nsnoc)
apply(rule nlistE2)
apply(subgoal_tac "l ` x : nlist[succ(n)]A", simp+)
apply(rule nsnoc_nfront_nlast[THEN sym], simp+)
done

theorem ssnoc_iff: 
  "\<lbrakk> a:sig(A); b:sig(B); la:sig(nlist[n]C); lb:sig(nlist[n]E) \<rbrakk>
    \<Longrightarrow> ([la <@ a |n] = [lb <@ b |n]) \<longleftrightarrow> (la = lb & a = b)"
apply(auto)
apply(simp add: ssnoc_def)
apply(rule fun_extension, simp+)
apply(drule lam_eqE, simp)
apply(insert nsnoc_iff, simp)
apply(simp add: ssnoc_def)
apply(rule fun_extension, simp+)
apply(drule lam_eqE, simp+)
done

theorem scons_iff: 
  "\<lbrakk> a:sig(A); b:sig(B); la:sig(nlist[n]C); lb:sig(nlist[n]E) \<rbrakk>
    \<Longrightarrow> ([a @> la |n] = [b @> lb |n]) \<longleftrightarrow> (la = lb & a = b)"
apply(auto)
apply(simp add: scons_def)
apply(rule fun_extension, simp+)
apply(drule lam_eqE, simp)
apply(insert ncons_iff, simp)
apply(simp add: scons_def)
apply(rule fun_extension, simp+)
apply(drule lam_eqE, simp+)
done

theorem ssnoc_inject: 
  "\<lbrakk> ([la <@ a |n] = [lb <@ b |n]); a:sig(A); b:sig(B); la:sig(nlist[n]C); lb:sig(nlist[n]E); 
    \<lbrakk>la = lb; a = b\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(insert ssnoc_iff, simp)
done

theorem scons_inject:
  "\<lbrakk> ([a @> la |n] = [b @> lb |n]); a:sig(A); b:sig(B); la:sig(nlist[n]C); lb:sig(nlist[n]E); 
    \<lbrakk>la = lb; a = b\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(insert scons_iff, simp)
done

lemma add_time_const: "\<lbrakk> \<And>x. x:time \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(auto)
done

theorem scons_iff2: 
  "\<lbrakk> a:sig(A); b:sig(B); la:sig(nlist[n]C); lb:sig(nlist[n1]E) \<rbrakk>
    \<Longrightarrow> ([a @> la |n] = [b @> lb |n1]) \<longleftrightarrow> (la = lb & a = b & n = n1)"
apply(auto)
apply(simp add: scons_def)
apply(rule fun_extension, simp+)
apply(drule lam_eqE, simp)
apply(insert ncons_iff2, simp)
apply(simp add: scons_def)
apply(rule fun_extension, simp+)
apply(drule lam_eqE, simp+)
apply(rule add_time_const)
apply(simp add: scons_def)
apply(drule lam_eqE, simp+)
done

theorem sapp_snil:
  "\<lbrakk> l:sig(nlist[n]A) \<rbrakk> \<Longrightarrow> sapp(0, n, snil, l) = l"
apply(simp add: sapp_def snil_def)
done

theorem sapp_scons: 
  "\<lbrakk> a:sig(A); la:sig(nlist[na]A); lb:sig(nlist[nb]A) \<rbrakk> 
    \<Longrightarrow> sapp(succ(na), nb, [a @> la | na], lb) = [a @> sapp(na, nb, la, lb) | (na #+ nb)]"
apply(simp add: sapp_def scons_def)
done

theorem scons_ssnoc: "\<lbrakk> a:sig(A) \<rbrakk> \<Longrightarrow> [a @> snil |0] = [snil <@ a |0]"
apply(simp add: snil_def scons_def ssnoc_def)
apply(rule fun_extension, simp+)
apply(rule ncons_nsnoc, simp)
done

lemma choose_func_type: "\<lbrakk> ALL t:int. EX x:B. P(x, t) \<rbrakk> \<Longrightarrow> (\<lambda>t1\<in>int. Choose({x \<in> B . P(x, t1)})) \<in> sig(B)"
apply(insert lam_funtype[of time "%t. Choose({x:B. P(x, t)})"])
apply(subgoal_tac "{Choose({xa \<in> B . P(xa, x)}) . x \<in> int} \<subseteq> B")
apply(frule sig_mono, auto)
apply(subgoal_tac "{x \<in> B . P(x, _)} \<noteq> 0")
apply(insert Choose_def[of "{a \<in> B . P(a, _)}"], auto)
done

lemma only_itself_set: "a:A \<Longrightarrow> c:{x:A. x=a} \<Longrightarrow> c = a"
apply(auto)
done

lemma choosing_its_own: "a:A \<Longrightarrow> a = Choose({x:A. x=a})"
apply(frule only_itself_set)
apply(insert Choose_def[of "{x \<in> A . x = a}"])
apply(subgoal_tac "{x \<in> A . x = a} \<noteq> 0", assumption, simp_all)
apply(auto)
done

theorem sig_pairE: "\<lbrakk> c:sig(A*B); \<And>a b. \<lbrakk> c = <a # b>; a:sig(A); b:sig(B) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(simp add: spair_def)
apply(subgoal_tac 
      "c = (\<lambda>t\<in>int. 
        \<langle> (\<lambda>t1\<in>time. Choose({x:A. x = fst(c`t1)})) ` t, 
          (\<lambda>t1\<in>time. Choose({x:B. x = snd(c`t1)})) ` t\<rangle>)")
apply(subgoal_tac "(\<lambda>t1\<in>time. Choose({x:A. x = fst(c`t1)})) : sig(A)")
apply(subgoal_tac "(\<lambda>t1\<in>time. Choose({x:B. x = snd(c`t1)})) : sig(B)")
apply(assumption)
apply(rule choose_func_type, auto)
apply(rule choose_func_type, auto)
apply(rule fun_extension, simp+)
apply(subst Pair_fst_snd_eq[of "c`_" A, THEN sym])
apply(frule apply_funtype, simp+, auto)
apply((rule choosing_its_own, simp)+)
done

theorem sig_nlist0E: "\<lbrakk> c:sig(nlist[0]A); c=snil \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(simp add: snil_def)
apply(subgoal_tac "c = (\<lambda>t\<in>int. nnil)", simp)
apply(rule fun_extension, simp+)
apply(frule apply_funtype, simp)
apply(erule nlistE2, simp+)
done

theorem sig_nlistE: 
  "\<lbrakk> c:sig(nlist[succ(n)]A); \<And>a l. \<lbrakk> c = [a @> l | n]; a:sig(A); l:sig(nlist[n]A) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(simp add: scons_def)
apply(subgoal_tac 
      "c = (\<lambda>t\<in>int. 
        ncons(n, (\<lambda>t1\<in>time. Choose({x:A. x = nhd(c`t1)})) ` t, 
          (\<lambda>t1\<in>time. Choose({x:nlist[n]A. x = ntl(succ(n), c`t1)})) ` t))")
apply(subgoal_tac "(\<lambda>t1\<in>time. Choose({x:A. x = nhd(c`t1)})) : sig(A)")
apply(subgoal_tac "(\<lambda>t1\<in>time. Choose({x:nlist[n]A. x = ntl(succ(n), c`t1)})) : sig(nlist[n]A)")
apply(assumption)
apply(rule choose_func_type, auto)
apply(rule choose_func_type, auto)
apply(rule fun_extension, simp+)
apply(frule apply_funtype, simp)
apply(erule nlistE2, simp+)
apply(subst ncons_iff, simp)
apply(subgoal_tac "l = Choose({x \<in> nlist[n']A . x = l})", simp)
apply(rule choosing_its_own, simp, auto)
apply((rule choosing_its_own, simp)+)
done

lemma nfront_nlast: "\<lbrakk> l:nlist[succ(n)]A \<rbrakk> \<Longrightarrow> l = nsnoc(n, nfront(succ(n), l), nlast(l))"
apply(rule nlistE2, simp+)
apply(rule nsnoc_nfront_nlast[THEN sym], simp+)
done

theorem sig_ssnocE:
  "\<lbrakk> x:sig(nlist[succ(n)]A); \<And>a l. \<lbrakk> a:sig(A); l:sig(nlist[n]A); x= [l <@ a |n] \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(simp add: ssnoc_def)
apply(subgoal_tac 
      "x = (\<lambda>t\<in>int. 
        nsnoc(n, (\<lambda>t1\<in>time. Choose({l:nlist[n]A. l = nfront(succ(n), x`t1)})) ` t, 
          (\<lambda>t1\<in>time. Choose({l:A. l = nlast(x`t1)})) ` t))")
apply(subgoal_tac "(\<lambda>t1\<in>time. Choose({l:A. l = nlast(x`t1)})) : sig(A)")
apply(subgoal_tac "(\<lambda>t1\<in>time. Choose({l:nlist[n]A. l = nfront(succ(n), x`t1)})) : sig(nlist[n]A)")
apply(assumption)
apply(rule choose_func_type, auto)
apply(rule choose_func_type, auto)
apply(rule fun_extension, simp+)
apply(frule apply_funtype, simp)
apply(subst nfront_nlast, simp)
apply(subst nsnoc_iff)
apply(erule nfront_type2, auto)
apply(subgoal_tac "nfront(succ(n), x ` xa) = Choose({l \<in> nlist[n]A . l = nfront(succ(n), x ` xa)})")
apply(simp, erule nfront_type2)
apply((rule choosing_its_own, simp)+)
done

theorem pri_iff: "\<lbrakk> a:sig(A) \<rbrakk> \<Longrightarrow> pri(<a # b>) = a"
apply(simp add: spair_def pri_def)
done

theorem sec_iff: "\<lbrakk> b:sig(B) \<rbrakk> \<Longrightarrow> sec(<a # b>) = b"
apply(simp add: spair_def sec_def)
done

lemmas signal_simps = pri_iff sec_iff scons_iff ssnoc_iff
lemmas signalE = 
  spair_inject scons_inject ssnoc_inject sig_pairE
  sig_nlist0E sig_ssnocE succ_nlist zero_nlist 
  ncons_inject nsnoc_inject
lemmas signal_types =
  spair_type scons_type snil_type sapp_type ssnoc_type

lemmas Ruby_type = signal_types Ruby_type

end