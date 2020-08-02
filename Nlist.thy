theory Nlist
imports "ZF-Induct.ListN" ListExt NatExt
begin

definition nlist :: "[i, i] \<Rightarrow> i" ("(nlist[_]/_)" [0, 1000] 85)
where
  "nlist[n]A == {p:listn(A). EX l. p = <n, l>}"

definition nnil :: "i"
where
  "nnil == <0, Nil>"

definition ncons :: "[i, i, i] => i"
where
  "ncons(n, a, l) == <succ(n), Cons(a, snd(l))>"

definition napp :: "[i, i, i, i] \<Rightarrow> i"
where
  "napp(n1, n2, l1, l2) == <n1 #+ n2, snd(l1) @ snd(l2)>"

definition nhd :: "i \<Rightarrow> i"
where
  "nhd(l) == hd(snd(l))"

definition ntl :: "[i, i] \<Rightarrow> i"
where
  "ntl(n, l) == <n #- 1, tl(snd(l))>"

definition nlast :: "i \<Rightarrow> i"
where
  "nlast(l) == hd(rev(snd(l)))"

definition nfront :: "[i, i] \<Rightarrow> i"
where
  "nfront(n, l) == <n #- 1, front(snd(l))>"

definition nsnoc :: "[i, i, i] \<Rightarrow> i"
where
  "nsnoc(n, l, a) == napp(n, 1, l, ncons(0, a, nnil))"

definition nnth :: "[i, i] \<Rightarrow> i"
where
  "nnth(i, l) == hd(drop(i, snd(l)))"

definition nbuild :: "[i, i \<Rightarrow> i] \<Rightarrow> i"
where
  "nbuild(n, p) == rec(n, nnil, %m r. nsnoc(m, r, p(m)))"

theorem listn_sub: "c:listn(A) \<Longrightarrow> c : nat * list(A)"
apply(insert dom_subset[of A])
apply(blast)
done

theorem nlistE: 
  "\<lbrakk> l:nlist[n]A; 
    \<And>la. \<lbrakk> l:listn(A); l = <n, la>; n:nat; la:list(A) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(simp only: nlist_def)
apply(simp, erule conjE)
apply(erule exE)
apply(frule listn_sub, simp)
done

lemma nlist_is_Part: "nlist[n]A = Part(listn(A), %m. <n, m>)"
apply(simp add: nlist_def)
apply(insert Part_def[of "listn(A)" "%m. <n, m>"])
proof -
  assume a: "Part(listn(A), \<lambda>m. \<langle>n, m\<rangle>) \<equiv> {x \<in> listn(A) . \<exists>z. x = \<langle>n, z\<rangle>}"
  then have "Part(listn(A), \<lambda>m. \<langle>n, m\<rangle>) = {p \<in> listn(A) . \<exists>z. p = \<langle>n, z\<rangle>}" by simp
  then show "{p \<in> listn(A) . \<exists>l. p = \<langle>n, l\<rangle>} = Part(listn(A), \<lambda>m. \<langle>n, m\<rangle>)" by simp
qed

theorem nlist_mono: "A \<subseteq> B \<Longrightarrow> nlist[n]A \<subseteq> nlist[n]B"
apply(subst nlist_is_Part)
apply(subst nlist_is_Part)
apply(rule Part_mono)
apply(rule listn_mono, simp)
done

theorem nlist_nat: "x:nlist[n]A \<Longrightarrow> n:nat"
apply(simp add: nlist_def)
apply(erule conjE)
apply(erule exE)
apply(drule listn_sub)
apply(simp)
done

theorem listn_append_induct_lemma: 
  "\<lbrakk> <xa, x> : listn(A); P_listn(0, []); 
    \<And>a n l. \<lbrakk> a:A; <n, l>: listn(A); P_listn(n, l); n:nat;
      l:list(A) \<rbrakk> \<Longrightarrow> P_listn(succ(n), l @ [a]) \<rbrakk> \<Longrightarrow> P_listn(xa, x)"
apply(insert listn_iff[of xa x A], simp, erule conjE)
apply(insert listn_iff[of _ _ A], simp)
apply(insert list_append_induct[of x A "%m. P_listn(length(m), m)"], simp)
done

theorem nnil_type: "nnil : nlist[0]A"
apply(simp add: nnil_def)
apply(simp add: nlist_is_Part)
apply(rule PartI)
apply(rule NilI)
done

theorem ncons_type: "\<lbrakk> l:nlist[n]A; a:A \<rbrakk> \<Longrightarrow> ncons(n, a, l):nlist[succ(n)]A"
apply(erule nlistE)
apply(simp add: nlist_is_Part ncons_def)
apply(rule PartI)
apply(rule ConsI, simp_all)
done

theorem napp_type: 
  "\<lbrakk> la:nlist[na]A; lb:nlist[nb]A \<rbrakk> 
    \<Longrightarrow> napp(na, nb, la, lb):nlist[na #+ nb]A"
apply(elim nlistE)
apply(rename_tac as bs)
apply(simp add: nlist_is_Part napp_def)
apply(rule PartI)
apply(rule listn_append, simp_all)
done

theorem nhd_type: "\<lbrakk> l:nlist[succ(n)]A \<rbrakk> \<Longrightarrow> nhd(l):A"
apply(elim nlistE)
apply(simp add: nhd_def)
apply(rule hd_type, simp)
apply(insert listn_iff[of "succ(n)"], simp)
done

theorem ntl_type: "\<lbrakk> l:nlist[n]A \<rbrakk> \<Longrightarrow> ntl(n, l):nlist[n #- 1]A"
apply(elim nlistE)
apply(simp add: nlist_is_Part ntl_def)
apply(rule PartI)
apply(subst listn_iff, auto)
apply(subst (asm) listn_iff)
apply(frule length_tl, simp)
done

theorem ntl_type2: "\<lbrakk> l:nlist[succ(n)]A \<rbrakk> \<Longrightarrow> ntl(succ(n), l):nlist[n]A"
apply(frule ntl_type)
apply(frule nlist_nat, simp)
done


theorem nlast_type: "\<lbrakk> l:nlist[succ(n)]A \<rbrakk> \<Longrightarrow> nlast(l):A"
apply(elim nlistE)
apply(simp add: nlast_def)
apply(rule hd_type)
apply(rule rev_type, simp)
apply(subst length_rev, auto)
apply(subst (asm) listn_iff, simp)
done

theorem nfront_type: "\<lbrakk> l:nlist[n]A \<rbrakk> \<Longrightarrow> nfront(n, l):nlist[n #- 1]A"
apply(elim nlistE)
apply(simp add: nlist_is_Part nfront_def)
apply(rule PartI)
apply(subst listn_iff, auto)
apply(subst (asm) listn_iff)
apply(insert length_front[of _ A], auto)
done

theorem nfront_type2: "\<lbrakk> l:nlist[succ(n)]A \<rbrakk> \<Longrightarrow> nfront(succ(n), l):nlist[n]A"
apply(frule nfront_type)
apply(frule nlist_nat, simp)
done

theorem nsnoc_type: "\<lbrakk> l:nlist[n]A; a:A \<rbrakk> \<Longrightarrow> nsnoc(n, l, a):nlist[succ(n)]A"
apply(erule nlistE)
apply(simp add: nlist_is_Part nsnoc_def napp_def ncons_def nnil_def)
apply(rule PartI)
apply(subst listn_iff, auto)
apply(subst (asm) listn_iff, auto)
done

theorem nnil_elem: "\<lbrakk> nnil:nlist[n]A; n=0 \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(simp add: nnil_def)
apply(elim nlistE, auto)
done

theorem zero_nlist: "\<lbrakk> x:nlist[0]A; x=nnil \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(elim nlistE)
apply(simp add: nnil_def)
apply(subst (asm) listn_iff, auto)
done

lemma cons_hd_tl: "\<lbrakk> x:list(A); 0 < length(x) \<rbrakk> \<Longrightarrow> x = Cons(hd(x), tl(x))"
apply(case_tac x, simp+)
done

theorem succ_nlist: 
  "\<lbrakk> x:nlist[succ(n)]A;
    \<And>a l. \<lbrakk> a:A; l:nlist[n]A; x=ncons(n, a, l) \<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
apply(frule nhd_type)
apply(frule ntl_type)
apply(frule nlist_nat, simp)
apply(subgoal_tac "x = ncons(n, nhd(x), ntl(succ(n), x))", simp)
apply(elim nlistE)
apply(simp add: ncons_def nhd_def ntl_def listn_iff)
proof -
  fix la laa
  assume a: "la:list(A)" "tl(la) = laa" "length(la) = succ(n)"
  then have "0 < length(la)" by simp
  then have "la = Cons(hd(la), tl(la))" using cons_hd_tl[of la A] a by simp
  then show "la = Cons(hd(la), laa)" using a by simp
qed

lemma hd_length_gt_0: "x:list(A) \<Longrightarrow> 0 < length([hd(x)])"
apply(auto)
done

lemma app_front_last: "\<lbrakk> x:list(A)\<rbrakk> \<Longrightarrow> (x = [] \<longrightarrow> True) & (x \<noteq> [] \<longrightarrow> x = front(x) @ [hd(rev(x))])"
apply(erule list_append_induct, auto)
apply(frule rev_type)
apply(case_tac y, auto)
apply(subst app_Cons[THEN sym])
apply(rule front_app_end[THEN sym], auto)
apply(subst rev_app_distrib, auto)
done

theorem succ_nlist_app: 
  "\<lbrakk> x:nlist[succ(n)]A; 
    \<And> a l. \<lbrakk> a:A; l:nlist[n]A; x = nsnoc(n, l, a) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(frule nfront_type)
apply(frule nlast_type)
apply(frule nlist_nat, simp)
apply(subgoal_tac "x = nsnoc(n, nfront(succ(n), x), nlast(x))", simp)
apply(elim nlistE)
apply(simp add: nsnoc_def ncons_def napp_def nlast_def nnil_def nfront_def)
proof -
  fix la laa
  assume a: "la:list(A)" "front(la) = laa" "\<langle>succ(n), la\<rangle> : listn(A)"
  then have "length(la) = succ(n)" using listn_iff by simp
  then have "la ~= []" using a by(auto)
  then have "la = front(la) @ [hd(rev(la))]" using app_front_last[of la A] a by simp
  then show "la = laa @ [hd(rev(la))]" using a by simp
qed

theorem ncons_iff: 
  "\<lbrakk> l:nlist[n]A; l':nlist[n]B \<rbrakk> 
    \<Longrightarrow> (ncons(n, a, l) = ncons(n, a', l') \<longleftrightarrow> (l = l' & a = a'))"
apply(elim nlistE)
apply(simp add: ncons_def, auto)
done

theorem ncons_inject: 
  "\<lbrakk> ncons(n, a, l) = ncons(n, a', l'); l:nlist[n]A; l':nlist[n]B;
    \<lbrakk> l = l'; a = a' \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
apply(frule ncons_iff[of l n A "l'" B], auto)
done

lemma ncons_n_iff_lemma: "\<lbrakk>l \<in> nlist[n]A; l' \<in> nlist[n']B; ncons(n, a, l) = ncons(n', a', l')\<rbrakk> \<Longrightarrow> n = n'"
apply(elim nlistE)
apply(simp add: ncons_def)
done

theorem ncons_iff2:
  "\<lbrakk> l:nlist[n]A; l':nlist[n']B \<rbrakk> \<Longrightarrow> (ncons(n, a, l) = ncons(n', a', l')) \<longleftrightarrow> (l = l' & a = a' & n = n')"
apply(auto)
apply(frule ncons_n_iff_lemma[of l n A "l'" "n'" B], auto)
apply(insert ncons_iff, auto)
apply(frule ncons_n_iff_lemma[of l n A "l'" "n'" B], auto)
apply(insert ncons_iff, auto)
apply(rule ncons_n_iff_lemma, auto)
done

theorem ncons_inject2: 
  "\<lbrakk> ncons(n, a, l) = ncons(n', a', l'); l:nlist[n]A; l':nlist[n']B; 
    \<lbrakk> l = l'; a = a'; n = n' \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
apply(frule ncons_iff2[of l n A "l'" "n'" B], auto)
done

theorem ncons_inj1: "\<lbrakk> ncons(n, a, l) = ncons(n, a', l') \<rbrakk> \<Longrightarrow> a = a'"
apply(simp add: ncons_def)
done

theorem ncons_inj2: "\<lbrakk> ncons(n, a, l) = ncons(n, a', l'); l:nlist[n]A; l':nlist[n]B \<rbrakk> \<Longrightarrow> l = l'"
apply(frule ncons_iff2[of l n A "l'" "n" B], auto)
done

theorem nsnoc_inject: 
  "\<lbrakk> nsnoc(n, l, a) = nsnoc(n, l', a'); a:A; a':B; l:nlist[n]C; l':nlist[n]E;
    \<lbrakk> l = l'; a = a' \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
apply(simp add: nsnoc_def napp_def)
apply(elim nlistE, simp add: ncons_def nnil_def)
proof -
  fix la laa
  assume a: "la @ [a] = laa @ [a']" "la:list(C)" "laa:list(E)" "a:A" "a':B"
      and b: "\<lbrakk>la = laa; a = a'\<rbrakk> \<Longrightarrow> R"
  then have "rev(la @ [a]) = rev(laa @ [a'])" by simp
  then have "la = laa & a = a'" using rev_app_end[of la C laa E a A "a'" B] a by simp
  then show R using b by simp
qed

theorem nsnoc_iff: 
  "\<lbrakk> l:nlist[n]A; l':nlist[n]B; a:C; a':E \<rbrakk> \<Longrightarrow>
    (nsnoc(n, l, a) = nsnoc(n, l', a')) \<longleftrightarrow> (l = l' & a = a')"
apply(auto)
apply(erule nsnoc_inject, auto)
apply(erule nsnoc_inject, auto)
done

theorem nhd_ncons: "l:nlist[n]A \<Longrightarrow> nhd(ncons(n, a, l)) = a"
apply(elim nlistE)
apply(simp add: nhd_def ncons_def)
done

theorem ntl_nnil: "ntl(0, nnil) = nnil"
apply(simp add: ntl_def nnil_def)
done

theorem ntl_ncons: "\<lbrakk> l:nlist[n]A \<rbrakk> \<Longrightarrow> ntl(succ(n), ncons(n, a, l)) = l"
apply(elim nlistE)
apply(simp add: ntl_def ncons_def)
done

theorem napp_nnil: "l:nlist[n]A \<Longrightarrow> napp(0, n, nnil, l) = l"
apply(elim nlistE)
apply(simp add: napp_def nnil_def)
done

theorem napp_ncons: 
  "\<lbrakk> la:nlist[na]A; lb:nlist[nb]B \<rbrakk> \<Longrightarrow> 
    napp(succ(na), nb, ncons(na, a, la), lb) = ncons(na #+ nb, a, napp(na, nb, la, lb))"
apply(elim nlistE)
apply(simp add: napp_def ncons_def )
done

theorem nfront_nnil: "nfront(0, nnil) = nnil"
apply(simp add: nfront_def nnil_def)
done

theorem nfront_ncons1: "nfront(1, ncons(0, a, nnil)) = nnil"
apply(simp add: nfront_def nnil_def ncons_def)
done

theorem nfront_ncons2: "nfront(succ(1), ncons(1, a, ncons(0, b, nnil))) = ncons(0, a, nnil)"
apply(simp add: nfront_def nnil_def ncons_def)
done

theorem nfront_napp_end: 
  "\<lbrakk> l:nlist[n]A; a:A; b:A \<rbrakk> 
    \<Longrightarrow> nfront(succ(n) #+ 1, nsnoc(succ(n), ncons(n, a, l), b)) = ncons(n, a, l)"
apply(elim nlistE)
apply(simp add: nfront_def nsnoc_def ncons_def nnil_def napp_def)
apply(subst app_Cons[THEN sym])
apply(rule front_app_end, auto)
done

theorem nfront_ncons3: 
  "\<lbrakk> l:nlist[n]A; a:A; b:A \<rbrakk> \<Longrightarrow> 
    nfront(succ(succ(n)), ncons(succ(n), a, ncons(n, b, l))) = 
    ncons(n, a, nfront(succ(n), ncons(n, b, l)))"
apply(elim nlistE)
apply(simp add: nfront_def nsnoc_def ncons_def nnil_def napp_def)
done

theorem ncons_nsnoc: "a:A \<Longrightarrow> ncons(0, a, nnil) = nsnoc(0, nnil, a)"
apply(simp add: ncons_def nsnoc_def nnil_def napp_def)
done

theorem nsnoc_nfront_nlast: 
  "\<lbrakk> l:nlist[n]A; a:A \<rbrakk> 
    \<Longrightarrow> nsnoc(n, nfront(succ(n), ncons(n, a, l)), nlast(ncons(n, a, l))) = ncons(n, a, l)"
apply(elim nlistE)
apply(simp add: nsnoc_def nfront_def ncons_def napp_def nnil_def)
apply(unfold nlast_def snd_conv)
apply(insert app_front_last[of "Cons(a, _)"], auto)
done

theorem nnth_type: "\<lbrakk> 0 < n; l:nlist[n]A; i:nats(n) \<rbrakk> \<Longrightarrow> nnth(i, l):A"
apply(elim nlistE)
apply(simp add: nnth_def)
apply(rule hd_type)
apply(rule drop_type, auto)
apply(subst (asm) listn_iff, simp)
done

theorem nnth_0_nsnoc: "p:A \<Longrightarrow> nnth(0, nsnoc(0, nnil, p)) = p"
apply(simp add: nnth_def nsnoc_def nnil_def napp_def ncons_def)
done

theorem nnth_nsnoc: "\<lbrakk> l:nlist[n]A; a:A \<rbrakk> \<Longrightarrow> nnth(n, nsnoc(n, l, a)) = a"
apply(elim nlistE)
apply(simp add: nnth_def nsnoc_def nnil_def napp_def ncons_def)
apply(subst (asm) listn_iff, simp)
apply(subst drop_append, auto)
done

theorem nnth_nsnoc_lt: "\<lbrakk> l:nlist[n]A; a:A; j < n \<rbrakk> \<Longrightarrow> nnth(j, nsnoc(n, l, a)) = nnth(j, l)"
apply(elim nlistE)
apply(simp add: nnth_def nsnoc_def nnil_def napp_def ncons_def)
apply(subst (asm) listn_iff, simp)
apply(subgoal_tac "j:nat")
apply(subst drop_append[of j _ A], auto)
apply(subgoal_tac "j #- length(la) = 0", auto)
apply(rule hd_append, auto)
apply(subgoal_tac "\<exists>z zs. drop(j, la) = Cons(z, zs)", simp)
apply(rule drop_length[of _ A], simp)
apply(erule ltD)
apply(rule nat_lt_imp_diff_eq_0, auto)
apply(rule lt_nat_in_nat, simp+)
done

theorem nbuild_type: "\<lbrakk> n:nat; \<And>j. j:nat \<Longrightarrow> p(j):A \<rbrakk> \<Longrightarrow> nbuild(n, p):nlist[n]A"
apply(subst nlist_is_Part)
apply(simp add: nbuild_def)
apply(rule rec_type[of n _ "%m. Part(listn(A), Pair(m))"], auto)
apply(subst nlist_is_Part[THEN sym], simp add: nnil_type)
apply(subst nlist_is_Part[THEN sym])
apply(rule nsnoc_type)
apply(subst nlist_is_Part)
apply(rule PartI, simp+)
done

theorem build_0: "nbuild(0, p) = nnil"
apply(simp add: nbuild_def)
done

theorem build_succ: "nbuild(succ(n), p) = nsnoc(n, nbuild(n, p), p(n))"
apply(simp add: nbuild_def)
done

lemma nbuild_def_equality: "nbuild(n, p) = rec(n, nnil, \<lambda>m r. nsnoc(m, r, p(m)))"
apply(simp add: nbuild_def)
done

theorem build_succ_lt: 
  "\<lbrakk> 0 < n; j < n; n:nat; \<And>j. j:nat \<Longrightarrow> p(j):A \<rbrakk>
    \<Longrightarrow> nnth(j, nbuild(succ(n), p)) = nnth(j, nbuild(n, p))"
apply(simp add: nbuild_def)
apply(insert nnth_nsnoc_lt[of "rec(n, nnil, \<lambda>m r. nsnoc(m, r, p(m)))" "n" A "p(n)" j])
apply(subgoal_tac "rec(n, nnil, \<lambda>m r. nsnoc(m, r, p(m))) \<in> nlist[n]A")
apply(frule leI) back
apply(simp)
apply(insert nbuild_def_equality[of n p, THEN sym], simp)
apply(rule nbuild_type, simp+)
done

theorem build_succ_eq: 
  "\<lbrakk> n:nat; \<And>j. j:nat \<Longrightarrow> p(j):A \<rbrakk>
    \<Longrightarrow> nnth(n, nbuild(succ(n), p)) = p(n)"
apply(simp add: nbuild_def)
apply(rule nnth_nsnoc)
apply(insert nbuild_def_equality[of n p, THEN sym], simp)
apply(rule nbuild_type, auto)
done

lemma nnth_build_lemma: 
  "\<lbrakk> n:nat; \<And>j. j:nat \<Longrightarrow> p(j):A \<rbrakk>
    \<Longrightarrow> (n \<le> j \<longrightarrow> True) & (j < n \<longrightarrow>nnth(j, nbuild(n, p)) = p(j))"
apply(induct_tac n, simp_all)
apply(rule impI)
apply(insert le_iff[of j ], simp, erule disjE)
apply(simp)
proof -
  fix x
  assume a: "\<And>j. j \<in> nat \<Longrightarrow> p(j) \<in> A" "x \<in> nat" "j < x"
    and b: "nnth(j, nbuild(x, p)) = p(j)"
  then have "0 < x" using lt_imp_0_lt[of j x] by simp
  then have "nnth(j, nbuild(succ(x), p)) = nnth(j, nbuild(x, p))"
    using build_succ_lt[of x j p A] using a by simp
  then show "nnth(j, nbuild(succ(x), p)) = p(j)" using b by simp
next
  fix x
  assume a: "\<And>j. j \<in> nat \<Longrightarrow> p(j) \<in> A" "x \<in> nat" "j = x"
  then have "nnth(x, nbuild(succ(x), p)) = p(x)" using build_succ_eq[of x p A] by simp
  then show "nnth(j, nbuild(succ(x), p)) = p(j)" using a by simp
qed

theorem nnth_build: 
  "\<lbrakk> n:nat; 0 < n; j:nats(n); \<And>j. j:nat \<Longrightarrow> p(j):A \<rbrakk>
    \<Longrightarrow> nnth(j, nbuild(n, p)) = p(j)"
apply(simp)
apply(frule nnth_build_lemma[of n p A j], simp+)
done

lemma nnth_nlist_lemma:
  "n:nat \<Longrightarrow> ALL xa x. ( 0 < n & xa:nlist[n]A & x:nlist[n]A & 
    (ALL j:nats(n). nnth(j, xa) = nnth(j, x)) ) \<longrightarrow> xa = x"
apply(induct_tac n, simp)
apply(intro allI)
apply(rule impI)
apply(elim conjE)
apply(elim succ_nlist_app)
apply(simp only: nsnoc_iff)
apply(rule conjI)
apply(erule leE)
prefer 2
apply(simp)
apply(elim zero_nlist, simp)
proof -
  fix x xa xb a l aa la
  assume a: "x:nat" "0 < x" "a:A" "l:nlist[x]A" "aa:A" "la:nlist[x]A"
      and b: "xa = nsnoc(x, l, a)" "xb = nsnoc(x, la, aa)"
      and c: "\<forall>j\<in>nats(succ(x)). nnth(j, nsnoc(x, l, a)) = nnth(j, nsnoc(x, la, aa))"
      and h: "\<forall>xa xb. 0 < x \<and> xa \<in> nlist[x]A \<and> xb \<in> nlist[x]A \<and> (\<forall>j\<in>nats(x). nnth(j, xa) = nnth(j, xb)) \<longrightarrow> xa = xb"
  have d: "\<forall>j\<in>nat. j < succ(x) \<longrightarrow> nnth(j, nsnoc(x, l, a)) = nnth(j, nsnoc(x, la, aa))" using c by simp
  {
    fix j
    assume aa: "j:nat" "j < x"
    then have "j < succ(x)" using add_lt_larger_side_help[of x j 1] a by simp
    then have "nnth(j, nsnoc(x, l, a)) = nnth(j, nsnoc(x, la, aa))" using d aa by simp
    then have "nnth(j, l) = nnth(j, nsnoc(x, la, aa))" 
      using nnth_nsnoc_lt[of l x A a j] aa a by simp
    then have "nnth(j, l) = nnth(j, la)" 
      using nnth_nsnoc_lt[of la x A aa j] aa a by simp
  } then have "\<forall>j\<in>nats(x). nnth(j, l) = nnth(j, la)" by simp
  then show "l = la" using h a by(auto)
next
  fix x xa xb a l aa la
  assume a: "x:nat" "a:A" "l:nlist[x]A" "aa:A" "la:nlist[x]A"
      and b: "\<forall>j\<in>nats(succ(x)). nnth(j, nsnoc(x, l, a)) = nnth(j, nsnoc(x, la, aa))"
  then have "x < succ(x)" by simp
  then have "nnth(x, nsnoc(x, l, a)) = nnth(x, nsnoc(x, la, aa))" using b a by simp
  then have "a = nnth(x, nsnoc(x, la, aa))" using nnth_nsnoc[of l x A a] a by simp
  then show "a = aa" using nnth_nsnoc[of la x A aa] a by simp
qed

theorem nnth_nlist:
  "\<lbrakk> n:nat; 0 < n; xa:nlist[n]A; x:nlist[n]A;
    ALL j:nats(n). nnth(j, xa) = nnth(j, x) \<rbrakk> \<Longrightarrow> xa = x"
apply(insert nnth_nlist_lemma[of n A], blast)
done

theorem nhd_ntl: "\<lbrakk> l:nlist[succ(n)]A \<rbrakk> \<Longrightarrow> l = ncons(n, nhd(l), ntl(succ(n), l))"
apply(elim nlistE)
apply(simp add: ncons_def nhd_def ntl_def) 
apply(rule cons_hd_tl[of _ A], simp)
apply(subst (asm) listn_iff, simp)
done

theorem nlist_into_univ: "\<lbrakk> l:nlist[n]A; A \<subseteq> univ(B) \<rbrakk> \<Longrightarrow> l:univ(B)" 
apply(elim nlistE)
apply(drule list_into_univ, simp)
apply(insert nat_subset_univ[of B])
apply(subgoal_tac "n:univ(B)")
apply(subgoal_tac "<n, la>: univ(B) \<times> univ(B)")
apply(subgoal_tac "<n, la>: univ(B)")
apply(simp)
apply(insert product_univ[of B])
apply(insert subsetD[of "univ(B) \<times> univ(B)" "univ(B)" "<n, _>"], simp)
apply(simp)
apply(insert subsetD, simp)
done

theorem nnil_ncons_iff: "~nnil = ncons(n, a, l)"
apply(simp add: nnil_def ncons_def)
done

theorem nlistE2: 
  "\<lbrakk> x:nlist[n]A; \<lbrakk> n = 0; x = nnil \<rbrakk> \<Longrightarrow> P; 
    \<And> n' a l. \<lbrakk> x = ncons(n', a, l); n=succ(n'); a:A; l:nlist[n']A \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(subgoal_tac "n = 0 | n ~= 0")
apply(erule disjE)
apply(simp_all)
apply(erule zero_nlist, simp)
apply(frule nlist_nat)
apply(case_tac n, simp)
apply(simp)
apply(erule succ_nlist, simp)
done

theorem nlist_n_eq_n': "\<lbrakk> l:nlist[n]A; l:nlist[n']A' \<rbrakk> \<Longrightarrow> n = n'"
apply(elim nlistE)
apply(simp)
done

lemmas nlist_types =
  ncons_type nnil_type napp_type nhd_type nsnoc_type
  ntl_type2 ntl_type nlast_type nfront_type2 nfront_type

lemmas Ruby_type =
  nlist_types arith_typechecks

lemmas nlist_simps =
  nhd_ncons ntl_nnil ntl_ncons napp_nnil napp_ncons
  nfront_nnil nfront_ncons1 nfront_ncons2 nfront_ncons3

lemmas nlist_ss =
  nlist_simps nlist_types

declare nlist_ss [simp]

end


