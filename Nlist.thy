theory Nlist
imports "ZF-Induct.ListN" listext natext
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




find_theorems name: app iff

end


