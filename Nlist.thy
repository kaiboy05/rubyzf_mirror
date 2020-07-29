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



end


