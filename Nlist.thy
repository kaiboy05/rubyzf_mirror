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





end


