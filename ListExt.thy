theory ListExt
imports ZF.List 
begin

definition front :: "i \<Rightarrow> i" where
  "front(l) == rev( tl( rev(l) ) )"

declare leI [simp]
declare length_type [simp]
declare rev_type [simp]
declare tl_type [simp]

theorem rev_app_disturb: "\<lbrakk> xs: list(A); ys: list(B) \<rbrakk> \<Longrightarrow> rev(xs@ys) = rev(ys)@rev(xs)"
by(induct_tac xs, auto simp add: app_assoc)

lemma all_drop_length_Cons_t: "xs: list(A) \<Longrightarrow> ALL x. EX z. EX zs:list(A). drop( length(xs), Cons(x, xs) ) = Cons(z, zs)"
by(induct_tac xs, auto)

theorem drop_length_Cons_t: "xs: list(A) \<Longrightarrow> EX z. EX zs:list(A). drop( length(xs), Cons(x, xs) ) = Cons(z, zs)"
by(simp add: all_drop_length_Cons_t)

lemma in_length_in_nat[simp]: "\<lbrakk> l:list(A); i:length(l) \<rbrakk> \<Longrightarrow> (i:nat)"
proof -
  assume a: "l:list(A)" "i:length(l)"
  then have b: "length(l):nat" using length_type by simp
  then have "i < length(l)" using a lt_def by simp
  then show ?thesis using b lt_nat_in_nat by simp
qed

theorem drop_length_t: "\<lbrakk> l:list(A); i:length(l) \<rbrakk> \<Longrightarrow> EX z. EX zs:list(A). drop(i, l) = Cons(z, zs)"
proof -
  assume a: "l:list(A)" "i:length(l)"
  then have "EX z. EX zs. drop(i, l) = Cons(z, zs)" using drop_length by(auto)
  then obtain z where "EX zs. drop(i, l) = Cons(z, zs)" ..
  then obtain zs where b: "drop(i, l) = Cons(z, zs)" ..
  have "i:nat" using a in_length_in_nat by simp
  then have "drop(i, l):list(A)" using a drop_type by(auto)
  then have "Cons(z, zs):list(A)" using b by(auto)
  then have "zs:list(A)" by(auto)
  then have "EX zs:list(A). drop(i, l) = Cons(z, zs)" using b by(auto)
  then show ?thesis ..
qed

theorem drop_length_app: "\<lbrakk> l:list(A); l':list(B) \<rbrakk> \<Longrightarrow> drop(length(l), l @ l') = drop(length(l), l) @ l'"
apply(subst drop_append, auto)
done

theorem drop_length_in_succ: "\<lbrakk> l:list(A); ll:list(B); j:succ(length(l)) \<rbrakk> \<Longrightarrow> drop(j, l @ ll) = drop (j, l) @ ll"
apply(subst drop_append, auto)
proof -
  assume a: "l:list(A)" "ll:list(B)" "j:length(l)"
  then have b: "j < length(l)" using lt_def by simp
  then have "j #- length(l) = 0" using diff_is_0_lemma[of j "length(l)"] a b by simp
  then show "drop(j, l) @ drop(j #- length(l), ll) = drop(j, l) @ ll" by simp
qed

theorem hd_type: "\<lbrakk> l:list(A); 0 < length(l) \<rbrakk> \<Longrightarrow> hd(l):A"
apply(frule length_greater_0_iff, auto)
apply(case_tac l, auto)
done

theorem length_tl: "\<lbrakk> l:list(A) \<rbrakk> \<Longrightarrow> length(tl(l)) = length(l) #- 1"
apply(auto)
done

theorem length_0_nil: "\<lbrakk> l:list(A); length(l) = 0 \<rbrakk> \<Longrightarrow> l = []"
apply(auto)
done

declare front_def [simp]

theorem front_Nil: "front([]) = []"
apply(simp)
done

theorem front_Cons1: "front([a]) = []"
apply(simp)
done

theorem front_Cons2: "front([a, b]) = [a]"
apply(simp)
done

theorem front_app_end: "\<lbrakk> l:list(A); a:A; b:A \<rbrakk> \<Longrightarrow> front( Cons(a, l) @ [b]) = Cons(a, l)"
apply(simp)
apply((subst rev_app_distrib, simp+)+)
done

theorem front_Cons3: "\<lbrakk> l:list(A); a:A; b:A \<rbrakk> \<Longrightarrow> front( Cons(a, Cons(b, l))) = Cons(a, front(Cons(b, l)))"
apply(simp)
apply(subst rev_app_distrib, auto)
done

theorem front_type: "\<lbrakk> l:list(A) \<rbrakk> \<Longrightarrow> front(l):list(A)"
apply(simp)
done

lemma length_front_induct_lemma: 
  " \<lbrakk>a \<in> A; l \<in> list(A); length(rev(tl(rev(l)))) = length(l) #- 1\<rbrakk> 
    \<Longrightarrow> length(rev(tl(rev(l) @ [a]))) = length(l)"
proof -
  assume a:"a:A" "l:list(A)" "length(rev(tl(rev(l)))) = length(l) #- 1"
  then have b: "rev(l) @ [a]:list(A)" by simp
  then have "tl(rev(l) @ [a]):list(A)" by simp
  then have "length(rev(tl(rev(l) @ [a]))) = length(tl(rev(l) @ [a]))" using length_rev by simp
  then have "length(rev(tl(rev(l) @ [a]))) = length(rev(l) @ [a]) #- 1" using length_tl b by simp
  then have "length(rev(tl(rev(l) @ [a]))) = length(rev(l)) #+ length([a]) #- 1"
    using length_app a by simp
  then have "length(rev(tl(rev(l) @ [a]))) = length(l) #+ length([a]) #- 1" 
    using length_rev a by simp
  then have "length(rev(tl(rev(l) @ [a]))) = length(l) #+ 1 #- 1" by simp
  then show ?thesis using a by simp
qed

theorem length_front: "\<lbrakk> l:list(A) \<rbrakk> \<Longrightarrow> length(front(l)) = length(l) #- 1"
apply(induct_tac l, auto)
apply(rule length_front_induct_lemma, simp+)
done

theorem rev_inject: "\<lbrakk> l:list(A); l':list(B) \<rbrakk> \<Longrightarrow> rev(l) = rev(l') <-> (l = l')"
apply(auto)
proof -
  assume a: "l:list(A)" "l':list(B)" and aa: "rev(l) = rev(l')"
  then have b: "rev(rev(l)) = rev(rev(l'))" by simp
  then have c: "rev(rev(l)) = l" using rev_rev_ident[of l A] a by simp
  then have "rev(rev(l')) = l'" using rev_rev_ident[of l' B] a by(simp only: mp)
  then show "l = l'" using b c by simp
qed

theorem rev_app_end: "\<lbrakk> l:list(A); l':list(B); a:C; a':E \<rbrakk> \<Longrightarrow> (rev(l @ [a]) = rev(l' @ [a'])) <-> (l = l' & a = a')"
proof(auto) 
  assume a: "l \<in> list(A)" "l' \<in> list(B)" and aa: "a \<in> C" "a' \<in> E" 
    and ab: "rev(l @ [a]) = rev(l' @ [a'])"
  have b: "rev(l @ [a]) = rev([a]) @ rev(l)" using rev_app_disturb a aa by simp
  have c: "rev(l' @ [a']) = rev([a']) @ rev(l')" using rev_app_disturb a aa by simp
  have "rev([a]) @ rev(l) = rev([a']) @ rev(l')" using ab b c by simp
  then have d: "[a] @ rev(l) = [a'] @ rev(l')" by simp
  then have "hd([a] @ rev(l)) = hd([a'] @ rev(l'))" by simp
  then have "a = a'" by simp
  then show "a = a'" by simp
  have "tl([a] @ rev(l)) = tl([a'] @ rev(l'))" using d by simp
  then have "rev(l) = rev(l')" by simp
  then have "l = l'" using rev_inject a by simp
  then show "l = l'" by simp  
qed

theorem snoc_iff: "\<lbrakk> l:list(A); l':list(B); a:C; a':E \<rbrakk> \<Longrightarrow> (l @ [a] = l' @ [a']) <-> (l = l' & a = a')"
apply(auto)
proof -
  assume a: "l:list(A)" "l':list(B)" and aa: "a:C" "a':E" and ab: "l @ [a] = l' @ [a']"
  have "rev(l @ [a]) = rev(l' @ [a'])" using ab by simp
  then have b: "l = l' & a = a'" using rev_app_end a aa by simp
  then show "l = l'" by simp
  show "a = a'" using b by simp
qed

declare leI [simp del]
declare length_type [simp del]
declare rev_type [simp del]
declare tl_type [simp del]
declare front_def [simp del]

lemmas list_typechecks =
  hd_type tl_type front_type list_rec_type
  map_type map_type2 app_type length_type rev_type flat_type
  list_add_type drop_type Cons Nil

lemmas list_simps =
  app_Nil app_Cons drop_0 drop_Nil drop_succ_Cons
  front_Cons1 front_Nil front_Cons2 front_Cons3

lemmas list_ss = list_typechecks list_simps
declare list_ss [simp]

end