theory listext
imports ZF.List 
begin

definition front :: "i \<Rightarrow> i" where
  "front(l) == rev( tl( rev(l) ) )"

theorem rev_app_disturb: "\<lbrakk> xs: list(A); ys: list(B) \<rbrakk> \<Longrightarrow> rev(xs@ys) = rev(ys)@rev(xs)"
by(induct_tac xs, auto simp add: app_assoc)

lemma all_drop_length_Cons_t: "xs: list(A) \<Longrightarrow> ALL x. EX z. EX zs:list(A). drop( length(xs), Cons(x, xs) ) = Cons(z, zs)"
by(induct_tac xs, auto)

theorem drop_length_Cons_t: "xs: list(A) \<Longrightarrow> EX z. EX zs:list(A). drop( length(xs), Cons(x, xs) ) = Cons(z, zs)"
by(simp add: all_drop_length_Cons_t)

theorem drop_length_t: "\<lbrakk> l:list(A); i:length(l) \<rbrakk> \<Longrightarrow> EX z. EX zs:list(A). drop(i, l) = Cons(z, zs)"
proof -
  assume a: "l:list(A)" "i:length(l)"
  then have "EX z. EX zs. drop(i, l) = Cons(z, zs)" using drop_length by(auto)
  then obtain z where "EX zs. drop(i, l) = Cons(z, zs)" ..
  then obtain zs where b: "drop(i, l) = Cons(z, zs)" ..
  have c: "length(l):nat" using a length_type by(auto)
  have "i < length(l)" using a lt_def by(auto)
  then have "i:nat" using c lt_nat_in_nat by(auto)
  then have "drop(i, l):list(A)" using a drop_type by(auto)
  then have "Cons(z, zs):list(A)" using b by(auto)
  then have "zs:list(A)" by(auto)
  then have "EX zs:list(A). drop(i, l) = Cons(z, zs)" using b by(auto)
  then show ?thesis ..
qed

theorem drop_length_app: "\<lbrakk> l:list(A); l':list(B) \<rbrakk> \<Longrightarrow> drop(length(l), l @ l') = drop(length(l), l') @ l'"
apply(induct_tac l, auto)
oops

theorem drop_length_in_succ: "\<lbrakk> l:list(A); l':list(B); j:succ(length(l)) \<rbrakk> \<Longrightarrow> drop(j, l @ l') = drop (j, l) @ l'"
oops

theorem hd_type: "\<lbrakk> l:list(A); 0< length(l) \<rbrakk> \<Longrightarrow> hd(l):A"
oops

theorem length_tl: "\<lbrakk> l:list(A) \<rbrakk> \<Longrightarrow> length(tl(l)) = length(l) #- 1"
oops

theorem length_0_nil: "\<lbrakk> l:list(A); length(l) = 0 \<rbrakk> \<Longrightarrow> l = []"
oops

theorem front_Nil: "front([]) = []"
oops

theorem front_Cons1: "front([a]) = []"
oops

theorem front_Cons2: "front([a, b]) = [a]"
oops

theorem front_app_end: "\<lbrakk> l:list(A); a:A; b:A \<rbrakk> \<Longrightarrow> front( Cons(a, l) @ [b]) = Cons(a, l)"
oops

theorem front_Cons3: "\<lbrakk> l:list(A); a:A; b:A \<rbrakk> \<Longrightarrow> front( Cons(a, Cons(b, l))) = Cons(a, front(Cons(b, l)))"
oops

theorem front_type: "\<lbrakk> l:list(A) \<rbrakk> \<Longrightarrow> front(l):list(A)"
oops

theorem length_front: "\<lbrakk> l:list(A) \<rbrakk> \<Longrightarrow> length(front(l)) = length(l) #- 1"
oops

theorem rev_inject: "\<lbrakk> l:list(A); l':list(B) \<rbrakk> \<Longrightarrow> rev(l) = rev(l') <-> (l = l')"
oops

theorem rev_app_end: "\<lbrakk> l:list(A); l':list(B); a:C; a':E \<rbrakk> \<Longrightarrow> (rev(l @ [a]) = rev(l' @ [a'])) <-> (l = l' & a = a')"
oops

theorem snoc_iff: "\<lbrakk> l:list(A); l':list(B); a:C; a':E \<rbrakk> \<Longrightarrow> (l @ [a] = l' @ [a']) <-> (l = l' & a = a')"
oops

end