theory intext
imports ZF.Int natext
begin

definition zmod :: "[i,i] \<Rightarrow> i" (infixl "$'/'/" 69)
where 
  "x $// y == if(znegative(x),
                  if(zmagnitude(x) mod y = 0,
                    0, y #- (zmagnitude(x) mod y)),
              zmagnitude(x) mod y)"

definition zdiv :: "[i,i] \<Rightarrow> i" (infixl "$'/" 69)
where
  "x $/ y == if(znegative(x),
                if(zmagnitude(x) mod y = 0,
                  $- $#(zmagnitude(x) div y),
                  $- $#(succ(zmagnitude(x) div y))),
                $#(zmagnitude(x) div y))"

theorem not_zneg_zmag:
  "\<lbrakk> z:int; ~znegative(z) \<rbrakk> \<Longrightarrow> $# zmagnitude(z) = z"
apply(auto)
done

theorem zneg_zmag:
  "\<lbrakk> z:int; znegative(z) \<rbrakk> \<Longrightarrow> $# zmagnitude(z) = $-z"
apply(auto)
done

lemma zmag_0_eq_0_iff: "z:int \<Longrightarrow> zmagnitude(z) = 0 \<longleftrightarrow> z = $#0"
apply(auto)
apply(subgoal_tac "znegative(z) | ~znegative(z)")
apply(erule disjE)
apply(frule zneg_zmag, simp)
proof -
  assume a: "zmagnitude(z) = 0" and ab: "$# zmagnitude(z) = $- z" and ac: "z:int"
  have b: "$# zmagnitude(z) = $# 0" using a by simp
  then have "$- $# zmagnitude(z) = $- $- z" using ab by simp
  then have "z = $- $# zmagnitude(z)" using ac by simp
  then have "z = $- $#0" using b by simp
  then show "z = $#0" by simp
next
  assume a: "z:int" and ab: "zmagnitude(z) = 0" and ac: "~znegative(z)"
  have "$# zmagnitude(z) = z" using a ac by simp
  then show "z = $# 0" using ab by simp
next
  show "znegative(z) \<or> \<not> znegative(z)" by simp
qed

lemma int_eq_or_neq_0: "\<lbrakk> z:int \<rbrakk> \<Longrightarrow> z = $#0 | z \<noteq> $#0"
apply(auto)
done

theorem zneg_zmag_0_lt:
  "\<lbrakk> z:int; znegative(z) \<rbrakk> \<Longrightarrow> 0 < zmagnitude(z)"
apply(insert zmagnitude_type[of z])
apply(drule nat_0_le)
apply(frule int_eq_or_neq_0)
apply(erule disjE, simp)
proof -
  assume a: "z:int" "znegative(z)" "0 \<le> zmagnitude(z)" "z \<noteq> $#0"
  then have "zmagnitude(z) ~= 0" using zmag_0_eq_0_iff[of z] by auto
  then show "0 < zmagnitude(z)" using a Ord_0_lt by simp
qed

theorem znat_mult:
  "\<lbrakk> n:nat; m:nat \<rbrakk> \<Longrightarrow> $#(n #* m) = $#n $* $#m"
apply(induct_tac n, auto)
proof -
  fix x
  assume a: "m \<in> nat" "x \<in> nat" "$# (x #* m) = $# x $* $# m"
  have "$# (m #+ x #* m) = $# m $+ $# (x #* m)" using int_of_add by simp
  then have b: "$# (m #+ x #* m) = $# m $+ $# x $* $# m" using a by simp
  have "$# succ(x) $* $# m = $# (x #+ 1) $* $# m" using a by simp
  then have "$# succ(x) $* $# m = ($# x $+ $# 1) $* $# m" using int_of_add[of x 1] by simp
  then have "$# succ(x) $* $# m = $# x $* $# m $+ $# 1 $* $# m" 
    using zadd_zmult_distrib[of "$# x" "$# 1" "$# m"] by simp
  then show "$# (m #+ x #* m) = $# succ(x) $* $# m" using b zadd_commute by simp
qed

theorem zminus_diff:
  "\<lbrakk> n:nat; m:nat; m \<le> n \<rbrakk> \<Longrightarrow> $- $#(n #- m) = $-$#n $+ $#m"
proof -
  assume a: "n:nat" "m:nat" "m \<le> n"
  then have "$#(n #- m) = $# n $- $# m" using int_of_diff by simp
  then have "$- $#(n #- m) = $- ($# n $- $# m)" by simp
  then have "$- $#(n #- m) = $#m $- $#n" using zminus_zdiff_eq by simp
  then show ?thesis using zadd_commute zcompare_rls by(simp add: zadd_commute zcompare_rls)
qed

theorem zadd_zmult_distrib_left:
  "\<lbrakk> z1:int; z2:int; w:int \<rbrakk>
    \<Longrightarrow> w $* (z1 $+ z2) = (w $* z1) $+ (w $* z2)"
apply(rule zadd_zmult_distrib2)
done

theorem zmult_1_right:
  "z:int \<Longrightarrow> z $* $#1 = z"
apply(insert zmult_int1)
apply(subst zmult_commute)
apply(simp)
done

theorem zmult_0_right:
  "z:int \<Longrightarrow> z $* $#0 = $#0"
apply(subst zmult_commute)
apply(rule zmult_int0)
done

theorem zdiff_type:
  "\<lbrakk> z:int; w:int \<rbrakk> \<Longrightarrow> z $- w : int"
apply(auto)
done

theorem zadd_left_commute:
  "\<lbrakk> z1:int; z2:int; z3:int \<rbrakk>
    \<Longrightarrow> z1 $+ (z2 $+ z3) = z2 $+ (z1 $+ z3)"
apply(subst zadd_assoc[of z2 z1 z3, THEN sym])
apply(subst zadd_commute[of z2 z1], simp add: zadd_assoc)
done

theorem zadd_cancel_right:
  "\<lbrakk> z $+ k = w $+ k; z:int; w:int; k:int \<rbrakk> \<Longrightarrow> z = w"
apply(auto)
done

lemma int_rep:
  "z:int \<Longrightarrow> (znegative(z) & z = $- $#(zmagnitude(z))) | (~znegative(z) & z = $#(zmagnitude(z)))"
apply(auto)
done

lemma int_zneg_zmag_iff:
  "\<lbrakk> z:int; w:int \<rbrakk> \<Longrightarrow> z = w \<longleftrightarrow> ((znegative(z) \<longleftrightarrow> znegative(w)) & zmagnitude(z) = zmagnitude(w))"
apply(auto)
apply((drule int_rep, auto)+)
done

lemma zmag_mult:
  "\<lbrakk> a:int; b:int \<rbrakk> \<Longrightarrow> zmagnitude(a $* b) = zmagnitude(a) #* zmagnitude(b)"
proof -
  assume a: "a:int" "b:int"
  {
    assume aa: "znegative(a)" "znegative(b)"
    have ab: "a = $- $#(zmagnitude(a))"
      using a aa int_rep by simp
    have ac: "b = $- $#(zmagnitude(b))"
      using a aa int_rep by simp
    have "zmagnitude(a $* b) 
                = zmagnitude(($- $#(zmagnitude(a))) $* ($- $#(zmagnitude(b))))"
      using ab ac by simp
    then have "zmagnitude(a $* b) 
                = zmagnitude($#(zmagnitude(a)) $* $#(zmagnitude(b)))" by simp
    then have "zmagnitude(a $* b) 
                = zmagnitude($#(zmagnitude(a) #* zmagnitude(b)))" 
      using znat_mult by simp
    then have "zmagnitude(a $* b) = zmagnitude(a) #* zmagnitude(b)" by simp
  } then have b: "\<lbrakk> znegative(a); znegative(b) \<rbrakk> 
      \<Longrightarrow> zmagnitude(a $* b) = zmagnitude(a) #* zmagnitude(b)" by simp
  {
    assume aa: "znegative(a)" "~znegative(b)"
    have ab: "a = $- $#(zmagnitude(a))"
      using a aa int_rep by simp
    have ac: "b = $#(zmagnitude(b))"
      using a aa int_rep by simp
    have "zmagnitude(a $* b) 
                = zmagnitude(($- $#(zmagnitude(a))) $* ($#(zmagnitude(b))))"
      using ab ac by simp
    then have "zmagnitude(a $* b) 
                = zmagnitude($- ($#(zmagnitude(a)) $* $#(zmagnitude(b))))" by simp
    then have "zmagnitude(a $* b) 
                = zmagnitude($-($#(zmagnitude(a) #* zmagnitude(b))))" 
      using znat_mult by simp
    then have "zmagnitude(a $* b) = zmagnitude(a) #* zmagnitude(b)" by simp
  } then have c: "\<lbrakk> znegative(a); ~znegative(b) \<rbrakk> 
      \<Longrightarrow> zmagnitude(a $* b) = zmagnitude(a) #* zmagnitude(b)" by simp
  {
    assume aa: "~znegative(a)" "znegative(b)"
    have ab: "a = $#(zmagnitude(a))"
      using a aa int_rep by simp
    have ac: "b = $- $#(zmagnitude(b))"
      using a aa int_rep by simp
    have "zmagnitude(a $* b) 
                = zmagnitude(($#(zmagnitude(a))) $* ($- $#(zmagnitude(b))))"
      using ab ac by simp
    then have "zmagnitude(a $* b) 
                = zmagnitude($- ($#(zmagnitude(a)) $* $#(zmagnitude(b))))" by simp
    then have "zmagnitude(a $* b) 
                = zmagnitude($-($#(zmagnitude(a) #* zmagnitude(b))))" 
      using znat_mult by simp
    then have "zmagnitude(a $* b) = zmagnitude(a) #* zmagnitude(b)" by simp
  } then have d: "\<lbrakk> ~znegative(a); znegative(b) \<rbrakk> 
      \<Longrightarrow> zmagnitude(a $* b) = zmagnitude(a) #* zmagnitude(b)" by simp
  {
    assume aa: "~znegative(a)" "~znegative(b)"
    have ab: "a = $#(zmagnitude(a))"
      using a aa int_rep by simp
    have ac: "b = $#(zmagnitude(b))"
      using a aa int_rep by simp
    have "zmagnitude(a $* b) 
                = zmagnitude(($#(zmagnitude(a))) $* ($#(zmagnitude(b))))"
      using ab ac by simp
    then have "zmagnitude(a $* b) 
                = zmagnitude($#(zmagnitude(a)) $* $#(zmagnitude(b)))" by simp
    then have "zmagnitude(a $* b) 
                = zmagnitude($#(zmagnitude(a) #* zmagnitude(b)))" 
      using znat_mult by simp
    then have "zmagnitude(a $* b) = zmagnitude(a) #* zmagnitude(b)" by simp
  } then have "\<lbrakk> ~znegative(a); ~znegative(b) \<rbrakk> 
      \<Longrightarrow> zmagnitude(a $* b) = zmagnitude(a) #* zmagnitude(b)" by simp
  then show ?thesis using b c d by auto
qed

lemma znegative_minus_int_of: "n:nat \<Longrightarrow> n \<noteq> 0 ==> znegative($- $# n)"
apply(rule ccontr)
apply(drule not_znegative_imp_zero, auto)
done

lemma zneg_mult: 
  "\<lbrakk> a:int; b:int; a \<noteq> $# 0; b \<noteq> $# 0 \<rbrakk> 
    \<Longrightarrow> ~znegative(a $* b) 
        \<longleftrightarrow> (znegative(a) & znegative(b) | ~znegative(a) & ~znegative(b))"
apply(auto)
apply(rule ccontr)
prefer 2
apply(rule ccontr)
prefer 2
proof -
  assume a: "a \<in> int" "b \<in> int" "a \<noteq> $# 0" "b \<noteq> $# 0"
  have aa: "zmagnitude(a) \<noteq> 0" using zmag_0_eq_0_iff[of a] a by simp
  have "zmagnitude(b) \<noteq> 0" using zmag_0_eq_0_iff[of b] a by simp
  then have ab: "zmagnitude(a) #* zmagnitude(b) \<noteq> 0" using aa by simp
  assume b: "~znegative(a $* b)" "znegative(a)" "\<not> znegative(b)"
  have c: "a = $- $#(zmagnitude(a))" using int_rep a b by simp
  have "b = $#(zmagnitude(b))" using int_rep a b by simp
  then have "a $* b = ($- $#(zmagnitude(a)) $* $#(zmagnitude(b)))" 
    using c by simp
  then have "a $* b = $- ($#(zmagnitude(a)) $* $#(zmagnitude(b)))" by simp
  then have d: "a $* b = $- $# (zmagnitude(a) #* zmagnitude(b))"
    using znat_mult by simp
  have "znegative($- ($# (zmagnitude(a) #* zmagnitude(b))))" 
    using znegative_minus_int_of[of "zmagnitude(a) #* zmagnitude(b)"] ab a by simp
  then have "znegative(a $* b)" using d by simp
  then show "False" using b by simp
next
  assume a: "a \<in> int" "b \<in> int" "a \<noteq> $# 0" "b \<noteq> $# 0"
  have aa: "zmagnitude(a) \<noteq> 0" using zmag_0_eq_0_iff[of a] a by simp
  have "zmagnitude(b) \<noteq> 0" using zmag_0_eq_0_iff[of b] a by simp
  then have ab: "zmagnitude(a) #* zmagnitude(b) \<noteq> 0" using aa by simp
  assume b: "~znegative(a $* b)" "~znegative(a)" "znegative(b)"
  have c: "a = $#(zmagnitude(a))" using int_rep a b by simp
  have "b = $- $#(zmagnitude(b))" using int_rep a b by simp
  then have "a $* b = ($#(zmagnitude(a)) $* $- $#(zmagnitude(b)))" 
    using c by simp
  then have "a $* b = $- ($#(zmagnitude(a)) $* $#(zmagnitude(b)))" by simp
  then have d: "a $* b = $- $# (zmagnitude(a) #* zmagnitude(b))"
    using znat_mult by simp
  have "znegative($- ($# (zmagnitude(a) #* zmagnitude(b))))" 
    using znegative_minus_int_of[of "zmagnitude(a) #* zmagnitude(b)"] ab a by simp
  then have "znegative(a $* b)" using d by simp
  then show "False" using b by simp
next
  assume a: "a \<in> int" "b \<in> int" "a \<noteq> $# 0" "b \<noteq> $# 0"
  have aa: "zmagnitude(a) \<noteq> 0" using zmag_0_eq_0_iff[of a] a by simp
  have "zmagnitude(b) \<noteq> 0" using zmag_0_eq_0_iff[of b] a by simp
  then have ab: "zmagnitude(a) #* zmagnitude(b) \<noteq> 0" using aa by simp
  assume b: "znegative(a $* b)" "znegative(a)" "znegative(b)"
  have c: "a = $- $#(zmagnitude(a))" using int_rep a b by simp
  have "b = $- $#(zmagnitude(b))" using int_rep a b by simp
  then have "a $* b = ($- $#(zmagnitude(a)) $* $- $#(zmagnitude(b)))" 
    using c by simp
  then have "a $* b = ($#(zmagnitude(a)) $* $#(zmagnitude(b)))" by simp
  then have d: "a $* b = $# (zmagnitude(a) #* zmagnitude(b))"
    using znat_mult by simp
  have "~ znegative(($# (zmagnitude(a) #* zmagnitude(b))))" 
    using ab a by simp
  then have "~znegative(a $* b)" using d by simp
  then show "False" using b by simp
next
  assume a: "a \<in> int" "b \<in> int" "a \<noteq> $# 0" "b \<noteq> $# 0"
  have aa: "zmagnitude(a) \<noteq> 0" using zmag_0_eq_0_iff[of a] a by simp
  have "zmagnitude(b) \<noteq> 0" using zmag_0_eq_0_iff[of b] a by simp
  then have ab: "zmagnitude(a) #* zmagnitude(b) \<noteq> 0" using aa by simp
  assume b: "znegative(a $* b)" "~znegative(a)" "~znegative(b)"
  have c: "a = $#(zmagnitude(a))" using int_rep a b by simp
  have "b = $#(zmagnitude(b))" using int_rep a b by simp
  then have "a $* b = ($#(zmagnitude(a)) $* $#(zmagnitude(b)))" 
    using c by simp
  then have "a $* b = ($#(zmagnitude(a)) $* $#(zmagnitude(b)))" by simp
  then have d: "a $* b = $# (zmagnitude(a) #* zmagnitude(b))"
    using znat_mult by simp
  have "~ znegative(($# (zmagnitude(a) #* zmagnitude(b))))" 
    using ab a by simp
  then have "~znegative(a $* b)" using d by simp
  then show "False" using b by simp
qed

lemma neq_0_zmult_0: "\<lbrakk> m:int; n:int; m \<noteq> $# 0; m $* n = $# 0 \<rbrakk> \<Longrightarrow> n = $# 0"
apply(rule ccontr)
apply(frule zneg_mult)
apply(assumption)
back
apply(auto)
proof -
  assume a: "m \<in> int" "n \<in> int" "m \<noteq> $# 0" "m $* n = $# 0" "n \<noteq> $# 0"
  and b: "znegative(m)" "znegative(n)"
  have cont: "zmagnitude(m $* n) = 0" using zneg_mult a by simp
  have "zmagnitude(m $* n) = zmagnitude(m) #* zmagnitude(n)" 
    using zmag_mult[of m n] a by simp
  have c: "zmagnitude(m) \<noteq> 0" using a zmag_0_eq_0_iff by simp
  have "zmagnitude(n) \<noteq> 0" using a zmag_0_eq_0_iff by simp
  then have d: "zmagnitude(m) #* zmagnitude(n) \<noteq> 0" using c by simp
  then have "zmagnitude(m $* n) = zmagnitude(m) #* zmagnitude(n)" 
    using zmag_mult[of m n] a by simp
  then have "zmagnitude(m $* n) \<noteq> 0" using d by simp
  then show "False" using cont by simp
next
  assume a: "m \<in> int" "n \<in> int" "m \<noteq> $# 0" "m $* n = $# 0" "n \<noteq> $# 0"
  and b: "~znegative(m)" "~znegative(n)"
  have cont: "zmagnitude(m $* n) = 0" using zneg_mult a by simp
  have "zmagnitude(m $* n) = zmagnitude(m) #* zmagnitude(n)" 
    using zmag_mult[of m n] a by simp
  have c: "zmagnitude(m) \<noteq> 0" using a zmag_0_eq_0_iff by simp
  have "zmagnitude(n) \<noteq> 0" using a zmag_0_eq_0_iff by simp
  then have d: "zmagnitude(m) #* zmagnitude(n) \<noteq> 0" using c by simp
  then have "zmagnitude(m $* n) = zmagnitude(m) #* zmagnitude(n)" 
    using zmag_mult[of m n] a by simp
  then have "zmagnitude(m $* n) \<noteq> 0" using d by simp
  then show "False" using cont by simp
qed

theorem zmult_cancel:
  "\<lbrakk> $#n $* z = $#n $* w; z:int; w:int; n:nat; 0 < n \<rbrakk>
    \<Longrightarrow> z = w"
proof -
  assume a: "$#n $* z = $#n $* w" "z:int" "w:int" "n:nat" "0 < n"
  have b: "(znegative($#n $* z) & $#n $* z = $- $#(zmagnitude($#n $* z))) | 
        (~znegative($#n $* z) & $#n $* z = $#(zmagnitude($#n $* z)))"
    using int_rep by simp
  have c: "(znegative($#n $* w) & $#n $* w = $- $#(zmagnitude($#n $* w))) | 
        (~znegative($#n $* w) & $#n $* w = $#(zmagnitude($#n $* w)))"
    using int_rep by simp
  have d: "znegative(($#n $* z)) \<longleftrightarrow> (znegative($#n $* w))" using a by simp
  {
    assume aa: "znegative(($#n $* z))"
    then have ab: "(znegative($#n $* w))" using d by simp
    have ac: "$#n $* z = $- $#(zmagnitude($#n $* z))" using b aa by simp
    have ad: "$#n $* w = $- $#(zmagnitude($#n $* w))" using b ab by simp
    have imp: "zmagnitude($#n $* z) = zmagnitude($#n $* w)" using a by simp
    have "zmagnitude($#n $* z) = zmagnitude($#n) #* zmagnitude(z)"
      using zmag_mult[of "$# n" z] a by simp
    then have ae: "zmagnitude($#n $* z) = n #* zmagnitude(z)" by simp
    have "zmagnitude($#n $* w) = zmagnitude($#n) #* zmagnitude(w)"
      using zmag_mult[of "$# n" w] a by simp
    then have af: "zmagnitude($#n $* w) = n #* zmagnitude(w)" by simp
    have "n #* zmagnitude(z) = n #* zmagnitude(w)" using imp ae af by simp
    then have "zmagnitude(z) = zmagnitude(w)" using a by(auto)
  } then have e: "znegative(($#n $* z)) \<Longrightarrow> zmagnitude(z) = zmagnitude(w)" by simp
  {
    assume aa: "~znegative(($#n $* z))"
    then have ab: "(~znegative($#n $* w))" using d by simp
    have ac: "$#n $* z = $#(zmagnitude($#n $* z))" using b aa by simp
    have ad: "$#n $* w = $#(zmagnitude($#n $* w))" using b ab by simp
    have imp: "zmagnitude($#n $* z) = zmagnitude($#n $* w)" using a by simp
    have "zmagnitude($#n $* z) = zmagnitude($#n) #* zmagnitude(z)"
      using zmag_mult[of "$# n" z] a by simp
    then have ae: "zmagnitude($#n $* z) = n #* zmagnitude(z)" by simp
    have "zmagnitude($#n $* w) = zmagnitude($#n) #* zmagnitude(w)"
      using zmag_mult[of "$# n" w] a by simp
    then have af: "zmagnitude($#n $* w) = n #* zmagnitude(w)" by simp
    have "n #* zmagnitude(z) = n #* zmagnitude(w)" using imp ae af by simp
    then have "zmagnitude(z) = zmagnitude(w)" using a by(auto)
  } then have "~znegative(($#n $* z)) \<Longrightarrow> zmagnitude(z) = zmagnitude(w)" by simp
  then have f: "zmagnitude(z) = zmagnitude(w)" using e by(auto)
  {
    assume aa: "z = $# 0 | w = $# 0"
    have n_neq_0: "$# n \<noteq> $# 0" using a by auto
    have "z = $#0 ==> $# n $* z = $# n $* $# 0" by simp
    then have ab: "z = $#0 ==> $# n $* z = $# 0" using zmult_0_right by simp
    have "w = $#0 ==> $# n $* w = $# n $* $# 0" by simp
    then have ac: "w = $#0 ==> $# n $* w = $# 0" using zmult_0_right by simp
    have "$# n $* z = $# 0 | $# n $* w = $# 0" using aa ab ac by blast
    then have ad: "$# n $* z = $# 0" using a by(auto)
    then have "$# n $* w = $# 0" using a by(auto)
    then have ae: "w = $# 0" using neq_0_zmult_0[of "$# n" w] a n_neq_0 by simp
    have "z = $# 0" using neq_0_zmult_0[of "$# n" z] ad n_neq_0 a by simp
    then have "z = w" using ae by simp
  } then have g: "z = $# 0 | w = $# 0 \<Longrightarrow> z = w" by simp
  {
    assume aa: "z \<noteq> $# 0 & w \<noteq> $# 0"
    have "znegative($# n $* z) \<longleftrightarrow> ~znegative($# n) \<and> znegative(z) \<or> znegative($# n) \<and> ~znegative(z)"
      using zneg_mult[of "$# n" z] aa a by(auto)
    then have "znegative($# n $* z) \<longleftrightarrow> znegative(z)" by simp
    then have "znegative(z) \<longleftrightarrow> znegative($# n $* w)" using a by(auto)
    then have "znegative(z) \<longleftrightarrow> (znegative($# n) & ~znegative(w) | ~znegative($# n) & znegative(w))"
      using zneg_mult[of "$# n" w] a aa by(auto)
    then have "znegative(z) \<longleftrightarrow> znegative(w)" by simp
    then have "z = w" using int_zneg_zmag_iff f a by simp
  } then have "z \<noteq> $# 0 & w \<noteq> $# 0 \<Longrightarrow> z = w" by simp
  then show "z = w" using g by(auto)
qed

declare zmod_def [simp]

theorem zmod_dep_type:
  "\<lbrakk> 0 < n; m:int; n:nat \<rbrakk> \<Longrightarrow> m $// n : nats(n)"
apply(auto)
oops

theorem zmod_less_pos:
  "\<lbrakk> 0 < n; m:int; zmagnitude(m) < n; ~znegative(m) \<rbrakk>
    \<Longrightarrow> m $// n = zmagnitude(m)"
apply(auto)
oops

theorem zmod_less_neg:
  "\<lbrakk> 0 < n; m:int; zmagnitude(m) < n; znegative(m);
    zmagnitude(m) mod n \<noteq> 0 \<rbrakk>
    \<Longrightarrow> m $// n = n #- zmagnitude(m)"
apply(auto)
oops

theorem zmod_pos:
  "\<lbrakk> 0 < n; m:int; ~znegative(m) \<rbrakk> 
    \<Longrightarrow> m $// n = zmagnitude(m) mod n"
apply(auto)
done

theorem zmod_neg_0:
  "\<lbrakk> 0 < n; m:int; znegative(m); zmagnitude(m) mod n = 0 \<rbrakk>
    \<Longrightarrow> m $// n = 0"
apply(auto)
done

theorem zmod_neg_not0:
  "\<lbrakk> 0 < n; m:int; znegative(m); zmagnitude(m) mod n ~= 0 \<rbrakk>
    \<Longrightarrow> m $// n = n #- (zmagnitude(m) mod n)"
apply(auto)
done

declare zdiv_def [simp]

theorem zdiv_type:
  "\<lbrakk> 0 < n; m:int; n:nat \<rbrakk> \<Longrightarrow> m $/ n : int"
apply(auto)
done

theorem zdiv_less_pos:
  "\<lbrakk> 0 < n; m:int; zmagnitude(m) < n; ~znegative(m) \<rbrakk>
    \<Longrightarrow> m $/ n = $#0"
apply(auto)
oops

theorem zdiv_less_neg:
  "\<lbrakk> 0 < n; m:int; n:nat; zmagnitude(m) < n; znegative(m) \<rbrakk>
    \<Longrightarrow> m $/ n = $#0"

oops

theorem zdiv_geq_pos:
  "\<lbrakk> 0 < n; m:int; n:nat; n \<le> zmagnitude(m); ~znegative(m) \<rbrakk>
    \<Longrightarrow> m $/ n = $# (zmagnitude(m) div n)"
apply(auto)
done

theorem zdiv_geq_neq_0:
  "\<lbrakk> 0 < n; m:int; n:nat; znegative(m); n \<le> zmagnitude(m);
    zmagnitude(m) mod n = 0 \<rbrakk>
    \<Longrightarrow> m $/ n = $- $# (zmagnitude(m) div n)"
apply(auto)
done

theorem zdiv_geq_neg_not0:
  "\<lbrakk> 0 < n; m:int; n:nat; znegative(m); n \<le> zmagnitude(m);
    zmagnitude(m) mod n \<noteq> 0 \<rbrakk>
    \<Longrightarrow> m $/ n = $- $# (succ(zmagnitude(m) div n))"
apply(auto)
done

theorem zmod_zdiv_equality:
  "\<lbrakk> 0 < n; m:int; n:nat \<rbrakk>
    \<Longrightarrow> (m $/ n) $* $#n $+ $#(m $// n) = m"

oops

theorem int_factorise:
  "ALL t':int. ALL n:{z:nat. 0 < x}. EX t:int. EX j:nats(n).
    t $* $#n $+ $#j = t"

oops

theorem int_factorise2:
  "\<lbrakk> t':int; n:{x:nat. 0 < x} \<rbrakk>
    \<Longrightarrow> EX t:int. EX j:nats(n). $#n $* t $+ $#j = t'"

oops

theorem mult_zmag_gt:
  "\<lbrakk> n:nat; 0 < n; t:int; znegative(t); j:nat; j < n \<rbrakk>
    \<Longrightarrow> j < n #* zmagnitude(t)"

oops

theorem zneg_nt_simp:
  "\<lbrakk> n:nat; 0 < n; t:int; j:nat; j < n; znegative(t) \<rbrakk>
    \<Longrightarrow> $# n $* t $+ $# j = $-$#(n #* zmagnitude(t) #- j)"

oops

theorem zneg_mult_add:
  "\<lbrakk> n:nat; 0 < n; t:int; znegative(t); j:nat; j < n \<rbrakk>
    \<Longrightarrow> znegative($# n $* t $+ $# j)"

oops

theorem zmod_mult_self:
  "\<lbrakk> n:nat; 0 < n; t:int; j:nats(n) \<rbrakk>
    \<Longrightarrow> ($# n $* t $+ $# j) $// n = j"

oops

theorem zdiv_mult_self:
  "\<lbrakk> n:nat; 0 < n; t:int; j:nats(n) \<rbrakk>
    \<Longrightarrow> ($# n $* t $+ $# j) $/ n = t"

oops

end