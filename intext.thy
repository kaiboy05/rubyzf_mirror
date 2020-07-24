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

find_theorems "$# _" 
find_theorems zadd

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
  
oops

theorem zadd_zmult_distrib_left:
  "\<lbrakk> z1:int; z2:int; w:int \<rbrakk>
    \<Longrightarrow> w $* (z1 $+ z2) = (w $* z1) $+ (w $* z2)"
oops

theorem zmult_1_right:
  "z:int \<Longrightarrow> z $* $#1 = z"

oops

theorem zmult_0_right:
  "z:int \<Longrightarrow> z $* $#0 = $#0"

oops

theorem zdiff_type:
  "\<lbrakk> z:int; w:int \<rbrakk> \<Longrightarrow> z $- w : int"
apply(auto)
done

theorem zadd_left_commute:
  "\<lbrakk> z1:int; z2:int; z3:int \<rbrakk>
    \<Longrightarrow> z1 $+ (z2 $+ z3) = z2 $+ (z1 $+ z3)"

oops

theorem zadd_cancel_right:
  "\<lbrakk> z $+ k = w $+ k; z:int; w:int; k:int \<rbrakk> \<Longrightarrow> z = w"
apply(auto)
done

theorem zmult_cancel:
  "\<lbrakk> $#n $* z = $#n $* w; z:int; w:int; n:nat; 0 < n \<rbrakk>
    \<Longrightarrow> z = w"
oops

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