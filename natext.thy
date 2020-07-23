theory natext
imports ZF.Arith ZF.ArithSimp
begin

definition nats :: "i \<Rightarrow> i" where
  "nats(n) == {m:nat. m < n}"

theorem le_in_succ: "[| i \<le> n; n: nat; i:nat|] ==> i:succ(n)"
apply(auto simp: ltD ltE)
done

theorem succ_add_1: "n:nat ==> succ(n) = n #+ 1"
apply(auto)
done

lemma neq_0_lt_0: "[| m #- n ~= 0; m:nat; n:nat |] ==> 0 < m #- n"
apply(rule Ord_0_lt)
apply(auto)
done

theorem diff_le_0: "[| m \<le> n; n:nat; m:nat |] ==> m #- n = 0"
apply(rule ccontr)
apply(drule le_imp_not_lt)
apply(drule neq_0_lt_0, assumption+)
apply(simp add: less_diff_conv)
done

theorem add_lt_n: "[| x #+ n < y #+ n; n:nat; x:nat; y:nat |] ==> x < y"
apply(rule_tac k = "n" in add_lt_elim1)
apply(simp add: add_commute)
apply(assumption+)
done

lemma lt_imp_neq: "x < y \<Longrightarrow> x \<noteq> y"
apply(auto)
done

theorem add_lt_reverse: "\<lbrakk> m < n; x #+ n = m #+ y; x:nat; y:nat; n:nat; m:mat \<rbrakk> \<Longrightarrow> x < y"
apply(rule ccontr)
apply(simp add: not_lt_iff_le)
apply(drule add_lt_le_mono, auto)
apply((drule lt_imp_neq)+)
apply(simp add: add_commute)
done

theorem diff_lt_0: "[| m < n; n:nat; m:nat |] ==> 0 < n #- m"
apply(simp add: less_diff_conv)
done

lemma add_lt_larger_side_help: "\<lbrakk> n:nat; m:nat; x:nat; m < n \<rbrakk> \<Longrightarrow> m #+ 0 < n #+ x"
by(rule add_lt_le_mono[of m n 0 x], auto)

lemma add_lt_larger_side: "\<lbrakk> n:nat; m:nat; x:nat; m < n \<rbrakk> \<Longrightarrow> m < x #+ n"
apply(frule add_lt_larger_side_help[of n m x], auto)
apply(simp add: add_commute)
done

lemma diff_add_comm_help: "⟦n ∈ nat; m ∈ nat; m < n; x ∈ nat; x #+ n #- m = x #+ (n #- m)⟧ ⟹ succ(x #+ n) #- m = succ(x #+ (n #- m))"
proof -
  assume a: "n ∈ nat" "m ∈ nat" "m < n" "x:nat" "x #+ n #- m = x #+ (n #- m)"
  then have "m < x #+ n" using add_lt_larger_side by simp
  then have "m \<le> x #+ n" using leI by simp
  then have b: "succ(x #+ n #- m) = succ(x #+ n) #- m" using diff_succ by simp
  have "succ(x #+ n #- m) = succ(x #+ (n #- m))" using succ_inject_iff a by simp
  then show ?thesis using b by simp
qed

theorem diff_add_assoc: "[| m < n; n:nat; m:nat; k:nat|] ==> k #+ n #- m = k #+ (n #- m)"
apply(drule diff_lt_0, assumption+)
apply(induct_tac k, auto)
by(rule diff_add_comm_help, auto)

theorem diff_add_comm: "[| m < n; n:nat; m:nat; k:nat|] ==> n #+ k #- m = k #+ (n #- m)"
apply(simp add: add_commute)
by(rule diff_add_assoc)

theorem n_gt_0_succ: "[| 0 < n; n: nat; !!x. [| n = succ(x); x:nat |] ==> P |] ==> P"
by(erule zero_lt_natE)

lemma refl_add_help: "[| n:nat; m:nat |] ==> 0 #+ n \<le> m #+ n" 
by(rule add_le_mono1, simp)

theorem mult_le_self: "[| 0 < m; n:nat; m:nat |] ==> n \<le> n #* m"
apply (case_tac m, simp)
apply (frule_tac ?m="n #* x" in refl_add_help)
by (auto simp add: add_commute)

theorem gt_not0: "[| 0 < n; n:nat |] ==> n~= 0"
apply(auto)
done

theorem diff_succ: "[| m \<le> n; n:nat; m:nat |] ==> succ(n) #- m = succ(n #- m)"
by(rule diff_succ)

lemma add_same_cancel: "\<lbrakk> m:nat; n:nat; k:nat; m #+ k = n #+ k \<rbrakk> \<Longrightarrow> m = n"
by(auto)

theorem diff_diff_inverse: "[| m < n; n:nat; m:nat |] ==> n #- (n #- m) = m"
proof -
  assume a: "m < n" "n:nat" "m:nat"
  then have "n #- m \<le> n" using diff_le_self by(auto)
  then have b: "n #- (n #- m) #+ (n #- m) = n" using add_diff_inverse2[of "n #- m" n] a by(auto)
  then have "m \<le> n" using a leI by(auto)
  then have "m #+ (n #- m) = n" using a add_diff_inverse by(auto)
  then have c: "n #- (n #- m) #+ (n #- m) = m #+ (n #- m)" using b by(auto)
  have d: "n #- m : nat" using a by(auto)
  then have "n #- (n #- m) : nat" using a by(auto)
  then show ?thesis using add_same_cancel[of "n #- (n #- m)" "m" "n #- m"] a c d by(auto)
qed

theorem add_0_eq_0: "[| n #+ m = 0; m:nat; n:nat |] ==> n = 0"
by(case_tac m, auto)

theorem mult_cancel: "[| n #* m = n #* p; 0 < n; n:nat; m:nat; p:nat |] ==> m = p"
by(auto)

declare nats_def [simp]

theorem mod_dep_type: "[| 0 < n; m:nat; n:nat |] ==> m mod n :nats(n)"
apply(auto)
by(rule mod_less_divisor)

theorem mod_lt: "[| 0 < n; m:nat; n:nat |] ==> m mod n < n"
by(rule mod_less_divisor)

theorem natsI: "[| m:nat; n:nat; m:n |] ==> m :nats(n)"
apply(auto)
by(rule ltI, simp_all)

theorem natsI2: "q:{ m:nat. m < n } ==> q: nats(n)"
by(simp)

theorem natsE: "[| m:nats(n); n:nat; [| m:nat; m < n |] ==> P |] ==> P"
by(auto)

lemma ball_le_nat: "n:nat \<Longrightarrow> ALL j:nat. j \<le> n \<longrightarrow> p(j) \<Longrightarrow> 
ALL j:nat. j < n \<longrightarrow> p(j)"
apply(auto)
by(drule leI, auto)

theorem ball_lt_nats: "[| ALL j:nats(succ(n)). p(j); ALL j:nats(n). p(j) ==> P; n:nat |] ==> P"
apply(auto)
by(drule ball_le_nat)

theorem mod_mult_self: "[| t:nat; n:nat; 0 < n; j:nats(n) |] ==> (n #* t #+ j) mod n = j"
apply(auto)
proof -
  assume a: "t ∈ nat" "n ∈ nat" "0 < n" "j ∈ nat" "j < n"
  then have b: "(n #* t #+ j) mod n = j mod n" using mod_mult_self1_raw [of t j n] by(simp add: add_commute) 
  have "j = j mod n" using a by(auto)
  then show ?thesis using b by(auto)
qed

lemma "\<lbrakk> m:nat; n:nat; a:nat; k:nat; (m mod n) = (a mod n) \<rbrakk> \<Longrightarrow> (m #+ k) mod n = (a #+ k) mod n"
apply(induct_tac k, auto)
by(simp add: mod_succ)  

lemma mod_diff_induct_lemma: 
  "⟦n ∈ nat; 0 < n; j ∈ nat; j < n; t = succ(ja); x ∈ nat; (n #+ n #* x #- j) mod n = (n #- j) mod n⟧
    \<Longrightarrow> (n #+ (n #+ n #* x) #- j) mod n = (n #- j) mod n"
proof -
  assume a: "n ∈ nat" "0 < n" "j ∈ nat" "j < n" "t = succ(ja)" 
            "x ∈ nat" "(n #+ n #* x #- j) mod n = (n #- j) mod n"
  then have "j < n #+ n #* x" using add_lt_larger_side by(simp add: add_commute)
  then have "n #+ (n #+ n #* x) #- j = n #+ ((n #+ n #* x) #- j)" 
    using diff_add_assoc[of j "n #+ n #* x" n ] a by simp
  then have "(n #+ (n #+ n #* x) #- j) mod n = (n #+ n #* x #- j) mod n" 
    using mod_add_self1 by simp
  then show ?thesis using a by simp
qed

theorem mod_diff: "[| t:nat; 0 < t; n:nat; 0 < n; j:nats(n) |] ==> 
                    (n #* t #- j) mod n = (n #- j) mod n"
apply(auto)
apply(drule zero_lt_lemma, auto)
apply(induct_tac ja, auto)
by(rule mod_diff_induct_lemma)

end
