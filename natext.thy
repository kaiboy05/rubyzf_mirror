theory natext
imports ZF.Arith
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

theorem diff_lt_0: "[| m < n; n:nat; m:nat |] ==> 0 < n #- m"
apply(simp add: less_diff_conv)
done


theorem diff_add_comm: "[| m < n; n:nat; m:nat; k:nat|] ==> n #+ k #- m = k #+ (n #- m)"
apply(simp add: add_commute)
apply(drule diff_lt_0, assumption+)
oops

theorem n_gt_0_succ: "[| 0 < n; n: nat; !!x. [| n = succ(x); x:nat |] ==> P |] ==> P"
by(erule zero_lt_natE)

find_theorems name: raw_mult
thm mult_def

find_theorems "_ #+ _ \<le> _"
find_theorems "0 #+ _"

thm add_le_mono1

lemma refl_add_help: "[| n:nat; m:nat |] ==> 0 #+ n \<le> m #+ n" 
by(rule add_le_mono1, simp)

theorem mult_le_self: "[| 0 < m; n:nat; m:nat |] ==> n \<le> n #* m"
apply(case_tac m, auto)
apply(simp add: refl_add_help)
oops

theorem gt_not0: "[| 0 < n; n:nat |] ==> n~= 0"
apply(auto)
done

find_theorems "succ(_) = _ #+ _"
find_theorems name: sym

theorem diff_succ: "[| m \<le> n; n:nat; m:nat |] ==> succ(n) #- m = succ(n #- m)"
apply(unfold succ_add_1)
oops

find_theorems "_ #- _"

theorem diff_diff_inverse: "[| m < n; n:nat; m:nat |] ==> n #- (n #- m) = m"
oops

theorem add_0_eq_0: "[| n #+ m = 0; m:nat; n:nat |] ==> n = 0"
apply(case_tac m)
apply(auto)
done

find_theorems "_ #* _ = _ #* _"

theorem mult_cancel: "[| n #* m = n #* p; 0 < n; n:nat; m:nat; p:nat |] ==> m = p"
oops

find_theorems "_ mod _"
find_theorems "raw_mod"

declare nats_def [simp]

theorem mod_dep_type: "[| 0 < n; m:nat; n:nat |] ==> m mod n :nats(n)"
apply(auto)
oops

theorem mod_lt: "[| 0 < n; m:nat; n:nat |] ==> m mod n < n"
oops

find_theorems "_ < _ \<Longrightarrow>_ : _"
find_theorems "_ < _" name: Ordinal

theorem natsI: "[| m:nat; n:nat; m:n |] ==> m :nats(n)"
apply(auto)
by(rule ltI, simp_all)

theorem natsI2: "q:{ m:nat. m < n } ==> q: nats(n)"
by(simp)

theorem natsE: "[| m:nats(n); n:nat; [| m:nat; m < n |] ==> P |] ==> P"
by(auto)

theorem ball_lt_nats: "[| ALL j:nats(succ(n)). p(j); ALL j:nats(n). p(j) ==> P; n:nat |] ==> P"
  apply(auto)
oops

theorem mod_mult_self: "[| t:nat; n:nat; 0 < n; j:nats(n) |] ==> (n #* t #+ j) mod n = j"
oops

theorem mod_diff: "[| t:nat; 0 < t; n:nat; 0 < n; j:nats(n) |] ==> 
                    (n #* t #- j) mod n = (n #- j) mod n"
oops


end
