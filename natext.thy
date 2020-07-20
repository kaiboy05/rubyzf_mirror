theory natext
imports ZF.Arith
begin

find_theorems "_ #- _"
find_theorems name: raw_diff

definition nats :: "i \<Rightarrow> i" where
  "nats(n) == {m:nat. m < n}"

theorem le_in_succ: "[| i \<le> n; n: nat; i:nat|] ==> i:succ(n)"
apply(auto simp: ltD ltE)
done

theorem succ_add_1: "n:nat ==> succ(n) = n #+ 1"
apply(auto)
done

theorem diff_le_0: "[| m \<le> n; n:nat; m:nat |] ==> m #- n = 0"
apply(auto simp: diff_def)
oops

theorem add_lt_n: "[| x #+ n < y #+ n; n:nat; x:nat; y:nat |] ==> x < y"
oops

theorem diff_lt_0: "[| m < n; n:nat; m:nat |] ==> 0 < n #- m"
oops

theorem diff_add_comm: "[| m < n; n:nat; m:nat; k:nat|] ==> n #+ k #- m = k #+ (n #- m)"
oops








end
