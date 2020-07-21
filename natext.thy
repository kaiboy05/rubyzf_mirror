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

theorem diff_le_0: "[| m \<le> n; n:nat; m:nat |] ==> m #- n = 0"
apply(auto simp: diff_def)
oops

theorem add_lt_n: "[| x #+ n < y #+ n; n:nat; x:nat; y:nat |] ==> x < y"
oops

theorem diff_lt_0: "[| m < n; n:nat; m:nat |] ==> 0 < n #- m"
oops

theorem diff_add_comm: "[| m < n; n:nat; m:nat; k:nat|] ==> n #+ k #- m = k #+ (n #- m)"
oops

theorem n_gt_0_succ: "[| 0 < n; n: nat; !!x. [| n = succ(x); x:nat |] ==> P |] ==> P"
by(erule zero_lt_natE)

theorem mult_le_self: "[| 0 < m; n:nat; m:nat |] ==> n \<le> n #* m"
oops

theorem gt_not0: "[| 0 < n; n:nat |] ==> n~= 0"
oops

theorem diff_succ: "[| m \<le> n; n:nat; m:nat |] ==> succ(n) #- m = succ(n #- m)"
oops

theorem diff_diff_inverse: "[| m < n; n:nat; m:nat |] ==> n #- (n #- m) = m"
oops

theorem add_0_eq_0: "[| n #+ m = 0; m:nat; n:nat |] ==> n = 0"
oops

theorem mult_cancel: "[| n #* m = n #* p; 0 < n; n:nat; m:nat; p:nat |] ==> m = p"
oops

theorem mod_dep_type: "[| 0 < n; m:nat; n:nat |] ==> m mod n :nats(n)"
oops

theorem mod_lt: "[| 0 < n; m:nat; n:nat |] ==> m mod n < n"
oops

theorem natsI: "[| m:nat; n:nat; m:n |] ==> m :nats(n)"
oops

theorem natsI2: "q:{ m:nat. m < n } ==> q: nats(n)"
by(simp add: nats_def)

theorem natsE: "[| m:nats(n); n:nat; [| m:nat; m < n |] ==> P |] ==> P"
oops

theorem ball_lt_nats: "[| ALL j:nats(succ(n)). p(j); ALL j:nats(n). p(j) ==> P; n:nat |] ==> P"
oops

theorem mod_mult_self: "[| t:nat; n:nat; 0 < n; j:nats(n) |] ==> (n #* t #+ j) mod n = j"
oops

theorem mod_diff: "[| t:nat; 0 < t; n:nat; 0 < n; j:nats(n) |] ==> 
                    (n #* t #- j) mod n = (n #- j) mod n"
oops


end
