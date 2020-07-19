theory natext
imports ZF.Nat
begin

definition nats :: "i ⇒ i" where
  "nats(n) == {m:nat. m < n}"

end
