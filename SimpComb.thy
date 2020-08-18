theory SimpComb
imports Wiring
begin

definition inv' :: "[i, i, i] \<Rightarrow> i" where
  "inv'(A,B,R) == lwir(B,A) ;; [[Id(B), [[R,Id(A)]]]] ;; rwir(B,A)"

definition "inv" :: "i \<Rightarrow> i" ("(_~)" [70] 70) where
  "R~ == inv'(dtyp(R), rtyp(R), R)"

definition conj :: "[i, i] \<Rightarrow> i" where
  "conj(R,S) == S ;; R ;; (S~)"

definition Fst :: "[i, i] \<Rightarrow> i" where
  "Fst(A,R) == [[R, Id(A)]]"

definition Snd :: "[i, i] \<Rightarrow> i" where
  "Snd(A,R) == [[Id(A), R]]"

definition below' :: "[i, i, i, i, i, i, i, i, i] \<Rightarrow> i" where
  "below'(A,B,C,De, E, F, G, R, S) ==
    reorg(A,E,F) ;; Snd(A,S) ;; (reorg(A,B,G)~) ;;
    Fst(G,R) ;; reorg(C, De, G)"

definition below :: "[i, i] \<Rightarrow> i" ("(_ ||/ _)" [67, 66] 66) where
  "R || S == below'(ddtyp(R), rdtyp(R), drtyp(R), rrtyp(R),
                    ddtyp(S), rdtyp(S), rrtyp(S), R, S)"

definition beside :: "[i, i] \<Rightarrow> i" ("(_ <~~>/ _)" [67, 66] 66) where
  "(R <~~> S) == ((R)~ || (S)~)~"

definition loop2' :: "[i, i, i, i] \<Rightarrow> i" where
  "loop2'(A,B,C,R) == 
    lwir(A,B) ;; (reorg(A,B,B)~) ;; Fst(B,R) ;; reorg(C,B,B) ;; (lwir(C,B)~)"

definition loop2 :: "i \<Rightarrow> i" where
  "loop2(R) == loop2'(ddtyp(R), rdtyp(R), drtyp(R), R)"

definition loop4' :: "[i, i, i, i, i, i] \<Rightarrow> i" where
  "loop4'(A,B,C,De, E, R) ==
    cross(A,C) ;; loop2(reorg(C,A,B) ;; cross(C,A*B) ;; R ;; (reorg(De, E, B)~))"

definition loop4 :: "i \<Rightarrow> i" where
  "loop4(R) == loop4'(domain(ddtyp(R)), range(ddtyp(R)),
                      rdtyp(R), drtyp(R), domain(rrtyp(R)), R)"



end