(* ----------------------------------------*)
(*      Type Checking Tactics              *)
(* ----------------------------------------*)
(* Extended to solve n < j *)
(*
fun is_rigid_elem (Const("Trueprop", _) $ (Const("op :", _) $ a $ _))
  = not(is_Var (head_of a)) |
    is_rigid_elem (Const("Trueprop", _) $ (Const("op <", _) $ a $ b))
  = not(is_Var (head_of a)) andalso (not (is_Var (head_of b))) |
    is_rigid_elem _ = false;

(* Try solving a:A by assumption provided a is rigid! *)
fun test_assume_tac ctxt = 
  SUBGOAL(fn (prem, i) =>
    if is_rigid_elem (Logic.strip_assums_concl prem)
    then assume_tac ctxt i
    else eq_assume_tac i
  );

(*  Type checking solves a:?A (a rigid, ?A maybe flexible).
    match_tac is too strict; would refuse to instantiate ?A *)

fun typechk_step_tac ctxt tyrls = 
  FIRSTGOAL (test_assume_tac ctxt ORELSE' resolve_tac tyrls 4);


fun typechk_tac tyrls = REPEAT (typechk_step_tac tyrls);

val basictypeinfo = Unsynchronized.ref([]:thm list);

fun addT typelist = (basictypeinfo := (typelist @(!basictypeinfo)));

fun typeit trls = (typechk_tac (trls @ (!basictypeinfo)));

addT ZF_typechecks;

fun typegoal trls = (type_auto_tac trls (!basictypeinfo));



fun typchk trls tac = 
  tac THEN
  (typechk_tac (trls @ (!basictypeinfo)));



fun resolve_tac_c trls thl i = (typchk trls (resolve_tac thl i));

fun eresolve_tac_c trls thl i =
  SELECT_GOAL (typchk trls (eresolve_tac thl 1)) i;

(* ----------------------------------------*)
(*      Other useful tactics               *)
(* ----------------------------------------*)

fun rotate n i = EVERY(replicate n (etac revcut_rl i));

fun REPEAT_n n tac =
  if (n < 1) then
    all_tac
  else
    ((REPEAT_n (n-1) tac) THEN tac);

fun unfold_once ctxt rl i =
  SELECT_GOAL (EVERY 
    [ rewrite_goals_tac ctxt [rl],
      asm_full_simp_tac (ZF_ss addsimps [rec_succ]) i,
      fold_goals_tac [rl]]) 1;
(* ----------------------------------------*)
(*      Extensions to simplification sets  *)
(* ----------------------------------------*)

fun type_ss ty ss = 
  ss setsolver
    (fn prems => resolve_tac (triv_rls@prems)
        ORELSE' assume_tac
        ORELSE' etac FalseE
        ORELSE' (type_auto_tac ty prems));

fun if_split ss = (ss setloop (split_tac [expand_if]));

fun ssE cs ss   = (ss setloop (SELECT_GOAL (safe_tac cs)));

(* ----------------------------------------*)
(*      Extensions to simplification sets  *)
(* ----------------------------------------*)

fun type_rel_elem trls i =
  (
    (typchk trls (forward_tac [mem_rel_type] i))
    THEN (eresolve_tac [conjE] i)
  );

fun split_equal_trls =
  typchk trls 
    ( (rtac equalityI 1) 
      THEN (ALLGOALS (rtac subset_rel)) );

fun prove_equal trls i =
  SELECT_GOAL 
    ( (split_equal tris)
      THEN
      (TRYALL (fn i => type_rel_elem trls i)) ) i;

(* ----------------------------------------*)
(*      RubyType Tactics                   *)
(* ----------------------------------------*)

val Rubytypeinfo = ref([]:thm list);

fun addR typelist = (Rubytypeinfo := !Rubytypeinfo @ typelist);

fun typeR trls = (tpechk_tac (trls @ (!Rubytypeinfo) @ ZF_typechecks));

(* ----------------------------------------*)
(*      Tactics to construct values        *)
(* ----------------------------------------*)

fun build_back i = (
  (REPEAT
    (
      ((eresolve_tac [SigmaE, sig_pairE, sig_nlistOE, sig_ssnocE])
      ORELSE' assume_tac) i
    )
  )
  THEN (REPEAT (hyp_subst_tac i))
);

fun build_front i = (
  (REPEAT
    (eresolve_tac [SigmaE, sig_pairE, sig_nlistOE, sig_nlistE] i)
  )
  THEN (REPEAT(hyp_subst_tac i))
);
*)









