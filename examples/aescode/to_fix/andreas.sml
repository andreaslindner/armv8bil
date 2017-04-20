HOL_Interactive.toggle_quietdec();
open HolKernel boolLib bossLib Parse;
open lcsymtacs utilsLib;
open wordsLib blastLib;
open aes_code;
open aes_mem;
open state_transformerTheory updateTheory arm8Theory;
open stateTheory;
open lcsymtacs arm8_stepTheory;
open state_transformerSyntax;
open arm8_stepLib;
open proofTools arithTheory;
open bilTheory arm8bilTheory;
open arm8bilLib;
open arm8stepbilLib;
open arm8bilInstructionLib;
open aesProp1CondTheory;
HOL_Interactive.toggle_quietdec();

(* ... *)

val goal = ``!s env. (Qb env /\ sim_invariant s env (SOME <|label := Address (Reg64 ^instrs_lstad); index := 0|>)) ==> Q s``;
val postcon_sim_proof = prove(``^goal``,
       (REPEAT STRIP_TAC)
  THEN (FULL_SIMP_TAC (simpLib.empty_ss) [Qb_def, postcond_arm, sim_invariant_def])
  THEN (Cases_on `^prog_counter`)

  THEN (FULL_SIMP_TAC (srw_ss()) [])
);

(*val _ = type_abbrev("bil_state", ``:environment # (programcounter option)``);*)

val _ = Datatype `bil_state = bilstate environment (programcounter option)`;
val sbil_env_def = Define `sbil_env (bilstate env pco) = env`;
val sbil_pco_def = Define `sbil_pco (bilstate env pco) = pco`;


val goal = ``!s:arm8_state s':arm8_state sbil:bil_state sbil':bil_state. (sim_invariant s (sbil_env sbil) (sbil_pco sbil)) ==> (sim_invariant s' (sbil_env sbil') (sbil_pco sbil')) ==> (Qbil sbil sbil') ==> (Qarm s s')``;

`` !sbil . (sim_invariant s' (sbil_env sbil') (sbil_pco sbil)) ``

``!s:bil_state. Ps(s)``
``!x. P(x)``

val postcond_thm = save_thm("postcond_thm", postcon_sim_proof);
