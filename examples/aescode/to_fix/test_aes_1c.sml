HOL_Interactive.toggle_quietdec();
open HolKernel boolLib bossLib Parse;
open lcsymtacs utilsLib;
open wordsLib blastLib;
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


(* use "./aescode/aes_p.sml"; *)

HOL_Interactive.toggle_quietdec();





val last_addr   = ``0x400D78w:word64``;

(* postcondition in ARM *)
val prog_counter   = ``a.PC = ^last_addr``;
val postcond_arm = Define `Q a = ^prog_counter`;


(* lifting and bil equivalent *)
val conv_val = (snd o dest_eq o concl o (SPEC ``a:arm8_state``)) postcond_arm;
val conv_bil = let val (x,_,_) = tc_exp_arm8_prefix conv_val "" in x end;
val Qb_def = Define `Qb env = (bil_eval_exp ^conv_bil env = Int (bool2b T))`;

/////// check invariant definition wrt program counter, bil PC and arm PC register preserving?!?!?!


(* proving postcondition transfer under simulation *)
val goal = ``!s env. (Qb env /\ sim_invariant s env (SOME <|label := Address (Reg64 ^last_addr); index := 0|>)) ==> Q s``;
val precon_sim_proof = prove(``^goal``,

(*
       (REPEAT STRIP_TAC)
  THEN (FULL_SIMP_TAC (simpLib.empty_ss) [sim_invariant_def, precond_arm, Pb_def])
  THEN (tac_expand)
  THEN (EVAL_TAC)
  THEN (FULL_SIMP_TAC (srw_ss()) [thm_if])
  THEN (FULL_SIMP_TAC (srw_ss()) [])
  THEN (`s.PC = ^first_addr` by (RW_TAC (srw_ss()) []))
  THEN (FULL_SIMP_TAC (srw_ss()) memf_axioms)
*)
);



