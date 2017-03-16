(* ========================================================================= *)
(* FILE          : arm8bilScript.sml                                         *)
(* DESCRIPTION   : A transcompiler from arm8model to BIL model.              *)
(* AUTHOR        : (c) Roberto Metere, KTH - Royal Institute of Technology   *)
(* DATE          : 2015                                                      *)
(* ========================================================================= *)

open HolKernel boolLib bossLib Parse;
open wordsTheory;
open bilTheory;
open arm8Theory;

val _ = new_theory "arm8bil";
(* ------------------------------------------------------------------------- *)

(* This is to overload the combination not-equal, in order to have easier conversions to NotEqual in BIL model *)
val word_neq_def = Define `word_neq (a:α word) (b:α word) = ~(a = b)`;
val _ = overload_on ("≠",              Term`$word_neq`);

(* ------------------------------------------------------------------------- *)
(*  ARMv8 State - BIL State Bisimulation                                     *)
(* ------------------------------------------------------------------------- *)
val sim_invariant_def = Define `sim_invariant s env pco =
   (env "" = (NoType,Unknown)) ∧
   (env "R0" = (Reg Bit64,Int (Reg64 (s.REG 0w)))) ∧
   (env "R1" = (Reg Bit64,Int (Reg64 (s.REG 1w)))) ∧
   (env "R2" = (Reg Bit64,Int (Reg64 (s.REG 2w)))) ∧
   (env "R3" = (Reg Bit64,Int (Reg64 (s.REG 3w)))) ∧
   (env "R29" = (Reg Bit64,Int (Reg64 (s.REG 29w)))) ∧
   (env "R30" = (Reg Bit64,Int (Reg64 (s.REG 30w)))) ∧
   (env "ProcState_C" = (Reg Bit1,Int (bool2b s.PSTATE.C))) ∧
   (env "ProcState_N" = (Reg Bit1,Int (bool2b s.PSTATE.N))) ∧
   (env "ProcState_V" = (Reg Bit1,Int (bool2b s.PSTATE.V))) ∧
   (env "ProcState_Z" = (Reg Bit1,Int (bool2b s.PSTATE.Z))) ∧
   (env "arm8_state_PC" = (Reg Bit64,Int (Reg64 s.PC))) ∧
   (env "arm8_state_SP_EL0" = (Reg Bit64,Int (Reg64 s.SP_EL0))) ∧
   (∃v. env "tmp_R0" = (Reg Bit64,Int (Reg64 v))) ∧
   (∃v. env "tmp_R1" = (Reg Bit64,Int (Reg64 v))) ∧
   (∃v. env "tmp_R2" = (Reg Bit64,Int (Reg64 v))) ∧
   (∃v. env "tmp_R3" = (Reg Bit64,Int (Reg64 v))) ∧
   (∃v. env "tmp_R29" = (Reg Bit64,Int (Reg64 v))) ∧
   (∃v. env "tmp_R30" = (Reg Bit64,Int (Reg64 v))) ∧
   (∃v. env "tmp_ProcState_C" = (Reg Bit1,Int (Reg1 v))) ∧
   (∃v. env "tmp_ProcState_N" = (Reg Bit1,Int (Reg1 v))) ∧
   (∃v. env "tmp_ProcState_V" = (Reg Bit1,Int (Reg1 v))) ∧
   (∃v. env "tmp_ProcState_Z" = (Reg Bit1,Int (Reg1 v))) ∧
   (∃v. env "tmp_arm8_state_PC" = (Reg Bit64,Int (Reg64 v))) ∧
   (∃v. env "tmp_arm8_state_SP_EL0" = (Reg Bit64,Int (Reg64 v))) ∧
   (∃m.
      (env "arm8_state_MEM" = (MemByte Bit64,Mem Bit64 m)) ∧
      ∀a. m (Reg64 a) = Reg8 (s.MEM a)) /\
   ¬s.SCTLR_EL1.E0E ∧ (s.PSTATE.EL = 0w) ∧ (s.exception = NoException) /\
   (* remove from here and use assertions *)
   ¬s.SCTLR_EL1.SA0 /\
   ¬s.TCR_EL1.TBI0 /\
   ¬s.TCR_EL1.TBI1 /\
   (pco = SOME <|label := Address (Reg64 s.PC); index := 0|>)
      `;

(* ------------------------------------------------------------------------- *)
val _ = export_theory();
