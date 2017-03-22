(* HOL_Interactive.toggle_quietdec(); *)
open HolKernel boolLib bossLib Parse;
open lcsymtacs utilsLib;
open wordsLib blastLib;
open aes;
open stateTheory;
open state_transformerTheory updateTheory arm8Theory;
open lcsymtacs stateTheory arm8_stepTheory; 
open lcsymtacs arm8_stepTheory;
open state_transformerSyntax;
open arm8_stepLib;
open arithTheory;
open bilTheory arm8bilTheory;
open arm8bilLib;
open arm8stepbilLib;
open arm8bilInstructionLib;
(* HOL_Interactive.toggle_quietdec(); *)

val _ = new_theory "aesCode";

(* the ARM code binary and locations *)
(* ---------------------- *)

(*
val instructions = [
"d10103ff",
"d10103ff"
];
val first_addr   = ``0x400520w:word64``;
val next_addr    = ``0x400D7Cw:word64``;

use "./aescode/aes.sml";
*)

val instructions = [List.hd instructions];

(* TODO: we need a proper program region function *)
val fault_wt_mem = ``\x.x<+0x100000w:word64``;


(* lifting the code and extracting the BIL blocks *)
(* ---------------------- *)
val inst_pcs = List.tabulate ((List.length instructions), fn i =>
  (List.nth (instructions, i),
   ((snd o dest_eq o concl o EVAL) ``^first_addr+(4w*^(wordsSyntax.mk_wordii (i, 64)))``))
);

val thms = List.map (fn (code, pc) =>
    let
       val (goal,_,_,_) = tc_one_instruction_goal code pc fault_wt_mem;
       val th = ASSUME goal;
     in th
  end) inst_pcs;

val bil_blocks = List.map (fn thm =>
  let val thm1 = SIMP_RULE (srw_ss()) [] thm in
(snd o pairSyntax.dest_pair o optionSyntax.dest_some o snd o dest_eq o snd o dest_exists o Option.valOf)
  (List.find (is_exists) ((fst o strip_imp o concl) thm1))
  end) thms;

val bil_program = listSyntax.mk_list (bil_blocks, ``:bil_block_t``);


(* definition: bil_program as BIL block list from instruction lifter output *)
(* ---------------------- *)
val aes_bil_program_def = Define `aes_bil_program = ^bil_program`;

val _ = export_theory();
