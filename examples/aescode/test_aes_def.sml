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
HOL_Interactive.toggle_quietdec();

val instructions = [
"d10103ff"
];

use "./aescode/aes.sml";







(*
val first_addr = ``0x400520w:word64``;
val last_addr = ``0x400bd8w:word64``;
val last_addr = (snd o dest_eq o concl o EVAL) ``^last_addr + 0x4w``

val prog_size = ``0x10000w:word64``;
val last_addr = (snd o dest_eq o concl o EVAL) ``^first_addr + ^prog_size``

val fault_wt_mem = ``\x.((^first_addr)<=+x)/\(x<+(^last_addr))``;



val code = "d10103ff";
val pc = first_addr;
(*val fault_wt_mem = ``\x.x<+0x100000w:word64``;*)
val (goal,certs,step,p) = tc_one_instruction_goal code pc fault_wt_mem;
*)


val fault_wt_mem = ``\x.((^first_addr)<=+x)/\(x<+(^next_addr))``;
val fault_wt_mem = ``\x.x<+0x100000w:word64``;


List.foldl (fn (code, pc) =>
  let val _ = print "******************************\n"
      val _ = print (String.concat ["Lifting instruction: ", code, "\n"])
  in
    (let
       val (goal,_,_,_) = tc_one_instruction_goal code pc fault_wt_mem;
       val th = Define `instr_sim ^pc s s1 prog pco env bs1 d1 e1 = ^goal`;
     in print_thm th ; print "\n" end
     handle _ => print "-------FAILURE-------\n");
     ((snd o dest_eq o concl o EVAL) ``^pc+4w``)
  end
) first_addr instructions;

