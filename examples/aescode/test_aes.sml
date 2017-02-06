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

List.foldl (fn (code, pc) =>
  let val _ = print "******************************\n"
      val _ = print (String.concat ["Lifting instruction: ", code, "\n"])
  in
    (let val th = tc_one_instruction2_by_bin code pc ``\x.x<+0x100000w:word64``;   
     in print_thm th ; print "\n" end
     handle _ => print "-------FAILURE-------\n");
     ((snd o dest_eq o concl o EVAL) ``^pc+4w``)
  end
) first_addr instructions;

