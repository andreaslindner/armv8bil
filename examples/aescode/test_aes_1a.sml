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


use "./aescode/aes_p.sml";

HOL_Interactive.toggle_quietdec();



val _ = new_constant(``f:word64 -> word8``);

val f_axiom = new_axiom("f_axiom",
      ``   (f 0x0001w = 02w)
        /\ (f 0x0002w = 18w)``);




TypeBase.mk_case (``x:word64``, [(``1w:word64``,``5w:word16``), (``3w:word64``,``44w:word16``),(``xx:word64``,``3w:word16``)]);

``1w:word8 - 2w:word8``


