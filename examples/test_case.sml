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


(* 0000000000000000 <internal_mul>: *)
val instructions = [
"d10103ff","f9000fe0","f9000be1","f90007e2","b90007e3","b9003bff","14000009",
"b9803be0","d37ff800","f94007e1","8b000020","7900001f","b9403be0","11000400",
"b9003be0","b94007e0","531f7801","b9403be0","6b00003f","54fffe8c","b94007e0",
"51000400","b9003fe0","14000043","b9803fe0","d37ff800","f9400fe1","8b000020",
"79400000","53003c00","f90017e0","f9001bff","b94007e0","51000400","b9003be0",
"1400002a","b9803be0","d37ff800","f9400be1","8b000020","79400000","53003c01",
"f94017e0","9b007c20","f9401be1","8b000020","f9001be0","b9403fe1","b9403be0",
"0b000020","93407c00","91000400","d37ff800","f94007e1","8b000020","79400000",
"53003c00","f9401be1","8b000020","f9001be0","b9403fe1","b9403be0","0b000020",
"93407c00","91000400","d37ff800","f94007e1","8b000020","f9401be1","53003c21",
"79000001","f9401be0","d350fc00","f9001be0","b9403be0","51000400","b9003be0",
"b9403be0","6b1f001f","54fffaaa","b9803fe0","d37ff800","f94007e1","8b000020",
"f9401be1","53003c21","79000001","b9403fe0","51000400","b9003fe0","b9403fe0",
"6b1f001f","54fff78a","910103ff","d65f03c0"
];


(* 0000000000000000 <internal_add_shifted>: *)
val instructions2 = [
"d100c3ff",
"f90007e0",
"b90007e1",
"b90003e2",
"b94003e0",
"11003c01",
"6b1f001f",
"1a80b020",
"13047c00",
"11000400",
"b9002fe0",
"b94003e1",
"131f7c20",
"531c7c00",
"0b000021",
"12000c21",
"4b000020",
"b9001fe0",
"b9401fe0",
"b94007e1",
"1ac02020",
"2a0003e0",
"f90013e0",
"14000017",
"b9802fe0",
"d37ff800",
"f94007e1",
"8b000020",
"79400000",
"53003c00",
"f94013e1",
"8b000020",
"f90013e0",
"b9802fe0",
"d37ff800",
"f94007e1",
"8b000020",
"f94013e1",
"53003c21",
"79000001",
"f94013e0",
"d350fc00",
"f90013e0",
"b9402fe0",
"11000400",
"b9002fe0",
"f94013e0",
"eb1f001f",
"54fffd01",
"9100c3ff",
"d65f03c0"];
val instructions = List.concat[instructions, instructions2];

List.length instructions;

(* internal_mod *)
val instructions3 = [
"a9b97bfd",
"910003fd",
"f9001fa0",
"b90037a1",
"f90017a2",
"b90033a3",
"f90013a4",
"b9001fa5",
"f94017a0",
"79400000",
"790097a0",
"b94033a0",
"7100041f",
"540000ad",
"f94017a0",
"79400400",
"7900dfa0",
"14000002",
"7900dfbf",
"b90067bf",
"140000de",
"b94067a0",
"6b1f001f",
"54000061",
"b9006bbf",
"1400000e",
"b98067a0",
"d37ff800",
"d1000800",
"f9401fa1",
"8b000020",
"79400000",
"b9006ba0",
"b98067a0",
"d37ff800",
"d1000800",
"f9401fa1",
"8b000020",
"7900001f",
"b94037a0",
"51000401",
"b94067a0",
"6b00003f",
"54000061",
"b9004fbf",
"14000008",
"b98067a0",
"91000400",
"d37ff800",
"f9401fa1",
"8b000020",
"79400000",
"b9004fa0",
"b9406ba0",
"d370bc01",
"b98067a0",
"d37ff800",
"f9401fa2",
"8b000040",
"79400000",
"53003c00",
"8b000020",
"f9002fa0",
"794097a0",
"f9402fa1",
"9ac00820",
"b90057a0",
"794097a1",
"f9402fa0",
"9ac10802",
"9b017c41",
"cb010000",
"b90047a0",
"7940dfa1",
"b94057a0",
"9b007c20",
"f9002fa0",
"b94047a0",
"d370bc01",
"b9404fa0",
"8b000021",
"f9402fa0",
"eb00003f",
"54000362",
"b94057a0",
"51000400",
"b90057a0",
"7940dfa0",
"f9402fa1",
"cb000020",
"f9002fa0",
"794097a1",
"b94047a0",
"0b000020",
"12003c00",
"b90047a0",
"794097a1",
"b94047a0",
"6b00003f",
"54000168",
"b94047a0",
"d370bc01",
"b9404fa0",
"8b000021",
"f9402fa0",
"eb00003f",
"54000082",
"b94057a0",
"51000400",
"b90057a0",
"b90053bf",
"b94033a0",
"51000400",
"b90063a0",
"14000037",
"b94057a1",
"b98063a0",
"d37ff800",
"f94017a2",
"8b000040",
"79400000",
"53003c00",
"9b007c20",
"f9002fa0",
"b94053a0",
"f9402fa1",
"8b000020",
"f9002fa0",
"f9402fa0",
"d350fc00",
"b90053a0",
"f9402fa0",
"53003c01",
"b94067a2",
"b94063a0",
"0b000040",
"93407c00",
"d37ff800",
"f9401fa2",
"8b000040",
"79400000",
"6b00003f",
"54000089",
"b94053a0",
"11000400",
"b90053a0",
"b94067a1",
"b94063a0",
"0b000020",
"93407c00",
"d37ff800",
"f9401fa1",
"8b000020",
"b94067a2",
"b94063a1",
"0b010041",
"93407c21",
"d37ff821",
"f9401fa2",
"8b010041",
"79400022",
"f9402fa1",
"53003c21",
"4b010041",
"53003c21",
"79000001",
"b94063a0",
"51000400",
"b90063a0",
"b94063a0",
"6b1f001f",
"54fff90a",
"b94053a1",
"b9406ba0",
"6b00003f",
"54000620",
"f9002fbf",
"b94033a0",
"51000400",
"b90063a0",
"14000026",
"b98063a0",
"d37ff800",
"f94017a1",
"8b000020",
"79400000",
"53003c00",
"f9402fa1",
"8b000020",
"f9002fa0",
"b94067a1",
"b94063a0",
"0b000020",
"93407c00",
"d37ff800",
"f9401fa1",
"8b000020",
"79400000",
"53003c00",
"f9402fa1",
"8b000020",
"f9002fa0",
"b94067a1",
"b94063a0",
"0b000020",
"93407c00",
"d37ff800",
"f9401fa1",
"8b000020",
"f9402fa1",
"53003c21",
"79000001",
"f9402fa0",
"d350fc00",
"f9002fa0",
"b94063a0",
"51000400",
"b90063a0",
"b94063a0",
"6b1f001f",
"54fffb2a",
"b94057a0",
"51000400",
"b90057a0",
"f94013a0",
"eb1f001f",
"540001a0",
"b94037a1",
"b94033a0",
"4b000021",
"b94067a0",
"4b000020",
"531c6c01",
"b9401fa0",
"0b000020",
"2a0003e2",
"b94057a1",
"f94013a0",
"94000000",
"b94067a0",
"11000400",
"b90067a0",
"b94037a1",
"b94033a0",
"4b000021",
"b94067a0",
"6b00003f",
"54ffe3ca",
"a8c77bfd",
"d65f03c0"]

val instructions = List.concat[instructions, instructions3];

List.length instructions;

List.foldl (fn (code, pc) =>
  let val _ = print "******************************\n"
      val _ = print (String.concat ["Lifting instruction: ", code, "\n"])
  in
    (let val th = tc_one_instruction2_by_bin code pc ``\x.x<+0x100000w:word64``;   
     in print_thm th ; print "\n" end
     handle _ => print "-------FAILURE-------\n");
     ((snd o dest_eq o concl o EVAL) ``^pc+4w``)
  end
) ``0w:word64`` instructions;

