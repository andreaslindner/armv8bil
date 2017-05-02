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
 


fun PAT_UNDISCH pat thm =
    List.foldl (fn (tm,thm) =>
         (let val _ =  match_term pat tm in thm end)
         handle _ => (DISCH tm thm))
    (UNDISCH_ALL thm) ((hyp o UNDISCH_ALL) thm);

fun normalize_thm thm = 
    (* fix the invariant: *)
    let (* First step: reorder the assumptions so we have pc=v as first *)
        (* and the we use that to simplify the statement *)
        val th1_1 = PAT_UNDISCH ``s.PC = v`` thm;
        val pc_value = (List.hd (hyp th1_1));
        (* I do not rewrite the pc in bil_exec_step_n *)
        val th1_1 = PAT_UNDISCH ``(bil_exec_step_n a b) = c`` thm;
        val th1_2 = REWRITE_RULE [ASSUME pc_value] th1_1;
        val th1_3 = DISCH_ALL th1_2;
        (* Check that the pc is aligned *)
        val th_tmp = prove (``Aligned (^((snd o dest_eq) pc_value),4)``, SIMP_TAC (srw_ss()) [Aligned_def, Align_def]);
        val th1_4 = SIMP_RULE (srw_ss()) [th_tmp] th1_3;
    in  
        th1_4
    end;

fun get_term_from_ass_path pat thm =
    let val th1_1 = PAT_UNDISCH pat thm;
    in (List.hd (hyp th1_1))
    end;

fun extract_code thm =
    let val hs = ((hyp o UNDISCH_ALL) thm)
        val ex = List.filter (fn tm => is_exists tm) hs
    in List.hd ex end;
        

fun extract_side_cond thm = 
    let val th1 =  List.foldl (fn (tm,thm) =>
            (let val cs = strip_conj tm in
                if List.exists (fn tm1 => tm1 = ``(s.exception = NoException)``) cs then thm
                else (DISCH tm thm)
            end)
             handle _ => (DISCH tm thm))
          (UNDISCH_ALL thm) ((hyp o UNDISCH_ALL) thm);
    in List.hd (hyp th1) end;
    
fun extract_mem_cnd tm =
 list_mk_conj (List.filter (fn tm =>
    let val _ = match_term ``s.MEM a = v`` tm in true end
    handle _ => false) (strip_conj tm));

fun extract_other_cnd tm =
 let val other = (List.filter (fn tm =>
    let val _ = match_term ``s.MEM a = v`` tm in false end
    handle _ =>
      if       tm = ``¬s.SCTLR_EL1.E0E`` orelse tm = ``(s.PSTATE.EL = 0w)``
        orelse tm = ``(s.exception = NoException)`` orelse tm = ``¬s.SCTLR_EL1.SA0``
        orelse tm = ``¬s.TCR_EL1.TBI0`` orelse tm = ``¬s.TCR_EL1.TBI1``
      then false
      else true
 ) (strip_conj tm))
 in if other = [] then ``T`` else list_mk_conj other end;


fun get_PC_value_from_add thm = get_term_from_ass_path ``s.PC = v`` thm;

fun generate_sim_goal thms =
    let val thms_norm = List.map normalize_thm thms;
        val goal = `` (sim_invariant s env pco) /\
                      (NextStateARM8 s = SOME s1)
                   ``;
       val cnd_PC = List.foldl (fn (thm,cnd) => ``^cnd \/ ^(get_PC_value_from_add thm)``) ``F`` thms_norm;
       val cnd_PC = (snd o dest_eq o concl) (SIMP_CONV (srw_ss()) [] cnd_PC);
       val goal = ``^goal /\ ^cnd_PC``;
       val goal = List.foldl (fn (thm,cnd) =>
              ``^cnd /\ ^(extract_code thm) /\ ^(extract_mem_cnd (extract_side_cond thm))``) goal thms_norm;
       val side_end_cond = List.foldl (fn (thm,cnd) =>
              ``^cnd /\ ^(extract_mem_cnd (extract_side_cond thm))``) ``T`` thms_norm;
      val side_end_cond_1 = (snd o dest_eq o concl) (SIMP_CONV (srw_ss()) []   ``(\s.^side_end_cond) s1``);
      val goal = ``^goal ==>
           ?k. (
           (bil_exec_step_n
                 <|pco := pco;
                   pi := prog; environ := env; termcode := Unknown; debug := d1;
                   execs := e1|> k =
               bs1) ==>
           (((sim_invariant s1 bs1.environ bs1.pco) /\ ^side_end_cond_1)
            \/ (bs1.pco = NONE))
           )``;
   in goal end;
  

fun generate_sim2_goal thms =
    let val thms_norm = List.map normalize_thm thms;
        val goal = `` (sim_invariant s env pco)
                   ``;
       val cnd_PC = List.foldl (fn (thm,cnd) => ``^cnd \/ ^(get_PC_value_from_add thm)``) ``F`` thms_norm;
       val cnd_PC = (snd o dest_eq o concl) (SIMP_CONV (srw_ss()) [] cnd_PC);
       val goal = ``^goal /\ ^cnd_PC``;
       val goal = List.foldl (fn (thm,cnd) =>
              ``^cnd /\ ^(extract_code thm) /\ ^(extract_mem_cnd (extract_side_cond thm))``) goal thms_norm;
       val side_end_cond = List.foldl (fn (thm,cnd) =>
              ``^cnd /\ ^(extract_mem_cnd (extract_side_cond thm))``) ``T`` thms_norm;
      val side_end_cond_1 = (snd o dest_eq o concl) (SIMP_CONV (srw_ss()) []   ``(\s.^side_end_cond) s1``);
      val goal = ``^goal ==>
      	   (!k. (
           (bil_exec_step_n
                 <|pco := pco;
                   pi := prog; environ := env; termcode := Unknown; debug := d1;
                   execs := e1|> k =
               bs1) ==>
	   (bs1.pco <> NONE) ==>
	   (startLabel bs1.pco) ==>
	   (NextStateARM8 s = SOME s1) ==>
	   ((sim_invariant s1 bs1.environ bs1.pco) /\ ^side_end_cond_1)
	  ))``;
   in goal end;



(* missing *)
(* sim_invariant_def *)
(* does_match *)
(* align_conversion_thm *)
(* Do we really nead to solve the aligned or we can generate the assertion? *)
(* val thm = hd thms; *)
fun PROVE_SIM_TAC thm =
        fn (asl,goal) => (
            (FULL_SIMP_TAC (srw_ss()) [])
            THEN (EXISTS_TAC (
                 List.nth((snd o strip_comb o fst o dest_eq)
                          (get_term_from_ass_path ``a = bs1:stepstate`` thm),
                          1)
            ))
            THEN (SUBGOAL_THEN (extract_other_cnd (extract_side_cond thm))
                 (fn thm => ASSUME_TAC thm))
            THENL [(REV_FULL_SIMP_TAC (srw_ss()) [sim_invariant_def])
                 THEN (RW_TAC (srw_ss()) [])
                 (* this is a copy paste *)
                 THEN (fn (asl,g) =>
                   if (does_match g ``Aligned(x,y)``) then
                        ((REPEAT (PAT_ASSUM ``Aligned(x,y)`` (fn thm=> (ASSUME_TAC thm) THEN (UNDISCH_TAC (concl thm)))))
                         THEN (REWRITE_TAC [align_conversion_thm])
                         THEN (blastLib.BBLAST_TAC))
                         (asl,g)
                   else (ALL_TAC)(asl,g)
                 ),
                 ALL_TAC
            ]
            THEN (REPEAT DISCH_TAC)
            THEN (ASSUME_TAC thm)
            THEN (REV_FULL_SIMP_TAC (srw_ss()) [sim_invariant_def])
         )(asl,goal);



(* Sample instructions *)


val instructions2 = [
"d10103ff","f9000fe0"
(* "d10103ff","f9000fe0","f9000be1","f90007e2","b90007e3","b9003bff","14000009" *)
];
val pcs2 = snd (List.foldl (fn (code, (pc, pcs)) =>
  ((snd o dest_eq o concl o EVAL) ``^pc+4w``, List.concat[pcs, [pc]])
) (``0w:word64``, []) instructions2);
val ops2 = ListPair.zip (instructions2, pcs2);
val ids2 = List.tabulate ((List.length ops2), (fn x=> x));

val instructions = [
"d10103ff"
,"f9000fe0"
(* ,"f9000be1","f90007e2","b90007e3","b9003bff","14000009",
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
*)
];
val pcs = snd (List.foldl (fn (code, (pc, pcs)) =>
  ((snd o dest_eq o concl o EVAL) ``^pc+4w``, List.concat[pcs, [pc]])
) (``0w:word64``, []) instructions);
val ops = ListPair.zip (instructions, pcs);
val ids = List.tabulate ((List.length ops), (fn x=> x));

(* Experiments to test the simulation tactic for each single instruction *)


print "*****START*************\n*****START*************\n*****START*************\n";
List.foldl (fn (id, x) =>
  let val _ = print "******************************\n"
      val (code, pc) = (List.nth(ops, id))
      val _ = print (String.concat ["Lifting instruction: ", code, "\n"])
  in
    (let val thms = [tc_one_instruction2_by_bin code pc ``\x.x<+0x100000w:word64``];
         val thm = List.hd thms;
         val goal = generate_sim_goal thms;
         val thm1 = prove (``^goal``,
               (REPEAT STRIP_TAC)
               (* One case for each value of the PC *)
               THEN (PROVE_SIM_TAC thm)
               );
     in (* print_thm thm1 ; *) print "\n" end
     handle _ => print "-------FAILURE-------\n");
     1
  end
) 1 ids;




(* Experiments to test the simulation tactic for each single instruction on the big theorem *)

val id = 0;
val id = 28;
val id = 70;
val id = 19;
val id = 0;
val id = (List.length ops)-1;
val x = 1;
val (instr, pc_value) = (List.nth(ops, id));
val thms = [tc_one_instruction2_by_bin (fst (List.nth(ops, id))) (snd (List.nth(ops, id))) ``\x.x<+0x100000w:word64``];

val thm = List.hd thms;
val goal = generate_sim_goal thms;
prove (``^goal``,
      (REPEAT STRIP_TAC)
      (* One case for each value of the PC *)
      THEN (PROVE_SIM_TAC thm)
);


(* Experiments to test the simulation tactic for all instruction and on the showing that the program remains in memory *)

val curr_ops = ops2;
print "*****START*************\n*****START*************\n*****START*************\n";
(* 74 s 7 instructions *)
val thms = List.map (fn (code, pc) => tc_one_instruction2_by_bin code pc ``\x.x<+0x100000w:word64``) curr_ops;
(* 1 s??? 7 instructions *)
val goal = generate_sim_goal thms;

val mem_cnd = (snd o dest_conj o fst o dest_disj o snd o dest_imp o snd o dest_exists o snd o strip_imp) goal;
val mem_hyp = (snd o dest_eq o concl o EVAL) ``(\s1. ^mem_cnd) s``;

val mem_thm = prove(`` ^mem_hyp ==>
                           (!a. (λx. x <₊ 0x100000w) a ⇒ (s.MEM a = s1.MEM a)) ==>
                           ^mem_cnd``,
   (REPEAT STRIP_TAC)
   THEN (FULL_SIMP_TAC (srw_ss()) []));
(* 1.6 s 7 instructions, 544 s 90 instructions *)

val thm1 = prove (``^goal``,
      (ASSUME_TAC mem_thm)
      THEN (REPEAT DISCH_TAC)
      THEN (FULL_SIMP_TAC (srw_ss()) [])
      (* One case for each value of the PC *)
      THENL (List.map PROVE_SIM_TAC thms)
);
(* 16.137s *)

(* Attempt to prove the other side of the simulation *)

val curr_ops = ops2;
print "*****START*************\n*****START*************\n*****START*************\n";
(* 74 s 7 instructions *)
val thms = List.map (fn (code, pc) => tc_one_instruction2_by_bin code pc ``\x.x<+0x100000w:word64``) curr_ops;
(* 1 s??? 7 instructions *)
val goal = generate_sim2_goal [List.hd thms];

prove (``^goal``,
      (REPEAT STRIP_TAC)
      List.hd thms





startLabel bs1.pco = pco.block_index = 0

! k < 5. bs1.pco.block_index <> 0