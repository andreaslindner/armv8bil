
(*   2c:   7900001f        strh    wzr, [x0] *)
val inst = `MOV X1, #1`;
val code = arm8AssemblerLib.arm8_code `MOV X1, #1`;
val instr = (hd code);
val instr = "13047c00";
val pc_value = ``376w:word64``;

val id = 1;
val x = 1;
val (instr, pc_value) = (List.nth(ops, id));

(* 2.11 seconds *)
  val fault_wt_mem = ``\x.x<+0x100000w:word64``;
  val (p, certs, [step]) = tc_stmt_arm8_hex instr;
  val (sts, sts_ty) = listSyntax.dest_list p;
  (* manually add the memory fault *)
  val (memory_check_needed, assert_stm, assert_cert) = generate_assert step fault_wt_mem;
  val sts = List.concat [assert_stm, sts];
  val certs = List.concat [assert_cert, certs];
  (* other conditions: like memory alignment *)
  val side_cnd = extract_other_cnd_from_step step;
  val (side_check_needed, assert_stm1, assert_cert1) = generate_assert_side side_cnd;
  val sts = List.concat [assert_stm1, sts];
  val certs = List.concat [assert_cert1, certs];
  (* manually add the final jump *)
  val s1 = (optionSyntax.dest_some o snd o dest_eq o concl) step;
  val new_pc_val = (snd o dest_eq o concl o EVAL) ``^s1.PC``;
  (* as usual this can be unchanged *)
  val new_pc_val1 = (snd o dest_eq o concl o (SIMP_CONV (srw_ss()) [ASSUME ``s.PC = ^pc_value``])) new_pc_val
                    handle _ => new_pc_val;
  val (sts, certs) = if wordsSyntax.is_word_literal new_pc_val1 then
                        let val (b_v1, _, t_v1) = tc_exp_arm8 new_pc_val1
                        in
                          (List.concat [sts, [``Jmp (Const (Reg64 (^new_pc_val1)))``]],
                           List.concat [certs, [t_v1]]) end
                     else if is_cond new_pc_val1 then
                        let val (c,v1,v2) = dest_cond new_pc_val1
                            val (b_c, _, t_c) = tc_exp_arm8 c
                            val (b_v1, _, t_v1) = tc_exp_arm8 v1
                            val (b_v2, _, t_v2) = tc_exp_arm8 v2
                            val ncerts = LIST_CONJ(List.map (UNDISCH_ALL o SPEC_ALL) [t_c, t_v1, t_v2]);
                            val ncerts = ((GEN ``env:environment``) o (GEN ``s:arm8_state``) o DISCH_ALL) ncerts;
                         in (List.concat [sts, [``CJmp ^b_c ^b_v1 ^b_v2``]],
                             List.concat [certs, [ncerts]]) end
                     else
                        let val (b_v1, _, t_v1) = tc_exp_arm8 new_pc_val1
                            val b_v1 = ((snd o dest_eq o concl o (SIMP_CONV (srw_ss()) [r2s_def])) b_v1)
                             handle _ => b_v1;
                            val t_v1 = SIMP_RULE (srw_ss()) [r2s_def] t_v1;
                            in (List.concat [sts, [``Jmp ^b_v1``]],
                              List.concat [certs, [t_v1]]) end
  (* standard section *)
  val p = listSyntax.mk_list(sts,sts_ty);
	val goal = tc_gen_goal p certs step pc_value fault_wt_mem;
  
	val thm = prove(``^goal``,
      (REWRITE_TAC [sim_invariant_def])
			THEN (DISCH_TAC) THEN (DISCH_TAC) THEN (DISCH_TAC) THEN (DISCH_TAC) THEN (DISCH_TAC)
		        THEN (FULL_SIMP_TAC (srw_ss()) [])
			(* for every instruction, plus 1 since the fixed jump has no certificate *)
			THEN (MAP_EVERY (ONE_EXEC_MAIN certs p pc_value) (List.tabulate (List.length certs, fn x => x+1)))
			(* Computation completed *)
			THEN (FULL_SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
			THEN DISCH_TAC
      (* Prove that every assumption of the step theorem is met *)
      THEN (MAP_EVERY (fn tm =>
              (SUBGOAL_THEN tm ASSUME_TAC)
              THENL [
                (FULL_SIMP_TAC (srw_ss()) [align_conversion_thm, markerTheory.Abbrev_def]),
                (* foced to do a full simp_tac due to the next simplification *)
                (FULL_SIMP_TAC (myss) [])
              ]
            )
            (get_side_step_cnd (hyp step)))
			(* use the step theorem *)
			THEN (ASSUME_TAC (UNDISCH_ALL (SIMP_RULE myss [ASSUME ``s.PC=^pc_value``] (DISCH_ALL step))))
			THEN (FULL_SIMP_TAC (srw_ss()) [])
      (* Manually abbreviate the memory condition *)
      THEN (Q.ABBREV_TAC `mem_cond = ^((snd o dest_eq o concl o EVAL) ``∀a. (\x.x<+0x100000w:word64) a ⇒ (s.MEM a = s1.MEM a)``)`)
			THEN (RW_TAC (srw_ss()) [combinTheory.UPDATE_def, bool2b_def])
      (* other part of the invariant: basically show that the code does not mess up with other stuff *)
      THEN (fn (asl,g) =>
        if (does_match g ``Aligned(x,y)``) then
             ((REPEAT (PAT_ASSUM ``Aligned(x,y)`` (fn thm=> (ASSUME_TAC thm) THEN (UNDISCH_TAC (concl thm)))))
              THEN (REWRITE_TAC [align_conversion_thm])
              THEN (blastLib.BBLAST_TAC))
              (asl,g)
        else ALL_TAC(asl,g)
      )
      (* now we manage the memory condition using the assumption of the assertion *)
      THEN (UNABBREV_ALL_TAC)
      THEN (RW_TAC (srw_ss()) [combinTheory.UPDATE_def])
      THEN (FULL_SIMP_TAC (srw_ss()) [])
);

      THEN (ONE_EXEC_MAIN certs p pc_value 1)
      THEN (ONE_EXEC_MAIN certs p pc_value 2)
      THEN (ONE_EXEC_MAIN certs p pc_value 3)
      THEN (ONE_EXEC_MAIN certs p pc_value 4)
      THEN (ONE_EXEC_MAIN certs p pc_value 5)
      
      THEN (ONE_EXEC_MAIN certs p pc_value 6)
      THEN (ONE_EXEC_MAIN certs p pc_value 7)


val lbl_non_empty_thm = prove(``!pc.Address (Reg64 pc) ≠ Label ""``, FULL_SIMP_TAC (srw_ss()) []);
val inv_empty_var = UNDISCH(prove(``(sim_invariant s env pco) ==> (env "" = (NoType,Unknown))``,
        FULL_SIMP_TAC (bool_ss) [sim_invariant_def]));


fun assert () = 
let
val program_ass = List.nth((fst o strip_imp) goal, 3);
val (_, [_, ("statements", sts)]) = (TypeBase.dest_record o snd o pairSyntax.dest_pair o optionSyntax.dest_some o snd o dest_eq o snd o dest_exists) program_ass;
val (sts1, _) = listSyntax.dest_list sts;
val statement = List.nth(sts1, 0);
val (operator, [exp]) = strip_comb statement;
val th_just = (List.nth (certs, 0));
val th_just1 = SPEC ``env:environment`` th_just;
val th_just2 = if is_forall (concl th_just1)
    		   then SPEC ``s:arm8_state`` th_just1
		       else th_just1;
val hy_just = (hd o hyp o UNDISCH) th_just2;
val th_hy_just = UNDISCH(prove(``(sim_invariant s env pco) ==> ^hy_just``,
        FULL_SIMP_TAC (bool_ss) [sim_invariant_def]));
val th_just4 = MP th_just2 th_hy_just;
val value = (hd o snd o strip_comb o hd o snd o strip_comb o snd o dest_eq o snd o strip_imp o concl) th_just2;
val label = ``Address (Reg64 ^pc_value)``;
val th1 = SPECL [pc_value, ``env:environment``, ``e1:num``, exp, value, label, ``8:num``, sts, ``0:num``] assert_step_thm;
val lbl_not_empty_thm = SPEC pc_value lbl_non_empty_thm;
val non_zero_steps = prove(``8:num > 0``, FULL_SIMP_TAC (arith_ss) []);
val hd_thm = EVAL ``EL 0 ^sts``
(* prove (``(EL 0 ^sts = Assert ^exp)``, (FULL_SIMP_TAC (srw_ss()) [])); *)
val length_thm = prove (``(LENGTH ^sts > 0+1)``, (FULL_SIMP_TAC (srw_ss()) []));
val empty_var = inv_empty_var;
val th2 = MP (MP (MP (MP (MP (MP th1 lbl_not_empty_thm) non_zero_steps) hd_thm) length_thm) empty_var) th_just4;
in
th2
end;


val n = 1;
fun assert_rule n = 
let
val n_num = (numSyntax.mk_numeral(Arbnum.fromInt(n)))
val program_ass = List.nth((fst o strip_imp) goal, 3);
val (_, [_, ("statements", sts)]) = (TypeBase.dest_record o snd o pairSyntax.dest_pair o optionSyntax.dest_some o snd o dest_eq o snd o dest_exists) program_ass;
val (sts1, _) = listSyntax.dest_list sts;
val statement = List.nth(sts1, n);
val (operator, [exp]) = strip_comb statement;
val th_just = (List.nth (certs, n));
val th_just1 = SPEC ``env:environment`` th_just;
val th_just2 = if is_forall (concl th_just1)
    		   then SPEC ``s:arm8_state`` th_just1
		       else th_just1;
val hy_just = (hd o hyp o UNDISCH) th_just2;
val th_hy_just = UNDISCH(prove(``(sim_invariant s env pco) ==> ^hy_just``,
        FULL_SIMP_TAC (bool_ss) [sim_invariant_def]));
val th_just4 = MP th_just2 th_hy_just;
val value = (hd o snd o strip_comb o hd o snd o strip_comb o snd o dest_eq o snd o strip_imp o concl) th_just2;
val label = ``Address (Reg64 ^pc_value)``;
val th1 = SPECL [pc_value, ``env:environment``, ``e1+^n_num``, exp, value, label, ``8-^n_num``, sts, n_num] assert_step_thm;
val lbl_not_empty_thm = SPEC pc_value lbl_non_empty_thm;
val non_zero_steps = prove(``8-^n_num > 0``, FULL_SIMP_TAC (arith_ss) []);
val hd_thm = EVAL ``EL ^n_num ^sts``
val length_thm = prove (``(LENGTH ^sts > ^n_num+1)``, (FULL_SIMP_TAC (srw_ss()) []));
val empty_var = inv_empty_var;
val th2 = MP (MP (MP (MP (MP (MP th1 lbl_not_empty_thm) non_zero_steps) hd_thm) length_thm) empty_var) th_just4;
in
(SIMP_RULE (arith_ss) [] (UNDISCH th2))
end;

val th1 = assert_rule 0;
val th1_ok = CONJUNCT1 th1;
val th1_fail = UNDISCH (CONJUNCT2 th1);
val th1_ok_1 = UNDISCH th1_ok;

val th2 = assert_rule 1;
val th2_ok = CONJUNCT1 th2;
val th2_fail = UNDISCH (CONJUNCT2 th2);
val th2_ok_1 = UNDISCH th2_ok;

val thok = TRANS th1_ok_1 th2_ok_1;

val thfail = REWRITE_RULE [SYM th1_ok_1] th2_fail;





val [th] = arm8thl;


val i = 4;
val prog = p;
val curr_goal = ``
(bil_exec_step_n
   <|pco := SOME <|label := Address (Reg64 376w); index := 3|>;
     pi := prog;
     environ :=
       (λc.
          if "arm8_state_PC" = c then
            (Reg Bit64,Int (Reg64 (s.REG 30w)))
          else if "tmp_R30" = c then (Reg Bit64,Int (Reg64 (s.REG 30w)))
          else if "tmp_arm8_state_PC" = c then
            (Reg Bit64,Int (Reg64 376w))
          else env c); termcode := Unknown; debug := d1;
     execs := e1 + 1 + 1 + 1|> 1 =
 bs1) ⇒
((bs1.environ "" = (NoType,Unknown)) ∧
 (bs1.environ "R0" = (Reg Bit64,Int (Reg64 (s1.REG 0w)))) ∧
 (bs1.environ "R1" = (Reg Bit64,Int (Reg64 (s1.REG 1w)))) ∧
 (bs1.environ "R2" = (Reg Bit64,Int (Reg64 (s1.REG 2w)))) ∧
 (bs1.environ "R3" = (Reg Bit64,Int (Reg64 (s1.REG 3w)))) ∧
 (bs1.environ "R30" = (Reg Bit64,Int (Reg64 (s1.REG 30w)))) ∧
 (bs1.environ "ProcState_C" = (Reg Bit1,Int (bool2b s1.PSTATE.C))) ∧
 (bs1.environ "ProcState_N" = (Reg Bit1,Int (bool2b s1.PSTATE.N))) ∧
 (bs1.environ "ProcState_V" = (Reg Bit1,Int (bool2b s1.PSTATE.V))) ∧
 (bs1.environ "ProcState_Z" = (Reg Bit1,Int (bool2b s1.PSTATE.Z))) ∧
 (bs1.environ "arm8_state_PC" = (Reg Bit64,Int (Reg64 s1.PC))) ∧
 (bs1.environ "arm8_state_SP_EL0" = (Reg Bit64,Int (Reg64 s1.SP_EL0))) ∧
 (∃v. bs1.environ "tmp_R0" = (Reg Bit64,Int (Reg64 v))) ∧
 (∃v. bs1.environ "tmp_R1" = (Reg Bit64,Int (Reg64 v))) ∧
 (∃v. bs1.environ "tmp_R2" = (Reg Bit64,Int (Reg64 v))) ∧
 (∃v. bs1.environ "tmp_R3" = (Reg Bit64,Int (Reg64 v))) ∧
 (∃v. bs1.environ "tmp_R30" = (Reg Bit64,Int (Reg64 v))) ∧
 (∃v. bs1.environ "tmp_ProcState_C" = (Reg Bit1,Int (Reg1 v))) ∧
 (∃v. bs1.environ "tmp_ProcState_N" = (Reg Bit1,Int (Reg1 v))) ∧
 (∃v. bs1.environ "tmp_ProcState_V" = (Reg Bit1,Int (Reg1 v))) ∧
 (∃v. bs1.environ "tmp_ProcState_Z" = (Reg Bit1,Int (Reg1 v))) ∧
 (∃v. bs1.environ "tmp_arm8_state_PC" = (Reg Bit64,Int (Reg64 v))) ∧
 (∃v. bs1.environ "tmp_arm8_state_SP_EL0" = (Reg Bit64,Int (Reg64 v))) ∧
 (∃m.
    (bs1.environ "arm8_state_MEM" = (MemByte Bit64,Mem Bit64 m)) ∧
    ∀a. m (Reg64 a) = Reg8 (s1.MEM a)) ∧ ¬s1.SCTLR_EL1.E0E ∧
 (s1.PSTATE.EL = 0w) ∧ (s1.exception = NoException) ∧
 ¬s1.SCTLR_EL1.SA0 ∧ ¬s1.TCR_EL1.TBI0 ∧ ¬s1.TCR_EL1.TBI1 ∧
 (bs1.pco = SOME <|label := Address (Reg64 s1.PC); index := 0|>)) ∧
(∀a. a <₊ 0x100000w ⇒ (s.MEM a = s1.MEM a)) ∨ (bs1.pco = NONE)
``;









******************************
Lifting instruction: 54fffe8c
-------FAILURE-------


******************************
Lifting instruction: 79400000
-------FAILURE-------

******************************
Lifting instruction: 79000001
failed.
-------FAILURE-------

******************************
Lifting instruction: d65f03c0
-------FAILURE-------
