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



(* COMPARISON: old execution *)
tc_one_instruction `MOV X0, #1`;
tc_one_instruction2 `MOV X0, #1` ``0w:word64``;

tc_one_instruction `ADD X0, X0, X0`;
tc_one_instruction2 `ADD X0, X0, X0`;

tc_one_instruction `ADD X0, X1, #42 `;
tc_one_instruction2 `ADD X0, X1, #42 `;

tc_one_instruction `BLR X0`;
tc_one_instruction2 `BLR X0 `;

tc_one_instruction `CSINC X0, X1, X0, NE`;
tc_one_instruction2 `CSINC X0, X1, X0, NE`;

tc_one_instruction `LDRSB X0, [X1]`;
tc_one_instruction2 `LDRSB X0, [X1]`;

tc_one_instruction `LDR X0, [X1]`;
tc_one_instruction2 `LDR X0, [X1]`;

tc_one_instruction `STR X1, [X0]`;
tc_one_instruction2 `STR X1, [X0]`;

tc_one_instruction `ADDS X0, X1, X0`;
tc_one_instruction2 `ADDS X0, X1, X0`;








(*   2c:   7900001f        strh    wzr, [x0] *)
val inst = `MOV X1, #1`;
val instr = "d10103ff";
val code = arm8AssemblerLib.arm8_code `MOV X1, #1`;
val instr = (hd code);
val pc_value = ``0w:word64``;
(* 2.11 seconds *)
val (p, certs, [step]) = tc_stmt_arm8_hex instr;
val (sts, sts_ty) = listSyntax.dest_list p;
val sts = List.concat [sts, [``Jmp (Const (Reg64 (^pc_value+4w)))``]];
val p = listSyntax.mk_list(sts,sts_ty);
val goal = tc_gen_goal p certs step pc_value;

prove(``^goal``,
 (* first processing 0.6s *)
      (DISCH_TAC) 
	  THEN (DISCH_TAC) THEN (DISCH_TAC) THEN (DISCH_TAC)
	  THEN (FULL_SIMP_TAC (srw_ss()) [])
    
THEN (ONE_EXEC_MAIN certs p pc_value 1)
THEN (ONE_EXEC_MAIN certs p pc_value 2)
THEN (ONE_EXEC_MAIN certs p pc_value 3)
THEN (ONE_EXEC_MAIN certs p pc_value 4)
THEN (ONE_EXEC_MAIN certs p pc_value 5)


(* THEN (ONE_EXEC2 certs 5) *)

(* Computation completed *)
THEN (FULL_SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
THEN DISCH_TAC

(* use the step theorem *)
THEN (ASSUME_TAC (UNDISCH_ALL (SIMP_RULE myss [ASSUME ``s.PC=0w``] (DISCH_ALL step))))
THEN (FULL_SIMP_TAC (srw_ss()) [])

THEN (RW_TAC (srw_ss()) [combinTheory.UPDATE_def, bool2b_def])
);


val i = 5;
val prog = p;
val curr_goal = ``
(bil_exec_step_n
   <|pco := SOME <|label := Address (Reg64 0w); index := 4|>;
     pi := prog;
     environ :=
       (λc.
          if "arm8_state_PC" = c then (Reg Bit64,Int (Reg64 4w))
          else if "R1" = c then (Reg Bit64,Int (Reg64 1w))
          else if "tmp_R1" = c then (Reg Bit64,Int (Reg64 (s.REG 1w)))
          else if "tmp_arm8_state_PC" = c then
            (Reg Bit64,Int (Reg64 0w))
          else env c); termcode := Unknown; debug := d1;
     execs := e1 + 1 + 1 + 1 + 1|> 1 =
 bs1) ⇒
(bs1.environ "" = (NoType,Unknown)) ∧
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
∃m.
  (bs1.environ "arm8_state_MEM" = (MemByte Bit64,Mem Bit64 m)) ∧
  ∀a. m (Reg64 a) = Reg8 (s1.MEM a)
``;




(* 0000000000000000 <internal_mul>: *)
(*    0:   d10103ff        sub     sp, sp, #0x40 *)
tc_one_instruction2_by_bin "d10103ff" ``0w:word64``;
(*    4:   f9000fe0        str     x0, [sp,#24] *)
tc_one_instruction2_by_bin "f9000fe0" ``4w:word64``;;
(*    8:   f9000be1        str     x1, [sp,#16] *)
tc_one_instruction2_by_bin "f9000be1" ``8w:word64``;
(*    c:   f90007e2        str     x2, [sp,#8] *)
tc_one_instruction2_by_bin "f90007e2";
(*   10:   b90007e3        str     w3, [sp,#4] *)
tc_one_instruction2_by_bin "b90007e3";
(*   14:   b9003bff        str     wzr, [sp,#56] *)
tc_one_instruction2_by_bin "b9003bff";
(*   18:   14000009        b       3c <internal_mul+0x3c> *)
tc_one_instruction2_by_bin "14000009" ``8w:word64``;;
(*   1c:   b9803be0        ldrsw   x0, [sp,#56] *)
tc_one_instruction2_by_bin "b9803be0";
(*   20:   d37ff800        lsl     x0, x0, #1 *)
tc_one_instruction2_by_bin "d37ff800";
(*   24:   f94007e1        ldr     x1, [sp,#8] *)
tc_one_instruction2_by_bin "f94007e1"  ``8w:word64``;
(*   28:   8b000020        add     x0, x1, x0 *)
tc_one_instruction2_by_bin "8b000020";
(*   2c:   7900001f        strh    wzr, [x0] *)
tc_one_instruction2_by_bin "7900001f";
(*   30:   b9403be0        ldr     w0, [sp,#56] *)
tc_one_instruction2_by_bin "b9403be0";
(*   34:   11000400        add     w0, w0, #0x1 *)
tc_one_instruction2_by_bin "11000400";
(*   38:   b9003be0        str     w0, [sp,#56] *)
tc_one_instruction2_by_bin "b9003be0";
(*   3c:   b94007e0        ldr     w0, [sp,#4] *)
tc_one_instruction2_by_bin "b94007e0";
(*   40:   531f7801        lsl     w1, w0, #1 *)
tc_one_instruction2_by_bin "531f7801";
(*   44:   b9403be0        ldr     w0, [sp,#56] *)
tc_one_instruction2_by_bin "b9403be0";
(*   48:   6b00003f        cmp     w1, w0 *)
tc_one_instruction2_by_bin "6b00003f";
(* OK, even if in CMP we are currently cheating *)

(* 4c:   54fffe8c        b.gt    1c <internal_mul+0x1c> *)
tc_one_instruction2_by_bin "54fffe8c"  ``8w:word64``;
(* 50:   b94007e0        ldr     w0, [sp,#4] *)
tc_one_instruction2_by_bin "b94007e0";
(* 54:   51000400        sub     w0, w0, #0x1 *)
tc_one_instruction2_by_bin "51000400";
(* 58:   b9003fe0        str     w0, [sp,#60] *)
tc_one_instruction2_by_bin "b9003fe0";
(* 5c:   14000043        b       168 <internal_mul+0x168> *)
tc_one_instruction2_by_bin "14000043";
(* 60:   b9803fe0        ldrsw   x0, [sp,#60] *)
tc_one_instruction2_by_bin "b9803fe0";
(* 64:   d37ff800        lsl     x0, x0, #1 *)
tc_one_instruction2_by_bin "d37ff800";
(* 68:   f9400fe1        ldr     x1, [sp,#24] *)
tc_one_instruction2_by_bin "f9400fe1";
(* 6c:   8b000020        add     x0, x1, x0 *)
tc_one_instruction2_by_bin "8b000020";
(* 70:   79400000        ldrh    w0, [x0] *)
tc_one_instruction2_by_bin "79400000";
(* 74:   53003c00        uxth    w0, w0 *)
tc_one_instruction2_by_bin "53003c00";
(* 78:   f90017e0        str     x0, [sp,#40] *)
tc_one_instruction2_by_bin "f90017e0";
(* 7c:   f9001bff        str     xzr, [sp,#48] *)
tc_one_instruction2_by_bin "f9001bff";
(* 80:   b94007e0        ldr     w0, [sp,#4] *)
tc_one_instruction2_by_bin "b94007e0";
(* 84:   51000400        sub     w0, w0, #0x1 *)
tc_one_instruction2_by_bin "51000400";
(* 88:   b9003be0        str     w0, [sp,#56] *)
tc_one_instruction2_by_bin "b9003be0";
(* 8c:   1400002a        b       134 <internal_mul+0x134> *)
tc_one_instruction2_by_bin "1400002a";
(* 90:   b9803be0        ldrsw   x0, [sp,#56] *)
tc_one_instruction2_by_bin "b9803be0";
(* 94:   d37ff800        lsl     x0, x0, #1 *)
tc_one_instruction2_by_bin "d37ff800";
(* 98:   f9400be1        ldr     x1, [sp,#16] *)
tc_one_instruction2_by_bin "f9400be1";
(* 9c:   8b000020        add     x0, x1, x0 *)
tc_one_instruction2_by_bin "8b000020";
(* a0:   79400000        ldrh    w0, [x0] *)
tc_one_instruction2_by_bin "79400000";
(* a4:   53003c01        uxth    w1, w0 *)
tc_one_instruction2_by_bin "53003c01";
(* a8:   f94017e0        ldr     x0, [sp,#40] *)
tc_one_instruction2_by_bin "f94017e0";
(* ac:   9b007c20        mul     x0, x1, x0 *)
tc_one_instruction2_by_bin "9b007c20";
(* b0:   f9401be1        ldr     x1, [sp,#48] *)
tc_one_instruction2_by_bin "f9401be1";
(* b4:   8b000020        add     x0, x1, x0 *)
tc_one_instruction2_by_bin "8b000020";
(* b8:   f9001be0        str     x0, [sp,#48] *)
tc_one_instruction2_by_bin "f9001be0";
(* bc:   b9403fe1        ldr     w1, [sp,#60] *)
tc_one_instruction2_by_bin "b9403fe1";
(* c0:   b9403be0        ldr     w0, [sp,#56] *)
tc_one_instruction2_by_bin "b9403be0";
(* c4:   0b000020        add     w0, w1, w0 *)
tc_one_instruction2_by_bin "0b000020";
(* c8:   93407c00        sxtw    x0, w0 *)
tc_one_instruction2_by_bin "93407c00";
(* cc:   91000400        add     x0, x0, #0x1 *)
tc_one_instruction2_by_bin "91000400";
(* d0:   d37ff800        lsl     x0, x0, #1 *)
tc_one_instruction2_by_bin "d37ff800";
(* d4:   f94007e1        ldr     x1, [sp,#8] *)
tc_one_instruction2_by_bin "f94007e1";
(* d8:   8b000020        add     x0, x1, x0 *)
tc_one_instruction2_by_bin "8b000020";
(* dc:   79400000        ldrh    w0, [x0] *)
tc_one_instruction2_by_bin "79400000";
(* e0:   53003c00        uxth    w0, w0 *)
tc_one_instruction2_by_bin "53003c00";
(* e4:   f9401be1        ldr     x1, [sp,#48] *)
tc_one_instruction2_by_bin "f9401be1";
(* e8:   8b000020        add     x0, x1, x0 *)
tc_one_instruction2_by_bin "8b000020";
(* ec:   f9001be0        str     x0, [sp,#48] *)
tc_one_instruction2_by_bin "f9001be0";
(* f0:   b9403fe1        ldr     w1, [sp,#60] *)
tc_one_instruction2_by_bin "b9403fe1";
(* f4:   b9403be0        ldr     w0, [sp,#56] *)
tc_one_instruction2_by_bin "b9403be0";
(* f8:   0b000020        add     w0, w1, w0 *)
tc_one_instruction2_by_bin "0b000020";
(* fc:   93407c00        sxtw    x0, w0 *)
tc_one_instruction2_by_bin "93407c00";
(* 100:   91000400        add     x0, x0, #0x1 *)
tc_one_instruction2_by_bin "91000400";
(* 104:   d37ff800        lsl     x0, x0, #1 *)
tc_one_instruction2_by_bin "d37ff800";
(* 108:   f94007e1        ldr     x1, [sp,#8] *)
tc_one_instruction2_by_bin "f94007e1";
(* 10c:   8b000020        add     x0, x1, x0 *)
tc_one_instruction2_by_bin "8b000020";
(* 110:   f9401be1        ldr     x1, [sp,#48] *)
tc_one_instruction2_by_bin "f9401be1";
(* 114:   53003c21        uxth    w1, w1 *)
tc_one_instruction2_by_bin "53003c21";
(* 118:   79000001        strh    w1, [x0] *)
tc_one_instruction2_by_bin "79000001";
(* 11c:   f9401be0        ldr     x0, [sp,#48] *)
tc_one_instruction2_by_bin "f9401be0";
(* 120:   d350fc00        lsr     x0, x0, #16 *)
tc_one_instruction2_by_bin "d350fc00";
(* 124:   f9001be0        str     x0, [sp,#48] *)
tc_one_instruction2_by_bin "f9001be0";
(* 128:   b9403be0        ldr     w0, [sp,#56] *)
tc_one_instruction2_by_bin "b9403be0";
(* 12c:   51000400        sub     w0, w0, #0x1 *)
tc_one_instruction2_by_bin "51000400";
(* 130:   b9003be0        str     w0, [sp,#56] *)
tc_one_instruction2_by_bin "b9003be0";
(* 134:   b9403be0        ldr     w0, [sp,#56] *)
tc_one_instruction2_by_bin "b9403be0";
(* 138:   6b1f001f        cmp     w0, wzr *)
tc_one_instruction2_by_bin "6b1f001f";
(* 13c:   54fffaaa        b.ge    90 <internal_mul+0x90> *)
tc_one_instruction2_by_bin "54fffaaa";
(* 140:   b9803fe0        ldrsw   x0, [sp,#60] *)
tc_one_instruction2_by_bin "b9803fe0";
(* 144:   d37ff800        lsl     x0, x0, #1 *)
tc_one_instruction2_by_bin "d37ff800";
(* 148:   f94007e1        ldr     x1, [sp,#8] *)
tc_one_instruction2_by_bin "f94007e1";
(* 14c:   8b000020        add     x0, x1, x0 *)
tc_one_instruction2_by_bin "8b000020";
(* 150:   f9401be1        ldr     x1, [sp,#48] *)
tc_one_instruction2_by_bin "f9401be1";
(* 154:   53003c21        uxth    w1, w1 *)
tc_one_instruction2_by_bin "53003c21";
(* 158:   79000001        strh    w1, [x0] *)
tc_one_instruction2_by_bin "79000001";
(* 15c:   b9403fe0        ldr     w0, [sp,#60] *)
tc_one_instruction2_by_bin "b9403fe0";
(* 160:   51000400        sub     w0, w0, #0x1 *)
tc_one_instruction2_by_bin "51000400";
(* 164:   b9003fe0        str     w0, [sp,#60] *)
tc_one_instruction2_by_bin "b9003fe0";
(* 168:   b9403fe0        ldr     w0, [sp,#60] *)
tc_one_instruction2_by_bin "b9403fe0";
(* 16c:   6b1f001f        cmp     w0, wzr *)
tc_one_instruction2_by_bin "6b1f001f";
(* 170:   54fff78a        b.ge    60 <internal_mul+0x60> *)
tc_one_instruction2_by_bin "54fff78a";
(* 174:   910103ff        add     sp, sp, #0x40 *)
tc_one_instruction2_by_bin "910103ff";
(* 178:   d65f03c0        ret *)
tc_one_instruction2_by_bin "d65f03c0";





(*   20:   d37ff800        lsl     x0, x0, #1 *)
val [t] = arm8_step_hex "d37ff800";
val instr = "d37ff800";


val ass_some = (List.filter (fn tm =>
    (is_eq tm) andalso ((optionLib.is_some o snd o dest_eq) tm) andalso ((optionLib.is_some o snd o dest_eq) tm)
) (hyp t));
val ass_some = List.map (SIMP_CONV (srw_ss()) []) ass_some;
val t1 = List.foldl (fn (thm, main_thm) => (DISCH ((fst o dest_eq o concl) thm) main_thm)) t ass_some;
val t2 = REWRITE_RULE ass_some t1;
val [t3] = IMP_CANON t2;
val t4 = UNDISCH_ALL t3;
val t5 = SIMP_RULE (bool_ss) [] t4;

val ass_const = (List.filter (fn tm =>
    (is_eq tm) andalso ((wordsSyntax.is_n2w o fst o dest_eq) tm)
) (hyp t5));
val ass_const = List.map (SYM o ASSUME) ass_const;
val t6 = REWRITE_RULE ass_const t5;

val upds = ((extract_arm8_changes o optionSyntax.dest_some o snd o dest_comb o concl) t6);
val exp = snd(List.nth(upds, 1));
tc_exp_arm8 exp;

