(* You should open emacs from ../arm8bil *)

HOL_Interactive.toggle_quietdec();
open HolKernel boolLib bossLib Parse;
open lcsymtacs utilsLib;
open wordsLib blastLib;
open state_transformerTheory updateTheory arm8Theory;
open stateTheory;
open lcsymtacs arm8_stepTheory;
open state_transformerSyntax;
open arm8_stepLib;
open proofTools arithTheory carryTheory;
open bilTheory arm8bilTheory;
open arm8bilLib;
HOL_Interactive.toggle_quietdec();

(* overflows *)
tc_exp_arm8 ``T``;
tc_exp_arm8 ``aaa.REG 1w``;
tc_exp_arm8 ``(aaa.REG 1w) + (aaa.REG 2w)``;
tc_exp_arm8 ``(aaa.REG 1w) * (aaa.REG 1w)``;
tc_exp_arm8 ``(aaa.REG 2w) + 3w``;
tc_exp_arm8 ``(aaa.REG 2w) >=+ 3w``;
tc_exp_arm8 ``T /\ F``;
tc_exp_arm8 ``T /\ (aaa.PSTATE.Z)``;
tc_exp_arm8 ``~(aaa.PSTATE.Z)``;
tc_exp_arm8 ``if T then F else T``;
tc_exp_arm8 ``if T then (aaa.REG 2w) + 3w else 2w``;

val [t1] = arm8_step_hex "0x910003e1";  (* mov     x1, sp *)
tc_exp_arm8 ``s.PC + 4w``;
tc_exp_arm8 ``s.SP_EL0 + 0w``;

(* From the manual  *)
(* https://www.element14.com/community/servlet/JiveServlet/previewBody/41836-102-1-229511/ARM.Reference_Manual.pdf *)

(* add 32-bit register  *)
arm8_step_code `ADD W0, W1, W2`;
tc_exp_arm8 ``(w2w
              ((w2w (s.REG (1w :word5)) :word32) +
               (w2w (s.REG (2w :word5)) :word32)) :word64)``;
(* FAILURE *)
(*
I do not see a failure here, but this output:

tc_exp_arm8 ``(w2w
              ((w2w (s.REG (1w :word5)) :word32) +
#                (w2w (s.REG (2w :word5)) :word32)) :word64)``;
<<HOL message: more than one resolution of overloading was possible>>
<<HOL message: more than one resolution of overloading was possible>>
<<HOL message: more than one resolution of overloading was possible>>
val it =
   (``Cast
    (Plus (LowCast (Den (r2s 1w)) Bit32) (LowCast (Den (r2s 2w)) Bit32))
    Bit64``,
    ``w2w (w2w (s.REG 1w) + w2w (s.REG 2w))``,
     []
|- ∀env s.
     (env (r2s 2w) = (Reg Bit64,Int (Reg64 (s.REG 2w)))) ⇒
     (env (r2s 1w) = (Reg Bit64,Int (Reg64 (s.REG 1w)))) ⇒
     (bil_eval_exp
        (Cast
           (Plus (LowCast (Den (r2s 1w)) Bit32)
              (LowCast (Den (r2s 2w)) Bit32)) Bit64) env =
      Int (Reg64 (w2w (w2w (s.REG 1w) + w2w (s.REG 2w)))))):
   term * term * thm

*)

(* 64-bit addition *)
arm8_step_code `ADD X0, X1, X2`;
tc_exp_arm8 `` s.REG 1w + s.REG 2w``;

(* add 64-bit extending register  *)
arm8_step_code `ADD X0, X1, W2, SXTW `;
tc_exp_arm8 ``s.REG 1w + ExtendValue (s.REG 2w,ExtendType_SXTW,0)``;
(* FAILURE *)

(* add 64-bit immediate  *)
arm8_step_code `ADD X0, X1, #42 `;
tc_exp_arm8 ``s.REG 1w + 42w``;

(* Absolute branch to address in Xn *)
arm8_step_code `BR X0`;
arm8_step_code `BLR X0`;

tc_exp_arm8 ``s.PC + 4w``;

arm8_step_code `B #4`;

(* Arithmetics instructions *)
arm8_step_code `ADD W0, W1, W2, LSL #3`;
(* still problems with 32 bits *)

(* Guancio: my first extension *)
arm8_step_code `SUB X0, X4, X3, ASR #2`;
tc_exp_arm8 ``s.REG 4w − s.REG 3w ≫ 2``;

val ae = ``s.REG 3w ≫ 2``;
tc_exp_arm8 ae;

val t = prove(``2 = w2n (2w:word64)``, (FULL_SIMP_TAC (srw_ss()) []));
val ae1 = (snd o dest_eq o concl) (REWRITE_CONV [Once t] ae);
val ae2 = (snd o dest_eq o concl) (REWRITE_CONV [(GSYM wordsTheory.word_asr_bv_def)] ae1);
(* val ae2 = (snd o dest_eq o concl) (REWRITE_CONV [Once t, (GSYM wordsTheory.word_asr_bv_def)] ae1); *)
tc_exp_arm8 ae2;

(* FLAGS *)

val [[t]] = arm8_step_code `ADDS X1, X2, X3 `;
val s1 = (snd o dest_comb o snd o dest_eq o concl) t;
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.V``;
tc_exp_arm8 exp;
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.C``;
tc_exp_arm8 exp;
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.Z``;
tc_exp_arm8 exp;
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.N``;
tc_exp_arm8 exp;

val [[t]] = arm8_step_code `CMP X3, X4 `;
val s1 = (snd o dest_comb o snd o dest_eq o concl) t;
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.V``;
tc_exp_arm8 exp;
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.C``;
val (a,b,c) = tc_exp_arm8 exp;
SIMP_RULE (srw_ss()) [r2s_def] c;


val [[t]] = arm8_step_code `CMP W3, W4 `;
val s1 = (snd o dest_comb o snd o dest_eq o concl) t;
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.C``;
val (a,b,c) = tc_exp_arm8 exp;
SIMP_RULE (srw_ss()) [r2s_def] c;




(if e<n then e else e mod n) = e mod n
==>
e<n ---- w2n x + w2n y + 1 < 2**64
==>
(x // 2w + y // 2w + (word_mod x 2w ‖ word_mod y 2w) <₊ 0x8000000000000000w)
--
(s.REg 3w // 2w + s.REg 4w // 2w + (word_mod s.REg 3w 2w ‖ word_mod s.REg 4w 2w) <₊ 0x8000000000000000w)

e1 <₊ e2

tc_exp_arm8 ``s.REG 3w``;
tc_exp_arm8 ``2w:word64``;

!e1b e2b e1w e2w. (eval eb1 env = int(e1w)) ==> (eval eb2 env = int(e2w)) ==>
 (bil_eval_exp (Div (eb1) (eb2) env = Int (e1w // e2w)


tc_exp_arm8 ``s.REG 3w // 2w:word64``;
tc_exp_arm8 ``s.REG 4w // 2w:word64``;

tc_exp_arm8 ``(s.REG 3w // 2w:word64) + (s.REG 4w // 2w:word64)``;

tc_exp_arm8 ``s.REG 3w``;
tc_exp_arm8 ``word_mod (s.REG 3w) 2w:word64``;
tc_exp_arm8 ``word_mod (s.REG 4w) 2w:word64``;

tc_exp_arm8 ``(word_mod (s.REG 3w) 2w:word64) || (word_mod (s.REG 4w) 2w:word64)``;

tc_exp_arm8 ``(s.REG 3w // 2w:word64) + (s.REG 4w // 2w:word64) + ((word_mod (s.REG 3w) 2w:word64) || (word_mod (s.REG 4w) 2w:word64))``;

tc_exp_arm8 ``word_mod (s.REG 1w) 2w <₊ 0x8000000000000000w``;

val new_exp_thm = (SIMP_CONV (myss) [
      			(* These are for the C flag in addittion *)
      			carry_thm, plus_lt_2exp64_tm, minus_lt_2exp64_tm,
      			(* These are for the V flag in addittion *)
      			BIT63_thm, Bword_add_64_thm] exp);
val ae1 = (snd o dest_eq o concl) new_exp_thm;
tc_exp_arm8 ae1;




val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.Z``;
tc_exp_arm8 exp;
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.N``;
tc_exp_arm8 exp;
(* TODO *)





(* BINARY OPERATIONS *)

arm8_step_code `BIC X0, X0, X1 `;
tc_exp_arm8 ``s.REG 0w && ¬s.REG 1w``;

arm8_step_code `SUB X0, X4, X3`;
tc_exp_arm8 ``s.REG 4w − s.REG 3w``;

arm8_step_code `SUBS X0, X4, X3`;

tc_exp_arm8 ``
((word_msb (s.REG 4w) ⇔ word_msb (¬s.REG 3w)) ∧
               (word_msb (s.REG 4w) ⇎
                BIT 63 (w2n (s.REG 4w) + w2n (¬s.REG 3w) + 1)))``;
(* WHY WE HAVE W2N IN THE HYPOTESYS? *)


arm8_step_code `CSINC X0, X1, X0, NE`;
tc_exp_arm8 ``
if ¬s.PSTATE.Z then s.REG 1w else s.REG 0w + 1w
``;


(* UNSUPPORTED *)
arm8_step_code `LDRB X0, [X1]`;

arm8_step_code `LDRSB X0, [X1]`;

tc_exp_arm8 ``sw2sw (s.MEM (s.REG 1w + 0w)):word64``;
tc_exp_arm8 ``(w2w (0w:word8)):word64``;
tc_exp_arm8 ``(w2n (0w:word8))``;
tc_exp_arm8 ``(sw2sw (0w:word8)):word64``;
tc_exp_arm8 ``s.MEM (0w:word64)``;
tc_exp_arm8 ``s.MEM (s.REG 1w + 0w)``;

(* memory should use an existential quantifier *)
tc_exp_arm8 ``s.MEM (0w:word64) + 2w``;


(* NO THEOREM WORKS IN 8bit? *)

tc_exp_arm8 ``s.MEM (0w:word64) + (if (s.REG 1w) = 1w then 0w else 1w)``;

(* 118:   79000001        strh    w1, [x0] *)
val [t] = arm8_step_hex "79000001";
val upds = ((extract_arm8_changes o optionSyntax.dest_some o snd o dest_comb o concl) t);
val exp = snd(List.nth(upds, 2));


tc_exp_arm8 exp;

val ae = exp;
val prefix = "";
val (o1, o2, o3) = extract_operands ae;
val f0 = extract_fun ae;




val [[t]] = arm8_step_code `ADD W0, W1, W2`;
val s1 = ((optionSyntax.dest_some o snd o dest_eq o concl) t);
val exp = (snd o dest_eq o concl o EVAL) ``^s1.REG 0w``;
tc_exp_arm8 exp;

val [[t]] = arm8_step_code `ADDS W0, W1, W2`;
val s1 = ((optionSyntax.dest_some o snd o dest_eq o concl) t);
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.V``;
tc_exp_arm8 exp;

tc_exp_arm8 ``s.REG 1w``;
tc_exp_arm8 ``(w2w (s.REG 1w)):word32``;
tc_exp_arm8 ``word_msb ((w2w (s.REG 1w)):word32)``;
tc_exp_arm8 ((fst o dest_conj) exp);

val BIT31_thm = prove(`` ∀n. BIT 31 n ⇔ word_lsb (n2w n >>>~ 31w:word32)``,
    cheat);

val exp1 = (snd o dest_eq o concl o  (REWRITE_CONV [BIT31_thm])) exp;

tc_exp_arm8 ((fst o dest_conj) exp1);
val exp2 = ((snd o dest_conj) exp1);

tc_exp_arm8 ((fst o dest_eq o dest_neg) exp2);

val exp3 = ((snd o dest_eq o dest_neg) exp2);
val ae = exp3;
(wordsSyntax.is_word_lsb ae);
val (o1, o2, o3) = extract_operands ae;
val f0 = extract_fun ae;

(tc_exp_arm8 o1);


val mp = (GEN_ALL o DISCH_ALL) (MP_UN (select_bil_op_theorem ((fst o strip_comb) ae) (word_size o1)) (tce o1))




tc_exp_arm8 ``word_lsb (w2w(s.REG 1w):word32)``;

val exp4 = snd (dest_comb exp3);
val exp5 = (List.hd o snd o strip_comb) exp4;
tc_exp_arm8 exp5;

tc_exp_arm8``(n2w
     (w2n (w2w ((s :arm8_state).REG (1w :word5)) :word64) +
      w2n (w2w (s.REG (2w :word5)) :word64)) :word64)``;



val ae = exp4;
(wordsSyntax.is_w2n         ae);
val (o1, o2, o3) = extract_operands ae;
val f0 = extract_fun ae;


val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.C``;
tc_exp_arm8 exp;

(* OK *)
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.Z``;
tc_exp_arm8 exp;


(* OK *)
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.N``;
tc_exp_arm8 exp;




val [[t]] = arm8_step_code `ADDS X0, X1, X2`;
val s1 = ((optionSyntax.dest_some o snd o dest_eq o concl) t);
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.V``;
val exp1 = (snd o dest_eq o concl o  (REWRITE_CONV [BIT63_thm])) exp;
tc_exp_arm8 exp1;

tc_exp_arm8 exp;

tc_exp_arm8 ``s.REG 1w``;
tc_exp_arm8 ``(w2w (s.REG 1w)):word32``;
tc_exp_arm8 ``word_msb ((w2w (s.REG 1w)):word32)``;
tc_exp_arm8 ((fst o dest_conj) exp);



> > val it =
   ``(word_msb (s.REG 1w) ⇔ word_msb (s.REG 2w)) ∧
  (word_msb (s.REG 1w) ⇎
  
   word_lsb (n2w (w2n (s.REG 1w) + w2n (s.REG 2w)) >>>~ 63w))``:
   term

``(word_msb (w2w (s.REG 1w)) ⇔ word_msb (w2w (s.REG 2w))) ∧
  (word_msb (w2w (s.REG 1w)) ⇎


   word_lsb
     (n2w (w2n (w2w (s.REG 1w)) + w2n (w2w (s.REG 2w))) >>>~ 31w))``:


tc_exp_arm8 ``word_lsb (n2w (w2n (s.REG 1w) + w2n (s.REG 2w)) >>>~ 63w:word64)``;
tc_exp_arm8 ``word_lsb (n2w (w2n (w2w(s.REG 1w):word64) + w2n (s.REG 2w)) >>>~ 63w:word64)``;

val exp3 = ``word_lsb (n2w (w2n (w2w(s.REG 1w):word64) + w2n (w2w (s.REG 2w):word64)) >>>~ 63w:word64)``;
val ae = exp3;
(wordsSyntax.is_word_lsb ae);
val (o1, o2, o3) = extract_operands ae;
val f0 = extract_fun ae;

(tc_exp_arm8 o1);

      (let val _ = if (type_of ae) = ``:bool`` then true
		   else raise UnsupportedARM8ExpressionException ae
	   val new_exp_thm = (SIMP_CONV (myss) [
      			(* These are for the C flag in addittion *)
      			carry_thm, plus_lt_2exp64_tm,
      			(* These are for the C flag in subtractions *)
			minus_lt_2exp64_tm,
      			(* These are for the V flag in addittion *)
      			BIT63_thm, Bword_add_64_thm] ae)
      	   val ae0 = (fst o dest_eq o concl) new_exp_thm
      	   val ae1 = (snd o dest_eq o concl) new_exp_thm
	   val t1 = MP_UN eq_trans_on_env_tm (tce ae1)
	   val t1_gen_v3 = GEN ``v3:bool`` t1
	   val t1_on_ae0 = SPEC ae0 t1_gen_v3
	   val t2 = MP t1_on_ae0 (SYM new_exp_thm)
	   val mp = (GEN_ALL o DISCH_ALL) t2
	   val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0)
      	   in
	      (be, ae, mp)
       end)





tc_exp_arm8 ``word_lsb ((n2w (w2n (s.REG 1w) + w2n (s.REG 2w)):word64):word64)``;
tc_exp_arm8 ``word_lsb (n2w (w2n (w2w(s.REG 1w):word64) + w2n (s.REG 2w)) >>>~ 63w:word64)``;


val prefix = "";




(* ******************** *)
(* ERROR WITH 13047c00 *)
(* ******************** *)

val [t] = arm8_step_hex "13047c00";
val s1 = ((optionSyntax.dest_some o snd o dest_comb o concl) t);
val exp = (snd o dest_eq o concl o EVAL) ``^s1.REG 0w``;
val exp = (snd o dest_eq o concl o (SIMP_CONV (srw_ss()) [ASSUME ``imm=0xFFFFFFFFw:word32``, ASSUME ``x=0xFFFFFFFw:word32``])) exp;
tc_exp_arm8 exp;


val exp =    ``word_bit (31 :num) (w2w (s.REG (0w :word5)) :word32)``;
tc_exp_arm8 exp;

(* Same problem here *)
val [t] = arm8_step_hex "131f7c20";

val [t] = arm8_step_hex "1ac02020";
val s1 = ((optionSyntax.dest_some o snd o dest_comb o concl) t);
val exp = (snd o dest_eq o concl o EVAL) ``^s1.REG 0w``;
tc_exp_arm8 exp;


val [t] = arm8_step_hex "eb1f001f";
val s1 = ((optionSyntax.dest_some o snd o dest_comb o concl) t);
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.C``;
tc_exp_arm8 exp;

(* store of two registers *)
val [t] = arm8_step_hex "a9b97bfd";
val s1 = ((optionSyntax.dest_some o snd o dest_comb o concl) t);
val exp = (snd o dest_eq o concl o EVAL) ``^s1.MEM``;
tc_exp_arm8 exp;

(* Update of register 29 that i not part of the simulation *)
val [t] = arm8_step_hex "910003fd";
val s1 = ((optionSyntax.dest_some o snd o dest_comb o concl) t);
val exp = (snd o dest_eq o concl o EVAL) ``^s1.MEM``;
tc_exp_arm8 exp;

(* Usage of register 29 that i not part of the simulation *)
val [t] = arm8_step_hex "f9001fa0";
val s1 = ((optionSyntax.dest_some o snd o dest_comb o concl) t);
val exp = (snd o dest_eq o concl o EVAL) ``^s1.MEM``;
tc_exp_arm8 exp;


val [t] = arm8_step_hex "b90037a1";
b90037a1











(* ******************** *)
(* ERROR WITH eb1f001f *)
(* problem related to the Carry flag *)
(* ******************** *)
val [t] = arm8_step_hex "eb1f001f";
val s1 = ((optionSyntax.dest_some o snd o dest_comb o concl) t);
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.C``;
val abc1 = tc_exp_arm8 exp;


val [[t]] = arm8_step_code `CMP X0, X1`;
val [[t]] = arm8_step_code `CMP X0, XZR`;

(* val [[t]] = arm8_step_code `ADDS X1, X2, X3 ` *)

exp

(if (a < x) then a else a MOD x) <> a

(if (a < x) then a<>a else (a MOD x) <> a)

(if (a < x) then F else T)

a >= x

w2n (s.REG 0w) + 18446744073709551615 + 1 >= 18446744073709551616

w2n (s.REG 0w) + 18446744073709551616 >= 18446744073709551616



fun appl_simp ae = (SIMP_CONV (myss) [
      			(* These are for the C flag in addittion *)
      			carry_thm, plus_lt_2exp64_tm,
      			(* These are for the C flag in subtractions *)
			minus_lt_2exp64_tm,
      			(* These are for the V flag in addittion *)
      			BIT63_thm, Bword_add_64_thm] ae)
;

val exp1 = (snd o dest_eq o concl) (SIMP_CONV (bool_ss) [carry_thm, minus_lt_2exp64_tm] exp); (* , w2n_of_not_zero_thm *)
val exp1 = (snd o dest_eq o concl) (appl_simp exp);
appl_simp exp;
val exp1 = (snd o dest_eq o concl) (appl_simp exp1);

tc_exp_arm8 exp;


match_term ``(x:word64) + 1w`` ``(f+g) + (1w:word64)``;

val pat_expr = ``~(w2n x + y + 1 < 18446744073709551616)``

val mat1 = ``~(w2n (s.REG 0w) + 18446744073709551615 + 1 < 18446744073709551616)``;
val mat2 = ``~(w2n (123w:word64) < 1)``;

match_term pat_expr mat2;
(let val _ = match_term pat_expr mat1 in "ok" end) handle _ => ("nok");



	    let
	      val matchpat = ``(x:word64) + 1w`` ``(f+g) + (1w:word64)``
	      fun matchfun term = (let val _ = match_term matchpat term in (true) end) handle _ => (false)
	    in
	      if (matchfun ae) then
	        let 
	        (tce )
	      else
                let
                  val mp = (GEN_ALL o DISCH_ALL) (MP_UN (select_bil_op_theorem ((fst o strip_comb) ae) 1) (tce o1));
                  val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
                in
                  (be, ae, mp)
                end
	    end


REWRITE_RULE [SYM t1] t2

TRANS (EVAL ``1 + 1:num``) (SYM (EVAL ``0 + 2:num``))




conv [w2n_of_not_zero_thm] [plus_lt_2exp64_tm] ae

fun conv thl0 thl1 ae =
let
  val no_thl0 = (List.length thl0 = 0)
  val t0 = if no_thl0 then NONE else (SOME (SIMP_CONV (bool_ss) thl0 ae))
  val t1 = if no_thl0 then (SIMP_CONV (bool_ss) thl1 ae) else (TRANS (valOf t0) (SIMP_CONV (bool_ss) thl1 ((snd o dest_eq o concl o valOf) t0)))
  (* val () = assert (ae = ae0) *)
  val ae0 = (fst o dest_eq o concl) t1
  val ae1 = (snd o dest_eq o concl) t1
  val t2 = tce ae1
  val mp = REWRITE_RULE [SYM t1] t2
  val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0)
in
  (be, ae, mp)
end


val matchpat = ``~(w2n x + y + 1 < 18446744073709551616)``
fun matchfun t = (let val v = match_term matchpat t in (SOME v) end) handle _ => (NONE)

(valOf (matchfun ``~(w2n x + 1234 + 1 < 18446744073709551616)``))

val prefix = ""

exp


 val t0 = (SOME (SIMP_CONV (bool_ss) [w2n_of_not_zero_thm] exp))
val t1 = (TRANS (valOf t0) (SIMP_CONV (bool_ss) [plus_lt_2exp64_tm] ((snd o dest_eq o concl o valOf) t0)))
  (* val () = assert (ae = ae0) *)
  val ae0 = (fst o dest_eq o concl) t1
  val ae1 = (snd o dest_eq o concl) t1
  val t2 = #3 (tce ae1)
  val mp = REWRITE_RULE [SYM t1] t2
  val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0)







 (myss)?


(* dest_neg *) (fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) carry_thm (* ``(if e < 18446744073709551616 then e else e MOD 18446744073709551616) ≠ e`` *)
val [[t]] = arm8_step_code `ADDS X1, X2, X3 `;
val s1 = ((optionSyntax.dest_some o snd o dest_comb o concl) t);
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.C``;
val abc2 = tc_exp_arm8 exp;

(* BIT *) (fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) BIT63_thm
bitSyntax.is_bit ``BIT 63 n``
is_boolean ``BIT 32 n``

(* n2w *) (fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) Bword_add_64_thm
wordsSyntax.is_n2w ``n2w (a + b)``




val (code, pc) = (List.nth(instructions, 1), ``8w:word64``);
val th = tc_one_instruction2_by_bin code pc ``\x.x<+0x100000w:word64``;

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



eb1f001f
eb1f001f
val [t] = arm8_step_hex "eb1f001f";
val s1 = ((optionSyntax.dest_some o snd o dest_comb o concl) t);
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.V``;
val abc1 = tc_exp_arm8 exp;


val thl0 = [];
val thl1 = [BIT63_thm,Bword_add_64_thm];
val ae = ``BIT 63 (w2n (s.REG 0w) + 18446744073709551615 + 1)``;

val no_thl0 = (List.length thl0 = 0)
val t0 = if no_thl0 then NONE else (SOME (SIMP_CONV (myss) thl0 ae))
val t1 = if no_thl0 then (SIMP_CONV (myss) thl1 ae) else (TRANS (valOf t0) (SIMP_CONV (myss) thl1 ((snd o dest_eq o concl o valOf) t0)))
(* val () = assert (ae = ae0) *)
val ae0 = (fst o dest_eq o concl) t1
val ae1 = (snd o dest_eq o concl) t1
val t2 = #3 (tc_exp_arm8 ae1)
val mp = REWRITE_RULE [SYM t1] t2
val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0)



(tc_exp_arm8 ``(n2w (w2n (s.REG 0w) + 18446744073709551615 + 1) >>>~ 63w:word64)``)
(tc_exp_arm8 ``word_lsb (0w:word64)``)


