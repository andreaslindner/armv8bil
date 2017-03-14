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

(*
(* example axiomatic *)
val first_addr   = ``0x400520w:word64``;
val AESC_mem        = ``\x.((0x400520w:word64)<=+x)/\(x<+(0x400522w:word64))``;
val _ = new_constant("AESC_mem_memf", mk_vartype "word64 -> word8");
val AESC_mem_memf_axiom = new_axiom("AESC_mem_memf_axiom", ``
  (AESC_mem_memf (0x400520w:word64) = 0xFFw:word8) /\ (AESC_mem_memf (0x400521w:word64) = 0xC3w:word8) /\ T``);
val AESC_mem_val    = ``AESC_mem_memf:word64->word8``;
val AESC_mem_in_mem = ``!addr. ^AESC_mem addr ==> (a.MEM addr = ^AESC_mem_val addr)``;


val aesc_in_mem    = ``^AESC_mem_in_mem``;
val prog_counter   = ``a.PC = ^first_addr``;
val stack_pointer  = ``a.SP_EL0 = 0x8000000FFw``;


val precond_arm = Define `P a = ^aesc_in_mem /\ ^prog_counter /\ ^stack_pointer`;
*)


val memf_axioms = [AESC_mem_memf_axiom, Te_mem_memf_axiom, Td_mem_memf_axiom, Td4_mem_memf_axiom];


(* expand predicate as preparation for expression lifting *)
exception UnsupportedForPrecondConversionException of term;
fun conv_fun t =
  if is_conj t then
    let
      val conj = dest_conj t
      val lt = fst conj
      val rt = snd conj
    in
      mk_conj (conv_fun lt, conv_fun rt)
    end
  else if is_eq t then
    t
  else if is_forall t then
    let
      val (vars,_) = match_term ``!a. (\x.(af<=+x)/\(x<+an)) a ==> (s.MEM a = memf a)`` t
      val af = wordsSyntax.uint_of_word (subst vars ``af:word64``)
      val an = wordsSyntax.uint_of_word (subst vars ``an:word64``)
      val memf = subst vars ``memf:word64->word8``
      val amemf = ``s.MEM``
    in
      list_mk_conj (List.tabulate ( an - af, fn x =>
        let
          val a = wordsSyntax.mk_wordii (af + x, 64)
        in
          mk_eq (mk_comb(amemf, a), (snd o dest_eq o concl o (SIMP_CONV (srw_ss()) memf_axioms) o mk_comb) (memf, a))
        end
        ) )
    end
  else
    raise UnsupportedForPrecondConversionException t
;

val conv_val = conv_fun ((snd o dest_eq o concl o (SPEC ``a:arm8_state``)) precond_arm);
val conv_bil = let val (x,_,_) = tc_exp_arm8_prefix conv_val "" in x end;
val Pb_def = Define `Pb env = (bil_eval_exp ^conv_bil env = Int (bool2b T))`;





val thm_if = prove(``!pa v1 . (if s.MEM pa = v1 then Reg1 (1w:word1) else Reg1 0w) = Reg1 (if s.MEM pa = v1 then 1w:word1 else 0w)``,
    (RW_TAC (srw_ss()) [])
);

val tac_expand =
  PAT_ASSUM ``!x.p ==> q`` (fn thm =>
    let   
      val (vars,_) = match_term ``!a. (\x.(af<=+x)/\(x<+an)) a ==> (s.MEM a = memf a)``(*``!a. ((af<=+a) /\ (a<+an)) ==> (s.MEM a = memf a)``*) (concl thm)
      val af = wordsSyntax.uint_of_word (subst vars ``af:word64``)
      val an = wordsSyntax.uint_of_word (subst vars ``an:word64``)
    in
      EVERY (List.tabulate ( an - af, fn x =>
        let
          val a = wordsSyntax.mk_wordii (af + x, 64)
        in
          ASSUME_TAC (SPEC a thm)
        end
        ) )
    end
  )
;

(*
    (test := thm; dsfasdf)
val test = ref Pb_def
test := ``y``
val thm = !test
*)


val goal = ``!s env. (P s /\ sim_invariant s env (SOME <|label := Address (Reg64 ^first_addr); index := 0|>)) ==> Pb env``;
val precon_sim_proof = prove(``^goal``,
       (REPEAT STRIP_TAC)
  THEN (FULL_SIMP_TAC (simpLib.empty_ss) [sim_invariant_def, precond_arm, Pb_def])
  THEN (tac_expand)
  THEN (EVAL_TAC)
  THEN (FULL_SIMP_TAC (srw_ss()) [thm_if])
  THEN (FULL_SIMP_TAC (srw_ss()) [])
  THEN (`s.PC = ^first_addr` by (RW_TAC (srw_ss()) []))
  THEN (FULL_SIMP_TAC (srw_ss()) memf_axioms)
);







(*

(*val _ = new_constant(``f:word64 -> word8``);*)
val _ = new_constant("Ff_a", mk_vartype "word64->word8");


val f_axiom = new_axiom("f_axiom",
      ``   (Ff_a 0x0001w = 02w)
        /\ (Ff_a 0x0002w = 18w) /\ T``);

EVAL ``Ff_a 1w:word64``;
SIMP_CONV (bool_ss) [f_axiom] ``Ff_a 3w:word64``;

SIMP_CONV (bool_ss) [AESC_mem_memf_axiom] ``(AESC_mem_memf (0x40054Ew:word64)):word8``;





TypeBase.mk_case (``x:word64``, [(``1w:word64``,``5w:word16``), (``3w:word64``,``44w:word16``),(``xx:word64``,``3w:word16``)]);

``1w:word8 - 2w:word8``


*)