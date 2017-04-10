(* HOL_Interactive.toggle_quietdec(); *)
open HolKernel boolLib bossLib Parse;
open lcsymtacs utilsLib;
open wordsLib blastLib;
open aes_code;
open aes_mem;
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
(* HOL_Interactive.toggle_quietdec(); *)

val _ = new_theory "aesProp1Cond";





fun holWord64Plus hx iy =
  wordsSyntax.mk_wordii ((wordsSyntax.uint_of_word hx) + iy, 64);

fun nextBytesOf fstad bytesarr =
  holWord64Plus fstad (length bytesarr);

fun axiomFromMem fstad bytesarr mem_val =
  list_mk_conj (List.tabulate (length bytesarr, fn x => mk_eq (mk_comb (mem_val, holWord64Plus fstad x), List.nth (bytesarr, x))))

val AESC_mem        = ``\x.((^AESC_mem_fstad)<=+x)/\(x<+(^(nextBytesOf AESC_mem_fstad AESC_mem_bytes)))``;
val _ = new_constant ("AESC_mem_memf", mk_vartype "word64 -> word8");
val AESC_mem_val    = ``AESC_mem_memf:word64->word8``;
val AESC_mem_memf_axiom_def = new_axiom ("AESC_mem_memf_axiom", axiomFromMem AESC_mem_fstad AESC_mem_bytes AESC_mem_val);
val AESC_mem_in_mem = ``!addr. ^AESC_mem addr ==> (s.MEM addr = ^AESC_mem_val addr)``;

val Te_mem        = ``\x.((^Te_mem_fstad)<=+x)/\(x<+(^(nextBytesOf Te_mem_fstad Te_mem_bytes)))``;
val _ = new_constant ("Te_mem_memf", mk_vartype "word64 -> word8");
val Te_mem_val    = ``Te_mem_memf:word64->word8``;
val Te_mem_memf_axiom_def = new_axiom ("Te_mem_memf_axiom", axiomFromMem Te_mem_fstad Te_mem_bytes Te_mem_val);
val Te_mem_in_mem = ``!addr. ^Te_mem addr ==> (s.MEM addr = ^Te_mem_val addr)``;

val Td_mem        = ``\x.((^Td_mem_fstad)<=+x)/\(x<+(^(nextBytesOf Td_mem_fstad Td_mem_bytes)))``;
val _ = new_constant ("Td_mem_memf", mk_vartype "word64 -> word8");
val Td_mem_val    = ``Td_mem_memf:word64->word8``;
val Td_mem_memf_axiom_def = new_axiom ("Td_mem_memf_axiom", axiomFromMem Td_mem_fstad Td_mem_bytes Td_mem_val);
val Td_mem_in_mem = ``!addr. ^Td_mem addr ==> (s.MEM addr = ^Td_mem_val addr)``;

val Td4_mem        = ``\x.((^Td4_mem_fstad)<=+x)/\(x<+(^(nextBytesOf Td4_mem_fstad Td4_mem_bytes)))``;
val _ = new_constant ("Td4_mem_memf", mk_vartype "word64 -> word8");
val Td4_mem_val    = ``Td4_mem_memf:word64->word8``;
val Td4_mem_memf_axiom_def = new_axiom ("Td4_mem_memf_axiom", axiomFromMem Td4_mem_fstad Td4_mem_bytes Td4_mem_val);
val Td4_mem_in_mem = ``!addr. ^Td4_mem addr ==> (s.MEM addr = ^Td4_mem_val addr)``;




val aesc_in_mem    = ``^AESC_mem_in_mem``;
val prog_counter   = ``s.PC = ^instrs_fstad``;
val stack_pointer  = ``s.SP_EL0 = 0x8000000FFw``;
val sbox_in_mem    = ``^Te_mem_in_mem /\ ^Td_mem_in_mem /\ ^Td4_mem_in_mem``;

val precond_arm = Define `P s = ^aesc_in_mem /\ ^prog_counter /\ ^stack_pointer /\ ^sbox_in_mem`;

val memf_axioms = [AESC_mem_memf_axiom_def, Te_mem_memf_axiom_def, Td_mem_memf_axiom_def, Td4_mem_memf_axiom_def];






print "\r\n ======== LOADED everything ========\r\n";

val instrs_lstad = holWord64Plus (nextBytesOf AESC_mem_fstad AESC_mem_bytes) ~4;

(* postcondition in ARM *)
val prog_counter   = ``s.PC = ^instrs_lstad``;
val postcond_arm = Define `Q s = ^prog_counter`;


(* lifting and bil equivalent *)
val conv_val = (snd o dest_eq o concl o (SPEC ``s:arm8_state``)) postcond_arm;
val conv_bil = let val (x,_,_) = tc_exp_arm8_prefix conv_val "" in x end;
val Qb_def = Define `Qb env = (bil_eval_exp ^conv_bil env = Int (bool2b T))`;

(*/////// check invariant definition wrt program counter, bil PC and arm PC register preserving?!?!?!
*)

(* proving postcondition transfer under simulation *)
val goal = ``!s env. (Qb env /\ sim_invariant s env (SOME <|label := Address (Reg64 ^instrs_lstad); index := 0|>)) ==> Q s``;
val postcon_sim_proof = prove(``^goal``,
       (REPEAT STRIP_TAC)
  THEN (FULL_SIMP_TAC (simpLib.empty_ss) [Qb_def, postcond_arm, sim_invariant_def])
  THEN (Cases_on `^prog_counter`)

  THEN (FULL_SIMP_TAC (srw_ss()) [])
);

val postcond_thm = save_thm("postcond_thm", postcon_sim_proof);



print "\r\n ======== Postcondition done ========\r\n";

(* expand predicate as preparation for expression lifting *)
(*
val t = (fst o dest_conj o snd o dest_eq o concl o (SPEC ``s:arm8_state``)) precond_arm;
val x = 0;
*)
exception UnsupportedForPrecondConversionException of term;
fun conv_fun t =
  if is_conj t then
    let
      val conj = dest_conj t
      val lt = fst conj
      val rt = snd conj
    in
      (conv_fun lt) @ (conv_fun rt)
    end
  else if is_eq t then
    [t]
  else if is_forall t then
    let
      val (vars,_) = match_term ``!a. (\x.(af<=+x)/\(x<+an)) a ==> (s.MEM a = memf a)`` t
      val af = wordsSyntax.uint_of_word (subst vars ``af:word64``)
      val an = wordsSyntax.uint_of_word (subst vars ``an:word64``)
      val memf = subst vars ``memf:word64->word8``
      val amemf = ``s.MEM``
    in
      (List.tabulate ( an - af, fn x =>
        let
          val a = wordsSyntax.mk_wordii (af + x, 64)
	  val arm_eq = mk_eq (mk_comb(amemf, a), (snd o dest_eq o concl o (SIMP_CONV (srw_ss()) memf_axioms) o mk_comb) (memf, a))
        in
          arm_eq
        end
        ) )
    end
  else
    raise UnsupportedForPrecondConversionException t
;

val conv_vals = conv_fun ((snd o dest_eq o concl o (SPEC ``s:arm8_state``)) precond_arm);









print "\r\n ======== BEFORE INDIVIDUAL LIFTING ========\r\n";

val thm_if = prove(``!pa v1 . (if s.MEM pa = v1 then Reg1 (1w:word1) else Reg1 0w) = Reg1 (if s.MEM pa = v1 then 1w:word1 else 0w)``,
    (RW_TAC (srw_ss()) [])
);

val goal_thms = List.map (fn conv_val_x =>
  let
    val bil_val_x = let val (x,_,_) = tc_exp_arm8_prefix conv_val_x "" in x end
    val goal = ``!s env pco. (^conv_val_x /\ sim_invariant s env pco) ==> (bil_eval_exp ^bil_val_x env = Int (bool2b T))``
    val thm_g = prove(``^goal``,
           (REPEAT STRIP_TAC)
      THEN (FULL_SIMP_TAC (simpLib.empty_ss) [sim_invariant_def])
      THEN (EVAL_TAC)
      THEN (FULL_SIMP_TAC (srw_ss()) [thm_if])
      )
  in
    thm_g
  end
  ) conv_vals;







print "\r\n ======== AFTER INDIVIDUAL LIFTING ========\r\n";

val conv_bil = let val (x,_,_) = tc_exp_arm8_prefix (list_mk_conj conv_vals) "" in x end;
val Pb_def = Define `Pb env = (bil_eval_exp ^conv_bil env = Int (bool2b T))`;

val overallgoal_ant = ``P s /\ sim_invariant s env pco``;
val overallgoal = ``!s env pco. ^overallgoal_ant ==> Pb env``;

val implics = List.map (dest_imp o snd o dest_forall o snd o dest_forall o snd o dest_forall o concl) goal_thms;

fun tac_expand addr =
  PAT_ASSUM ``!x.p ==> q`` (fn thm =>
    let   
      val (vars,_) = match_term ``!a. (\x.(af<=+x)/\(x<+an)) a ==> (s.MEM a = memf a)``(*``!a. ((af<=+a) /\ (a<+an)) ==> (s.MEM a = memf a)``*) (concl thm)
      val af = wordsSyntax.uint_of_word (subst vars ``af:word64``)
      val an = wordsSyntax.uint_of_word (subst vars ``an:word64``)
    in
      if af <= addr andalso addr < an then
        let
          val a = wordsSyntax.mk_wordii (addr, 64)
        in
          ASSUME_TAC (SPEC a thm)
        end
      else
        ALL_TAC
    end
  )
;






print "\r\n ======== BEFORE p and S IS ENTAILED ========\r\n";

val list_ax_thms = List.foldr (fn (x,y) => List.concat [CONJUNCTS x, y]) [] memf_axioms;
val memf_aesc_len = (List.length o CONJUNCTS o hd) memf_axioms;

val pandSentailed = List.tabulate (List.length implics, fn idx =>
  let
    val anttm = (fst o List.nth) (implics, idx);
    val memf_thm = if (idx < memf_aesc_len) then
                     [List.nth (list_ax_thms, idx)]
                   else if (idx >= memf_aesc_len + 2) then
		     [List.nth (list_ax_thms, idx - 2)]
		   else
		     [];
    val tac_expand_inst = if (memf_aesc_len <= idx andalso idx < memf_aesc_len + 2) then
                            ALL_TAC
			  else
			    tac_expand ((wordsSyntax.uint_of_word o snd o dest_comb o fst o dest_eq o concl o hd) memf_thm);
    val subgoal = ``!s env pco. ^overallgoal_ant ==> ^anttm``;
  in
    prove(``^subgoal``,
      (REPEAT STRIP_TAC)
      THEN (FULL_SIMP_TAC (simpLib.empty_ss) [precond_arm])
      THEN (tac_expand_inst)
      THEN (FULL_SIMP_TAC (srw_ss()) memf_thm)
      THEN (FULL_SIMP_TAC (srw_ss()) [])
    )
  end
  );






print "\r\n ======== BEFORE /\\pb |- Pb ========\r\n";

val bil_eval_and2_thm = prove(``!x y xv yv env. (bil_eval_exp x env = Int (bool2b xv)) ==> (bil_eval_exp y env = Int (bool2b yv)) ==> (bil_eval_exp (And x y) env = Int (bool2b (xv /\ yv)))``,
  (RW_TAC (srw_ss()) [])
  THEN (Cases_on `xv`)
  THEN (Cases_on `yv`)  
  THEN (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def])
  THEN (FULL_SIMP_TAC (srw_ss()) [])
  THEN (EVAL_TAC)
);

val bil_eval_and_spec_thm = ((GENL [``x:bil_exp_t``, ``y:bil_exp_t``]) o (SIMP_RULE bool_ss []) o (SPECL [``x:bil_exp_t``, ``y:bil_exp_t``, ``T``, ``T``, ``env:environment``])) bil_eval_and2_thm;

val allconjs = (List.map ((hd o snd o strip_comb o fst o dest_eq) o snd) implics);


val thmWeActuallyWant = List.foldr (fn (bi,thm1) =>
    let
      val bexp_y = ((hd o snd o strip_comb o fst o dest_eq) o concl) thm1;
      val thm2 = (UNDISCH o UNDISCH o (SPECL [bi, bexp_y])) bil_eval_and_spec_thm;
    in
      MP (DISCH (concl thm1) thm2) thm1
    end
  )
  ((ASSUME o snd o last) implics)
  ((List.rev o tl o List.rev) allconjs);

val thmImpChain = List.foldr (fn (x,y) => DISCH x y) thmWeActuallyWant (List.map (snd) implics); (* DISCH_ALL *)



val assumAB = (ASSUME o list_mk_conj) (List.map (snd) implics);
val conjAssum = CONJ thmImpChain assumAB;
val afterAssum = CONJUNCT1 conjAssum;
fun conjunctAt x last =
  let
    val conj2chain = if x = 0 then (fn x => x) else (List.foldr (fn (x,y) => y o x) (CONJUNCT2) (List.tabulate (x-1, fn _ => CONJUNCT2)));
  in
    if x = last then
      conj2chain
    else
      CONJUNCT1 o conj2chain
  end
;

val thmAlmost = List.foldl (fn (cNext,x) =>
    MP x cNext
  )
  afterAssum
  (List.tabulate (length implics, fn x => conjunctAt x ((length implics) - 1) assumAB))
;

val Pb_ent = ((GEN ``env:environment``) o (REWRITE_RULE [(SYM o (SPEC ``env:environment``)) Pb_def]) o DISCH_ALL) thmAlmost;







print "\r\n ======== AFTER /\\pb |- Pb ========\r\n";

val v_pco = ``pco:programcounter option``;
val v_env = ``env:environment``;
val v_s = ``s:arm8_state``;
val quantif_remov = SPEC v_pco o SPEC v_env o SPEC v_s;
val quantif_add = GEN v_s o GEN v_env o GEN v_pco;

fun mp_list list1 list2 =
  if null list1 then
    []
  else
    let
      val x1 = hd list1
      val x2 = hd list2
      val y1 = (UNDISCH_ALL o quantif_remov) x1
      val z = (*(quantif_add o DISCH_ALL)*) (MATCH_MP x2 y1)
    in
      z::(mp_list (tl list1) (tl list2))
    end
  ;

val thm_list = List.rev (mp_list pandSentailed goal_thms);

val thm_conj =
  if length(thm_list) < 2 then
    hd thm_list
  else
    List.foldl (fn (x,y) => CONJ x y) (hd thm_list) (tl thm_list)
  ;

val precon_sim_proof = (quantif_add o DISCH_ALL) (MATCH_MP Pb_ent thm_conj);






print "\r\n ======== AFTER |- P /\\ sim ==> Pb  ========\r\n";

val goal = ``!s env pco. ^overallgoal_ant ==> (Pb env /\ (pco = SOME <|label := Address (Reg64 ^instrs_fstad); index := 0|>))``;
val goal_thm = prove(``^goal``,
  (REPEAT STRIP_TAC)
  THENL [
    (ASSUME_TAC (quantif_remov precon_sim_proof))
    THEN (FULL_SIMP_TAC (bool_ss) [])
    ,
    ALL_TAC]
  THEN (FULL_SIMP_TAC (simpLib.empty_ss) [sim_invariant_def, precond_arm])
  THEN (EVAL_TAC)
  );

val precond_thm = save_thm("precond_thm", goal_thm);






print "\r\n ======== AFTER |- P /\\ sim ==> Pb /\\ pco ========\r\n";

val _ = export_theory();
