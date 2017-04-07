(* HOL_Interactive.toggle_quietdec(); *)
open HolKernel boolLib bossLib Parse;
open lcsymtacs utilsLib;
open wordsLib blastLib;
open state_transformerTheory updateTheory arm8Theory;
open stateTheory;
open aes_p;
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

val first_addr   = ``0x400520w:word64``;
val AESC_mem        = ``\x.((0x400520w:word64)<=+x)/\(x<+(0x40052Aw:word64))``;
val AESC_mem_memf_axiom = ("AESC_mem_memf_axiom", ``
  (AESC_mem_memf (0x400520w:word64) = 0xFFw:word8) /\ (AESC_mem_memf (0x400521w:word64) = 0xC3w:word8) /\ 
  (AESC_mem_memf (0x400522w:word64) = 0x01w:word8) /\ (AESC_mem_memf (0x400523w:word64) = 0xD1w:word8) /\ 
  (AESC_mem_memf (0x400524w:word64) = 0xE0w:word8) /\ (AESC_mem_memf (0x400525w:word64) = 0x0Fw:word8) /\ 
  (AESC_mem_memf (0x400526w:word64) = 0x00w:word8) /\ (AESC_mem_memf (0x400527w:word64) = 0xF9w:word8) /\ 
  (AESC_mem_memf (0x400528w:word64) = 0xE1w:word8) /\ (AESC_mem_memf (0x400529w:word64) = 0x17w:word8)
``);


val Te_mem        = ``\x.((0x400E18w:word64)<=+x)/\(x<+(0x400E22w:word64))``;
val Te_mem_memf_axiom = ("Te_mem_memf_axiom", ``
  (Te_mem_memf (0x400E18w:word64) = 0xA5w:word8) /\ (Te_mem_memf (0x400E19w:word64) = 0x63w:word8) /\ 
  (Te_mem_memf (0x400E1Aw:word64) = 0x63w:word8) /\ (Te_mem_memf (0x400E1Bw:word64) = 0xC6w:word8) /\ 
  (Te_mem_memf (0x400E1Cw:word64) = 0x84w:word8) /\ (Te_mem_memf (0x400E1Dw:word64) = 0x7Cw:word8) /\ 
  (Te_mem_memf (0x400E1Ew:word64) = 0x7Cw:word8) /\ (Te_mem_memf (0x400E1Fw:word64) = 0xF8w:word8) /\ 
  (Te_mem_memf (0x400E20w:word64) = 0x99w:word8) /\ (Te_mem_memf (0x400E21w:word64) = 0x77w:word8)
``);


val Td_mem        = ``\x.((0x401E18w:word64)<=+x)/\(x<+(0x401E22w:word64))``;
val Td_mem_memf_axiom = ("Td_mem_memf_axiom", ``
  (Td_mem_memf (0x401E18w:word64) = 0x50w:word8) /\ (Td_mem_memf (0x401E19w:word64) = 0xA7w:word8) /\ 
  (Td_mem_memf (0x401E1Aw:word64) = 0xF4w:word8) /\ (Td_mem_memf (0x401E1Bw:word64) = 0x51w:word8) /\ 
  (Td_mem_memf (0x401E1Cw:word64) = 0x53w:word8) /\ (Td_mem_memf (0x401E1Dw:word64) = 0x65w:word8) /\ 
  (Td_mem_memf (0x401E1Ew:word64) = 0x41w:word8) /\ (Td_mem_memf (0x401E1Fw:word64) = 0x7Ew:word8) /\ 
  (Td_mem_memf (0x401E20w:word64) = 0xC3w:word8) /\ (Td_mem_memf (0x401E21w:word64) = 0xA4w:word8)
``);


val Td4_mem        = ``\x.((0x402E18w:word64)<=+x)/\(x<+(0x402E22w:word64))``;
val Td4_mem_memf_axiom = ("Td4_mem_memf_axiom", ``
  (Td4_mem_memf (0x402E18w:word64) = 0x52w:word8) /\ (Td4_mem_memf (0x402E19w:word64) = 0x09w:word8) /\ 
  (Td4_mem_memf (0x402E1Aw:word64) = 0x6Aw:word8) /\ (Td4_mem_memf (0x402E1Bw:word64) = 0xD5w:word8) /\ 
  (Td4_mem_memf (0x402E1Cw:word64) = 0x30w:word8) /\ (Td4_mem_memf (0x402E1Dw:word64) = 0x36w:word8) /\ 
  (Td4_mem_memf (0x402E1Ew:word64) = 0xA5w:word8) /\ (Td4_mem_memf (0x402E1Fw:word64) = 0x38w:word8) /\ 
  (Td4_mem_memf (0x402E20w:word64) = 0xBFw:word8) /\ (Td4_mem_memf (0x402E21w:word64) = 0x40w:word8)
``);

print "\r\n ======== LOADED everything ========\r\n";

val _ = new_constant ("AESC_mem_memf", mk_vartype "word64 -> word8");
val AESC_mem_memf_axiom_def = new_axiom AESC_mem_memf_axiom;
val AESC_mem_val    = ``AESC_mem_memf:word64->word8``;
val AESC_mem_in_mem = ``!addr. ^AESC_mem addr ==> (s.MEM addr = ^AESC_mem_val addr)``;

val _ = new_constant ("Te_mem_memf", mk_vartype "word64 -> word8");
val Te_mem_memf_axiom_def = new_axiom Te_mem_memf_axiom;
val Te_mem_val    = ``Te_mem_memf:word64->word8``;
val Te_mem_in_mem = ``!addr. ^Te_mem addr ==> (s.MEM addr = ^Te_mem_val addr)``;

val _ = new_constant ("Td_mem_memf", mk_vartype "word64 -> word8");
val Td_mem_memf_axiom_def = new_axiom Td_mem_memf_axiom;
val Td_mem_val    = ``Td_mem_memf:word64->word8``;
val Td_mem_in_mem = ``!addr. ^Td_mem addr ==> (s.MEM addr = ^Td_mem_val addr)``;

val _ = new_constant ("Td4_mem_memf", mk_vartype "word64 -> word8");
val Td4_mem_memf_axiom_def = new_axiom Td4_mem_memf_axiom;
val Td4_mem_val    = ``Td4_mem_memf:word64->word8``;
val Td4_mem_in_mem = ``!addr. ^Td4_mem addr ==> (s.MEM addr = ^Td4_mem_val addr)``;

val aesc_in_mem    = ``^AESC_mem_in_mem``;
val prog_counter   = ``s.PC = ^first_addr``;
val stack_pointer  = ``s.SP_EL0 = 0x8000000FFw``;
val sbox_in_mem    = ``^Te_mem_in_mem /\ ^Td_mem_in_mem /\ ^Td4_mem_in_mem``;

val precond_arm_quot = `P s = ^aesc_in_mem /\ ^prog_counter /\ ^stack_pointer /\ ^sbox_in_mem`;
val precond_arm = Define precond_arm_quot;


val memf_axioms = [AESC_mem_memf_axiom_def, Te_mem_memf_axiom_def, Td_mem_memf_axiom_def, Td4_mem_memf_axiom_def];




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
	  val arm_eq = mk_eq (mk_comb(amemf, a), (snd o dest_eq o concl o (SIMP_CONV (srw_ss()) memf_axioms) o (mk_comb) (memf, a))
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



val goal = ``!s env pco. ^overallgoal_ant ==> (Pb env /\ (pco = SOME <|label := Address (Reg64 ^first_addr); index := 0|>))``;
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




val _ = export_theory();
