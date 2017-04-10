val lasttimer = start_time();
(*HOL_Interactive.toggle_quietdec();*)
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


use "./aescode/to_fix/aes_p.sml";

(*HOL_Interactive.toggle_quietdec();*)





print "\r\n ======== LOADED everything ========\r\n";
end_time lasttimer;
val lasttimer = start_time();




(*
(* example axiomatic *)
val first_addr   = ``0x400520w:word64``;
val AESC_mem        = ``\x.((0x400520w:word64)<=+x)/\(x<+(0x400522w:word64))``;
val _ = new_constant("AESC_mem_memf", mk_vartype "word64 -> word8");
val AESC_mem_memf_axiom = new_axiom("AESC_mem_memf_axiom", ``
  (AESC_mem_memf (0x400520w:word64) = 0xFFw:word8) /\ (AESC_mem_memf (0x400521w:word64) = 0xC3w:word8)``);
val AESC_mem_val    = ``AESC_mem_memf:word64->word8``;
val AESC_mem_in_mem = ``!addr. ^AESC_mem addr ==> (s.MEM addr = ^AESC_mem_val addr)``;


val aesc_in_mem    = ``^AESC_mem_in_mem``;
val prog_counter   = ``s.PC = ^first_addr``;
val stack_pointer  = ``s.SP_EL0 = 0x8000000FFw``;


val precond_arm = Define `P s = ^aesc_in_mem /\ ^prog_counter /\ ^stack_pointer`;

val memf_axioms = [AESC_mem_memf_axiom];
*)


val memf_axioms = [AESC_mem_memf_axiom, Te_mem_memf_axiom, Td_mem_memf_axiom, Td4_mem_memf_axiom];


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




val thm_if = prove(``!pa v1 . (if s.MEM pa = v1 then Reg1 (1w:word1) else Reg1 0w) = Reg1 (if s.MEM pa = v1 then 1w:word1 else 0w)``,
    (RW_TAC (srw_ss()) [])
);





print "\r\n ======== BEFORE INDIVIDUAL LIFTING ========\r\n";
end_time lasttimer;
val lasttimer = start_time();






(*val conv_val_x = List.nth(conv_val,2);*)
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
  
    (* /\ pco = (SOME <|label := Address (Reg64 ^first_addr); index := 0|>)*)







print "\r\n ======== AFTER INDIVIDUAL LIFTING ========\r\n";
end_time lasttimer;
val lasttimer = start_time();







val conv_bil = let val (x,_,_) = tc_exp_arm8_prefix (list_mk_conj conv_vals) "" in x end;
val Pb_def = Define `Pb env = (bil_eval_exp ^conv_bil env = Int (bool2b T))`;



val overallgoal_ant = ``P s /\ sim_invariant s env pco``;
val overallgoal = ``!s env pco. ^overallgoal_ant ==> Pb env``;



(*
val thm1 = List.nth (goal_thms, 0);
*)
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
(*
      EVERY (List.tabulate ( an - af, fn x =>
        let
          val a = wordsSyntax.mk_wordii (af + x, 64)
        in
          ASSUME_TAC (SPEC a thm)
        end
        ) )
*)
    end
  )
;






print "\r\n ======== BEFORE p and S IS ENTAILED ========\r\n";
end_time lasttimer;
val lasttimer = start_time();




val list_ax_thms = List.foldr (fn (x,y) => List.concat [CONJUNCTS x, y]) [] memf_axioms;
val memf_aesc_len = (List.length o CONJUNCTS o hd) memf_axioms;

(*
val anttm = fst (List.nth(implics, 0));
val idx = 0;
*)
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
end_time lasttimer;
val lasttimer = start_time();


(*
val allconjs = (List.map ((hd o snd o strip_comb o fst o dest_eq) o snd) implics);


val termList = List.map (snd) implics;
val termImpl = List.foldl mk_imp (concl faerdigt) termList;

val termList = List.concat [List.map (snd) implics, [concl faerdigt]];
val termImpl = List.foldl (fn (thd,trest) =>
    mk_imp (thd, trest)
  )
  (last termList)
  ((tl o List.rev) termList)
;

(UNDISCH_ALL o ASSUME) termImpl
*)
 
(*
val testt = prove(``(x = (5w:word64)) ==> (y = (3w:word64)) ==> (x + y = 8w)``, STRIP_TAC THEN (RW_TAC bool_ss []) THEN EVAL_TAC);
val assumAB = ASSUME ``(x = (5w:word64)) /\ (y = (3w:word64))``;
val afterAssum = CONJUNCT1 (CONJ testt assumAB);

DISCH_ALL (MP (MP afterAssum ((CONJUNCT1 o CONJUNCT2) (CONJ testt assumAB))) ((CONJUNCT2 o CONJUNCT2) (CONJ testt assumAB)))
*)



val bil_eval_and2_thm = prove(``!x y xv yv env. (bil_eval_exp x env = Int (bool2b xv)) ==> (bil_eval_exp y env = Int (bool2b yv)) ==> (bil_eval_exp (And x y) env = Int (bool2b (xv /\ yv)))``,
  (RW_TAC (srw_ss()) [])
  THEN (Cases_on `xv`)
  THEN (Cases_on `yv`)
(*  THEN (RW_TAC (srw_ss()) []) *)
  
  THEN (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def])
  THEN (FULL_SIMP_TAC (srw_ss()) [])
  THEN (EVAL_TAC)
);

val bil_eval_and_spec_thm = ((GENL [``x:bil_exp_t``, ``y:bil_exp_t``]) o (SIMP_RULE bool_ss []) o (SPECL [``x:bil_exp_t``, ``y:bil_exp_t``, ``T``, ``T``, ``env:environment``])) bil_eval_and2_thm;


val allconjs = (List.map ((hd o snd o strip_comb o fst o dest_eq) o snd) implics);

(*
val thm1 = ((ASSUME o snd o last) implics);
val bi = ((hd o snd o strip_comb o fst o dest_eq) o snd o hd o tl o List.rev) implics;

val thm1 = MP (DISCH (concl thm1) thm2) thm1;
val bi = ((hd o snd o strip_comb o fst o dest_eq) o snd o hd o tl o tl o List.rev) implics;
*)
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

(*
val termList = List.concat [List.map (snd) implics, [concl thmWeActuallyWant]];
val termImpl = List.foldl (fn (thd,trest) =>
    mk_imp (thd, trest)
  )
  (last termList)
  ((tl o List.rev) termList)
;
*)

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

(*
List.map concl (List.tabulate (length implics, fn x => conjunctAt x ((length implics) - 1) assumAB))
*)

val Pb_ent = ((GEN ``env:environment``) o (REWRITE_RULE [(SYM o (SPEC ``env:environment``)) Pb_def]) o DISCH_ALL) thmAlmost;
(*
val Pb_ent_goal = ``!env. ^(list_mk_conj (List.map snd implics)) ==> Pb env``;
val Pb_ent_check = prove(``^Pb_ent_goal``, ACCEPT_TAC Pb_ent);
*)

(*
val testt = prove(``(x = (5w:word64)) ==> (y = (3w:word64)) ==> (x + y = 8w)``, STRIP_TAC THEN (RW_TAC bool_ss []) THEN EVAL_TAC);
val assumAB = ASSUME ``(x = (5w:word64)) /\ (y = (3w:word64))``;
val conjAssum = CONJ testt assumAB;
val afterAssum = CONJUNCT1 conjAssum;

DISCH_ALL (MP (MP afterAssum ((CONJUNCT1 o CONJUNCT2) conjAssum)) ((CONJUNCT2 o CONJUNCT2) conjAssum))
*)



(*
val arg1 = (hd allconjs);
val arg2 = (hd (tl allconjs));

val thm1 = SIMP_RULE bool_ss [] (UNDISCH (SPECL [arg1, arg2, ``T``, ``T``, ``env:environment``] bil_eval_and2_thm));

val storkonj = list_mk_conj (List.map snd implics);
*)


(*
val Pb_ent_goal = ``!env. ^(list_mk_conj (List.map snd implics)) ==> Pb env``;
*)


(*
(* --------------------------------------------------------------- *)


val bil_eval_and2_thm = prove(``!x y xv yv env. (bil_eval_exp x env = Int (bool2b xv)) ==> (bil_eval_exp y env = Int (bool2b yv)) ==> (bil_eval_exp (And x y) env = Int (bool2b (xv /\ yv)))``,
  (RW_TAC (srw_ss()) [])
  THEN (Cases_on `xv`)
  THEN (Cases_on `yv`)
(*  THEN (RW_TAC (srw_ss()) []) *)
  
  THEN (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def])
  THEN (FULL_SIMP_TAC (srw_ss()) [])
  THEN (EVAL_TAC)
);


(*exception SomeRandomException;*)
val bil_and_tac = ((fn (ass, go) =>
    let
      val exp = (fst o dest_eq) go
      val (f, [arg, env]) = strip_comb exp
      val (f, [arg1, arg2]) = strip_comb arg
    in
      if f <> ``And`` then
      	(*raise SomeRandomException*)
        (*ALL_TAC (ass, go)*) FAIL_TAC "unknown exception" (ass, go)
      else
        let
          val thm1 = SIMP_RULE bool_ss [] (UNDISCH (SPECL [arg1, arg2, ``T``, ``T``, env] bil_eval_and2_thm))
          val hyp = (fst o dest_imp o concl) thm1
        in
	  (
            (SUBGOAL_THEN hyp (fn thm => (ACCEPT_TAC (MP thm1 thm)) ))
            (*(ASSUME_TAC thm) THEN (ASSUME_TAC thm1) THEN (REV_FULL_SIMP_TAC bool_ss [])))*)
            THEN ALL_TAC
          )(ass, go)
        end
    end
  ))
;


val Pb_ent_goal = ``!env. ^(list_mk_conj (List.map snd implics)) ==> Pb env``;
val Pb_ent = prove(``^Pb_ent_goal``,
  (RW_TAC (srw_ss()) [])
  THEN (SIMP_TAC (bool_ss) [Pb_def])

(*  THEN (REPEAT (CHANGED_TAC bil_and_tac)) *)
  THEN (REPEAT bil_and_tac)
  
  THEN (FULL_SIMP_TAC (bool_ss) [])
  


(*
  THEN (fn (ass, go) =>
    let val exp = (fst o dest_eq) go
	val (f, [arg, env]) = strip_comb exp
	val (f, [arg1, arg2]) = strip_comb arg
	val thm1 = (UNDISCH (SPECL [arg1, arg2, ``T``, ``T``, env] bil_eval_and2_thm))
	val hyp = (fst o dest_imp o concl) thm1
    in  (
        (SUBGOAL_THEN hyp (fn thm => (ASSUME_TAC thm) THEN (ASSUME_TAC thm1) THEN (REV_FULL_SIMP_TAC bool_ss [])))
    	THEN ALL_TAC
	)(ass, go)
    end
  )
*)



(*
  THEN (REWRITE_TAC [bil_eval_and2_thm])

val go = ``bil_eval_exp
  (And
     (Equal
        (Load (Den "arm8_state_MEM") (Const (Reg64 0x400520w))
           (Const (Reg1 1w)) Bit8) (Const (Reg8 255w)))
     (And
        (Equal
           (Load (Den "arm8_state_MEM") (Const (Reg64 0x400521w))
              (Const (Reg1 1w)) Bit8) (Const (Reg8 195w)))
        (And (Equal (Den "arm8_state_PC") (Const (Reg64 0x400520w)))
           (Equal (Den "arm8_state_SP_EL0")
              (Const (Reg64 0x8000000FFw)))))) env =
Int (bool2b T)``;

val go = ``bil_eval_exp
  (Equal (Den "arm8_state_SP_EL0") (Const (Reg64 0x8000000FFw))) env =
Int (bool2b T)``;

*)


(*
  THEN (List.foldr (fn (x,y) => x THEN y) ALL_TAC
                       (List.tabulate (List.length implics - 1, fn _ =>
                         (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def]) THEN (FULL_SIMP_TAC (srw_ss()) []))))
  (*
  THEN (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def]) THEN (FULL_SIMP_TAC (srw_ss()) [])
  THEN (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def]) THEN (FULL_SIMP_TAC (srw_ss()) [])
  *)
  THEN (EVAL_TAC)
*)
);



(*
REWRITE_TAC (* possibly instanciate theorem with actual values *)

CONJ_TAC

ACCEPT_TAC

(fn (ass,g) =>
 (ALL_TAC)(ass,g)
)
FIRST_ASSUM
POP_ASSUM_LIST

*)

(* --------------------------------------------------------------- *)
*)

print "\r\n ======== AFTER /\\pb |- Pb ========\r\n";
end_time lasttimer;
val lasttimer = start_time();






val v_pco = ``pco:programcounter option``;
val v_env = ``env:environment``;
val v_s = ``s:arm8_state``;
val quantif_remov = SPEC v_pco o SPEC v_env o SPEC v_s;
val quantif_add = GEN v_s o GEN v_env o GEN v_pco;

(*
val x1 = List.nth(pandSentailed,0);
val x2 = List.nth(goal_thms,0);
*)
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














(* --------------------------------------------------



(*
    (test := thm; dsfasdf)
val test = ref Pb_def
test := ``y``
val thm = !test
*)




val precon_sim_proof = prove(``^overallgoal``,
       (REPEAT STRIP_TAC)
  THEN (FULL_SIMP_TAC (simpLib.empty_ss) )
);






val precon_sim_proof = prove(``^overallgoal``,
       (REPEAT STRIP_TAC)
  THEN (FULL_SIMP_TAC (simpLib.empty_ss) [sim_invariant_def, precond_arm, Pb_def]) (* goal_thms *)
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


   -------------------------------------------------- *)
