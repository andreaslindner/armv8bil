(*
val precond_arm = Define `P s = code in mem /\ prog counter /\ stack pointer /\ sbox`;


val first_addr = ``0x10w:word64``;
val last_addr  = ``0x12w:word64``;
val AESC_mem     = ``\x.((^first_addr)<=+x)/\(x<+(^last_addr))``;
val AESC_mem_val = ``\(x:word64). case x of 0x10w => 0xFFw:word8 | 0x11w => 0xAFw:word8 | _ => 0x0w``;

val test = Define `Pe s = (!a. ^AESC_mem a ==> (s.MEM a = ^AESC_mem_val a)) /\ (s.PC = ^first_addr) /\ (s.SP_EL0 = 0x8000000FFw) /\ (T=T)`;



val t = (fst o dest_conj o snd o dest_eq o concl o (SPEC ``s:arm8_state``)) test
*)







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
          mk_eq (mk_comb(amemf, a), (snd o dest_eq o concl o EVAL o mk_comb) (memf, a))
        end
        ) )
    end
    (*
    let
      val forall = dest_forall t
      val var = fst forall
      val t = snd forall
    in
      if is_imp t then
        let
	  val imp = dest_imp t
	  val antec = fst imp
	  val conse = snd imp
	in
	  antec
	end
      else
        raise UnsupportedForPrecondConversionException t
    end
    *)    
  else
    raise UnsupportedForPrecondConversionException t
  ;

val conv_val = conv_fun ((snd o dest_eq o concl o (SPEC ``s:arm8_state``)) test);
(*val conv_val = (snd o dest_eq o concl o EVAL) conv_val;*)

val conv_bil = let val (x,_,_) = tc_exp_arm8_prefix conv_val "" in x end;
(*``bil_eval_exp exp env``*)

val Pb_def = Define `Pb env = (bil_eval_exp ^conv_bil env = Int (bool2b T))`;

(*
val goal = ``!s env. (Pe s /\ sim_invariant s env (SOME <|label := Address (Reg64 ^first_addr); index := 0|>)) ==> (bil_eval_exp ^conv_bil env = Int (bool2b T))``;
*)

val goal = ``!s env. (Pe s /\ sim_invariant s env (SOME <|label := Address (Reg64 ^first_addr); index := 0|>)) ==> Pb env``;

val goal = (snd o dest_eq o concl) (SIMP_CONV (bool_ss) [test, Pb_def] goal);

val thm_if = prove(``!pa v1 . (if s.MEM pa = v1 then Reg1 (1w:word1) else Reg1 0w) = Reg1 (if s.MEM pa = v1 then 1w:word1 else 0w)``,
    (RW_TAC (srw_ss()) [])
);
    

val precon_sim_proof = prove(``^goal``,
       (REPEAT STRIP_TAC)
  THEN (FULL_SIMP_TAC (bool_ss) [sim_invariant_def])
  THEN (EVAL_TAC)
  THEN (FULL_SIMP_TAC (srw_ss()) [thm_if])
  THEN (PAT_ASSUM ``!x.p ==> q`` (fn thm=> (ASSUME_TAC (SPEC ``16w:word64`` thm)) THEN (ASSUME_TAC thm)))
  THEN (PAT_ASSUM ``!x.p ==> q`` (fn thm=> (ASSUME_TAC (SPEC ``17w:word64`` thm))))
  THEN (FULL_SIMP_TAC (srw_ss()) [])
  THEN (`s.PC = 16w` by (RW_TAC (srw_ss()) []))
  THEN (FULL_SIMP_TAC (srw_ss()) [])
);



(*
fun fa a = fa a;
val t = (snd o dest_eq o concl o (SPEC ``s:arm8_state``)) test;
*)

(*
------ arm8bilInstructionLib.sml
val sim_invariant_def = Define `sim_invariant s env pco =
*)

val test2 = Define `A s = AES ==> T`;

(* val test = Define `f c = c - 2w`;
EVAL ``f 5w``; *)