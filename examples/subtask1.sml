(*
val precond_arm = Define `P s = code in mem /\ prog counter /\ stack pointer /\ sbox`;


val first_addr = ``0x100000w:word64``;
val last_addr  = ``0x200000w:word64``;
val AESC_mem     = ``\x.((^first_addr)<=+x)/\(x<+(^last_addr))``;
val AESC_mem_val = ``\(x:word64). case x of 0x100000w => 0xFFw:word8 | 0x100001w => 0xAFw:word8 | _ => 0x0w``;

val test = Define `Pe s = (!a. ^AESC_mem a ==> (s.MEM a = ^AESC_mem_val a)) /\ (s.PC = ^first_addr) /\ (s.SP_EL0 = 0x8000000FFw) /\ (T=T)`;
*)



val t = (fst o dest_conj o snd o dest_eq o concl o (SPEC ``s:arm8_state``)) test



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
(*
  fun match_pat matchpat t = (let val _ = match_term matchpat t in (true) end) handle _ => (false);
  (match_pat ``(if e < 18446744073709551616 then e else e MOD 18446744073709551616) ≠ e`` ae)
*)  
  let
    val (vars,[]) = match_term ``!a. (\x.(af<=+x)/\(x<+an)) a ==> ((s:arm8_state).MEM a = memf a)`` t
    val af = subst vars ``af:word64``
    val an = subst vars ``an:word64``
    val memf = subst vars ``memf:word64->word8``
  in
    memf
    wordsSyntax.uint_of_word ``0x12w:word64``
  end (* mk_comb *)
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