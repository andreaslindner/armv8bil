open HolKernel boolLib bossLib Parse;
open wordsLib;

load "aesCodeTheory";

(* export to BAP format: first helper functions *)
(* ---------------------- *)
fun get_var_type var_name =
    if List.exists (fn tm=>tm=var_name) [``"R0"``, ``"R1"``, ``"R2"``, ``"R3"``, ``"R29"``,
                                         ``"R30"``, ``"arm8_state_PC"``, ``"arm8_state_SP_EL0"``,
                                         ``"tmp_R0"``, ``"tmp_R1"``, ``"tmp_R2"``, ``"tmp_R3"``, ``"tmp_R29"``,
                                         ``"tmp_R30"``, ``"tmp_arm8_state_PC"``, ``"tmp_arm8_state_SP_EL0"``]
       then ``Bit64``
    else if List.exists (fn tm=>tm=var_name)
            [``"ProcState_C"``, ``"ProcState_N"``, ``"ProcState_V"``, ``"ProcState_Z"``,
``"tmp_ProcState_C"``, ``"tmp_ProcState_N"``, ``"tmp_ProcState_V"``, ``"tmp_ProcState_Z"``
] then ``Bit1``
    else if var_name = ``"arm8_state_MEM"`` then ``MemByte``
    else ``T``;
    
fun print_type var_type =
    if var_type = ``Bit64`` then "u64"
    else if var_type = ``Reg64`` then "u64"
    else if var_type = ``Bit32`` then "u32"
    else if var_type = ``Reg32`` then "u32"
    else if var_type = ``Bit16`` then "u16"
    else if var_type = ``Reg16`` then "u16"
    else if var_type = ``Bit1`` then "bool"
    else if var_type = ``Reg1`` then "bool"
    else if var_type = ``MemByte`` then "?u64"
    else "ERROR";

     (* (env "ProcState_C" = (Reg Bit1,Int (bool2b s.PSTATE.C))) ∧ *)
     (* (env "ProcState_N" = (Reg Bit1,Int (bool2b s.PSTATE.N))) ∧ *)
     (* (env "ProcState_V" = (Reg Bit1,Int (bool2b s.PSTATE.V))) ∧ *)
     (* (env "ProcState_Z" = (Reg Bit1,Int (bool2b s.PSTATE.Z))) ∧ *)


(* let casttype_of_string = function *)
(*   | "pad"     -> CAST_UNSIGNED *)
(*   | "extend"  -> CAST_SIGNED   *)
(*   | "high"    -> CAST_HIGH     *)
(*   | "low"     -> CAST_LOW      *)
(*   | s -> err("Unexpected cast type '"^s^"'") *)

fun print_exp exp =
let val (ope, args) = strip_comb exp
in
    if ope = ``Den`` then
       let val var_name = hd args
           val var_type = get_var_type var_name
           val var_type_str = print_type var_type
       in "V_" ^ (stringSyntax.fromHOLstring var_name) ^ ":" ^ var_type_str end
    else if ope = ``Const`` then
       let val (var_type, [value]) = (strip_comb o hd) args
           val var_type_str = print_type var_type
           val val_str = term_to_string value
        in (String.substring(val_str, 0, String.size(val_str) -1)) ^ ":" ^ var_type_str end
    else if ope = ``Plus`` then
       let val exp1 = print_exp (List.nth(args, 0))
           val exp2 = print_exp (List.nth(args, 1))
       in "("^exp1 ^ ")+(" ^ exp2 ^ ")" end
    else if ope = ``Mult`` then
       let val exp1 = print_exp (List.nth(args, 0))
           val exp2 = print_exp (List.nth(args, 1))
       in "("^exp1 ^ ")*(" ^ exp2 ^ ")" end
    else if ope = ``Mod`` then
       let val exp1 = print_exp (List.nth(args, 0))
           val exp2 = print_exp (List.nth(args, 1))
       in "("^exp1 ^ ")%(" ^ exp2 ^ ")" end
    else if ope = ``And`` then
       let val exp1 = print_exp (List.nth(args, 0))
           val exp2 = print_exp (List.nth(args, 1))
       in "("^exp1 ^ ")&(" ^ exp2 ^ ")" end
    else if ope = ``Or`` then
       let val exp1 = print_exp (List.nth(args, 0))
           val exp2 = print_exp (List.nth(args, 1))
       in "("^exp1 ^ ")|(" ^ exp2 ^ ")" end
    else if ope = ``RightShift`` then
       let val exp1 = print_exp (List.nth(args, 0))
           val exp2 = print_exp (List.nth(args, 1))
       in "("^exp1 ^ ")>>(" ^ exp2 ^ ")" end
    else if ope = ``LeftShift`` then
       let val exp1 = print_exp (List.nth(args, 0))
           val exp2 = print_exp (List.nth(args, 1))
       in "("^exp1 ^ ")<<(" ^ exp2 ^ ")" end
    else if ope = ``Equal`` then
       let val exp1 = print_exp (List.nth(args, 0))
           val exp2 = print_exp (List.nth(args, 1))
       in "("^exp1 ^ ")==(" ^ exp2 ^ ")" end
    else if ope = ``LessThan`` then
       let val exp1 = print_exp (List.nth(args, 0))
           val exp2 = print_exp (List.nth(args, 1))
       in "("^exp1 ^ ")<(" ^ exp2 ^ ")" end
    else if ope = ``SignedLessThan`` then
       let val exp1 = print_exp (List.nth(args, 0))
           val exp2 = print_exp (List.nth(args, 1))
       in "("^exp1 ^ ")$<(" ^ exp2 ^ ")" end
    else if ope = ``Not`` then
       let val exp1 = print_exp (List.nth(args, 0))
       in "~("^exp1 ^ ")" end
    else if ope = ``ChangeSign`` then
       let val exp1 = print_exp (List.nth(args, 0))
       in "-("^exp1 ^ ")" end
    else if ope = ``LowCast`` then
       let val exp1 = print_exp (List.nth(args, 0))
           val ty_str = print_type (List.nth(args, 1))
       in "low:"^ty_str^"("^exp1 ^ ")" end
    else if ope = ``Cast`` then
       let val exp1 = print_exp (List.nth(args, 0))
           val ty_str = print_type (List.nth(args, 1))
       in "pad:"^ty_str^"("^exp1 ^ ")" end
    else if ope = ``SignedCast`` then
       let val exp1 = print_exp (List.nth(args, 0))
           val ty_str = print_type (List.nth(args, 1))
       in "extend:"^ty_str^"("^exp1 ^ ")" end
    else if ope = ``Load`` then
       let val exp1 = print_exp (List.nth(args, 0))
           val exp2 = print_exp (List.nth(args, 1))
           val ty = List.nth(args, 3)
       in if ty = ``Bit64`` then "(("^exp1 ^ ")[" ^ exp2 ^ ", e_little]:u64)"
          else if ty = ``Bit32`` then "(("^exp1 ^ ")[" ^ exp2 ^ ", e_little]:u32)"
          else if ty = ``Bit16`` then "(("^exp1 ^ ")[" ^ exp2 ^ ", e_little]:u16)"
          else "ERROR"
       end
    else if ope = ``Store`` then
       let val exp1 = print_exp (List.nth(args, 0))
           val exp2 = print_exp (List.nth(args, 1))
           val exp3 = print_exp (List.nth(args, 2))
           val ty = List.nth(args, 4)
       in if ty = ``Bit64`` then "("^exp1 ^ ") with [" ^ exp2 ^ ", e_little]:u64 = " ^ exp3
          else if ty = ``Bit32`` then "("^exp1 ^ ") with [" ^ exp2 ^ ", e_little]:u32 = " ^ exp3
          else if ty = ``Bit16`` then "("^exp1 ^ ") with [" ^ exp2 ^ ", e_little]:u16 = " ^ exp3
          else "ERROR"
       end
    else if ope = ``IfThenElse`` then
       let val exp1 = print_exp (List.nth(args, 0))
           val exp2 = print_exp (List.nth(args, 1))
           val exp3 = print_exp (List.nth(args, 2))
       in "if (" ^exp1^") then ("^exp2^") else (" ^exp3^")"
       end
    else "ERROR"
end;

fun print_statement statement =
let val (inst,args) = strip_comb statement
in
  if inst = ``Assign`` then
     let val exp = (List.nth(args,1))
         val exp_str = print_exp exp
         val var_name = (List.nth(args,0))
         val var_type = get_var_type var_name
         val var_type_str = print_type var_type
     in "V_" ^ (stringSyntax.fromHOLstring var_name) ^ ":" ^ var_type_str ^ "=" ^exp_str ^ "\n" end
  else if inst = ``Jmp`` then
     let val exp = (List.nth(args,0))
         val exp_str = print_exp exp
     in "jmp " ^exp_str ^ "\n" end
  else if inst = ``CJmp`` then
     let val exp1 = (List.nth(args,0))
         val exp2 = (List.nth(args,1))
         val exp3 = (List.nth(args,2))
         val exp1_str = print_exp exp1
         val exp2_str = print_exp exp2
         val exp3_str = print_exp exp3
     in "cjmp " ^exp1_str ^ ", " ^ exp2_str ^ ", " ^ exp3_str^ "\n" end
  else if inst = ``Assert`` then
     let val exp = (List.nth(args,0))
         val exp_str = print_exp exp
     in "assert " ^exp_str ^ "\n" end
  else "ERROR\n"
end;

fun print_block block =
let
    val instrs = block;
    val (_, [("label", lbl),  ("statements", sts)]) = TypeBase.dest_record instrs;
    val (sts1, _) = listSyntax.dest_list sts;
    val (_, pc) = dest_comb lbl;
    val pc_str = (print_exp ``Const ^pc``)
    val pc_str = "addr " ^ (String.substring(pc_str, 0, String.size(pc_str) -4)) ^ "\n";
    val frag_str =  "\n" ^ (String.concat (pc_str::(List.map print_statement sts1))) ^ "\n";
in frag_str end;




(* export to BAP format: then using the helper functions *)
(* ---------------------- *)
val bapinput_content = List.foldr (fn (x, y) => (print_block x) ^ y) "" ((fst o listSyntax.dest_list o snd o dest_eq o concl) aesCodeTheory.aes_bil_program_def);

val fd = TextIO.openOut "aes.bil";
val _ = TextIO.output (fd, bapinput_content) handle e => (TextIO.closeOut fd; raise e);
val _ = TextIO.closeOut fd;

