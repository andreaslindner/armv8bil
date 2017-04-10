val Tarm = ``!s . P(s:bool) ==>
   ?n:num. (!s'. (s'= execA(s,n)) ==>
   Q(s, s':bool))``;


(* WP + SMT *)
val Tbil = ``!sbil:bool . Pbil(sbil:bool) ==>
   !n1:num. (!sbil'. (sbil'= execB(sbil,n1)) ==>
   (haltingPoint(sbil')) ==>
   ((Qbil(sbil, sbil':bool)) /\ (~(error sbil')) /\ (startLabel sbil')))``;

(* LOOP FREEDOM *)
val Tbil = ``!sbil:bool . Pbil(sbil:bool) ==>
   ?n1:num. (!sbil'. (sbil'= execB(sbil,n1)) ==>
   (haltingPoint(sbil'))``;

val Tbil = ``!sbil:bool . Pbil(sbil:bool) ==>
   ?n1:num. (!sbil'. (sbil'= execB(sbil,n1)) ==>
   ((Qbil(sbil, sbil':bool)) /\ (~(error sbil')) /\ (startLabel sbil')))``;




val Tsim = ``!s:bool .? sbil:bool . sim s sbil``;
    
val Tlifter = ``!s:bool sbil:bool.
 (sim s sbil) ==>
 !n':num sbil':bool.
  ((sbil' = execB(sbil, n')) /\
   (startLabel sbil') /\
   (~(error sbil'))) ==>
 (?n:num. !s':bool .
  (s' = execA(s, n)) ==>
   (sim s' sbil'))``;

val Psim = ``!s:bool sbil:bool. (sim s sbil) ==> (P s) ==> (Pbil sbil)``;

val Qsim = ``!s:bool s':bool sbil:bool sbil':bool. (sim s sbil) ==> (sim s' sbil') ==> (Qbil(sbil,sbil')) ==> (Q(s,s'))``;


    ``^Tlifter ==> ^Tsim ==> ^Tbil ==> ^Psim ==> ^Qsim ==> ^Tarm``
	(RW_TAC (srw_ss()) []) THEN
	    (PAT_X_ASSUM ``∀s. ∃sbil. sim s sbil`` (fn thm =>
      CHOOSE_TAC (SPECL [``s:bool``] thm))) THEN
	    (PAT_X_ASSUM ``∀s sbil. sim s sbil ⇒ P s ⇒ Pbil sbil`` (fn thm =>
      ASSUME_TAC (SPECL [``s:bool``, ``sbil:bool``] thm))) THEN
      (REV_FULL_SIMP_TAC (srw_ss()) []) THEN
      (PAT_X_ASSUM ``∀sbil. Pbil sbil ==> a`` (fn thm =>
      ASSUME_TAC (SPECL [``sbil:bool``] thm))) THEN
      (REV_FULL_SIMP_TAC (srw_ss()) []) THEN
      
      (PAT_X_ASSUM ``∀s sbil.
        sim s sbil ⇒
        ∀n'.
          startLabel (execB (sbil,n')) ∧ ¬error (execB (sbil,n')) ⇒
          ∃n. sim (execA (s,n)) (execB (sbil,n'))`` (fn thm =>
      ASSUME_TAC (SPECL [``s:bool``, ``sbil:bool``] thm))) THEN
      (REV_FULL_SIMP_TAC (srw_ss()) []) THEN

      (PAT_X_ASSUM ``!n:num.p`` (fn thm=> ASSUME_TAC (SPEC ``n1:num`` thm))) THEN
      (REV_FULL_SIMP_TAC (srw_ss()) []) THEN

      (EXISTS_TAC ``n:num``) THEN
      (PAT_X_ASSUM ``!s.P`` (fn thm=>
         (ASSUME_TAC (SPECL [``s:bool``, ``(execA (s:bool,n:num)):bool``,
			     ``sbil:bool``, ``(execB (sbil:bool,n1:num)):bool``] thm)))) THEN
      (REV_FULL_SIMP_TAC (srw_ss()) [])



val Tarm = ``!s . P(s:bool) ==>
   !n:num. (!s'. (s'= execA(s,n)) ==>
   Q(s, s':bool))``;


val Tbil = ``!sbil:bool . Pbil(sbil:bool) ==>
   !n1:num. (!sbil'. (sbil'= execB(sbil,n1)) ==>
   ((Qbil(sbil, sbil':bool)) /\ (~(error sbil'))))``;

val Tsim = ``!s:bool .? sbil:bool . sim s sbil``;
    
val Tlifter = ``!s:bool sbil:bool.
 (sim s sbil) ==>
 !n:num s':bool.
 (s' = execA(s, n)) ==>
 (?n':num. !sbil':bool .
   (sbil' = execB(sbil, n')) ==>
   ((error sbil') \/ (sim s' sbil')))
				 ``;

val Psim = ``!s:bool sbil:bool. (sim s sbil) ==> (P s) ==> (Pbil sbil)``;

val Qsim = ``!s:bool s':bool sbil:bool sbil':bool. (sim s sbil) ==> (sim s' sbil') ==> (Qbil(sbil,sbil')) ==> (Q(s,s'))``;

    ``^Tlifter ==> ^Tsim ==> ^Tbil ==> ^Psim ==> ^Qsim ==> ^Tarm``
	(RW_TAC (srw_ss()) []) THEN
	    (PAT_X_ASSUM ``∀s. ∃sbil. sim s sbil`` (fn thm =>
      CHOOSE_TAC (SPECL [``s:bool``] thm))) THEN
	    (PAT_X_ASSUM ``∀s sbil. sim s sbil ⇒ P s ⇒ Pbil sbil`` (fn thm =>
      ASSUME_TAC (SPECL [``s:bool``, ``sbil:bool``] thm))) THEN
      (REV_FULL_SIMP_TAC (srw_ss()) []) THEN
      (PAT_X_ASSUM ``∀sbil.
        Pbil sbil ⇒ !n1. Qbil (execB (sbil,n1)) /\ q`` (fn thm =>
      ASSUME_TAC (SPECL [``sbil:bool``] thm))) THEN
      (REV_FULL_SIMP_TAC (srw_ss()) []) THEN
      
      (PAT_X_ASSUM ``∀s sbil.
        sim s sbil ⇒
        ∀n.
          ∃n'.
            error (execB (sbil,n')) ∨
            sim (execA (s,n)) (execB (sbil,n'))`` (fn thm =>
      ASSUME_TAC (SPECL [``s:bool``, ``sbil:bool``] thm))) THEN
      (REV_FULL_SIMP_TAC (srw_ss()) []) THEN

      (PAT_X_ASSUM ``!n:num.?n1.P`` (fn thm=>
         (CHOOSE_TAC (SPEC ``n:num`` thm)))) THEN

      (PAT_X_ASSUM ``!n1:num.P`` (fn thm=>
         (ASSUME_TAC (SPECL [``n':num``] thm)))) THEN
      (FULL_SIMP_TAC (srw_ss()) []) THEN

      (PAT_X_ASSUM ``!s.P`` (fn thm=>
         (ASSUME_TAC (SPECL [``s:bool``, ``(execA (s:bool,n:num)):bool``,
			     ``sbil:bool``, ``(execB (sbil:bool,n':num)):bool``] thm)))) THEN
      (REV_FULL_SIMP_TAC (srw_ss()) [])
