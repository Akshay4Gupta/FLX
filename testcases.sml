use "signatureLAMBDAFLX.sml";
use "structureLAMBDAFLX.sml";
open LambdaFlx;


(* isWellTyped(P (ITE (LAMBDA (VAR "x",IZ (S T)),Z,Z))) = false;																			(* false *)
isWellTyped(P (APP (LAMBDA (VAR "x",ITE(T,S (VAR "x"),Z)),T))) = false;                                  								(* false *)
isWellTyped(P (APP (LAMBDA (VAR "x",ITE(T,S (VAR "x"),Z)),Z))) = true;                                  								(* true *) *)
isWellTyped(IZ (ITE (LAMBDA (VAR "x",IZ (VAR "x")),S (P Z),Z))) = false;                                 								(* false *)
isWellTyped(APP (LAMBDA (VAR "y",ITE (LAMBDA (VAR "x",IZ (VAR "x")),S (P Z),Z)),T)) = false;             								(* false *)
(* isWellTyped(APP (LAMBDA (VAR "y",ITE (LAMBDA (VAR "x",IZ (VAR "x")),S (P (VAR "y")),Z)),T)) = false;									(* false *)
isWellTyped(LAMBDA (VAR "x",ITE(IZ (P(S (VAR "x"))),IZ Z,T))) = true;																	(* true *)
isWellTyped(APP(LAMBDA (VAR "x",ITE(IZ (P(S (VAR "x"))),IZ Z,T)),IZ Z)) = false;														(* false *)
isWellTyped(ITE(VAR "x", (APP (LAMBDA (VAR "y", LAMBDA(VAR "x", GTZ(S (P (S (S (VAR "y"))))))), F)), F)) = false;						(* false *) *)
(* isWellTyped(APP(APP(LAMBDA(VAR "x", LAMBDA(VAR"y",APP(VAR "x", VAR "y"))),LAMBDA(VAR "x", VAR"x")),LAMBDA(VAR "x",Z))) = true;			(* true *) *)
(* isWellTyped(P (ITE (LAMBDA (VAR "x",IZ (S T)),Z,Z))) = false;                                          									(* false *)
isWellTyped(P (APP (LAMBDA (VAR "x",ITE(T,S (VAR "x"),Z)),T))) = false;                                 								(* false *)
isWellTyped(P (APP (LAMBDA (VAR "x",ITE(T,S (VAR "x"),Z)),Z))) = true;																	(* true *) *)
isWellTyped(IZ (ITE (LAMBDA (VAR "x",IZ (VAR "x")),S (P Z),Z))) = false;                               									(* false *)
isWellTyped(APP (LAMBDA (VAR "y",ITE (LAMBDA (VAR "x",IZ (VAR "x")),S (P Z),Z)),T)) = false;             								(* false *)
(* isWellTyped(APP (LAMBDA (VAR "y",ITE (LAMBDA (VAR "x",IZ (VAR "x")),S (P (VAR "y")),Z)),T)) = false;     								(* false *)
isWellTyped(LAMBDA (VAR "x",ITE(IZ (P(S (VAR "x"))),IZ Z,T))) = true;                                   								(* true *)
isWellTyped(APP(LAMBDA (VAR "x",ITE(IZ (P(S (VAR "x"))),IZ Z,T)),IZ Z)) = false;                         								(* false *)
isWellTyped(APP(LAMBDA (VAR "x",ITE(IZ (P(S (VAR "x"))),IZ Z,T)),P (S Z))) = true;                      								(* true *)
isWellTyped(APP(LAMBDA (VAR "x",ITE(IZ (P(S (VAR "x"))),IZ Z,T)),ITE(T,P (S Z),T))) = false;             								(* false *)
isWellTyped(APP(LAMBDA (VAR "x",ITE(VAR "x",IZ Z,T)),ITE(T,P (S Z),T))) = false;                         								(* false *) *)
isWellTyped(APP(APP(LAMBDA(VAR "x",LAMBDA(VAR "y",ITE(T,VAR "x",VAR "y"))),T),Z)) = false;               								(* FALSE *)
(* isWellTyped(APP(LAMBDA(VAR "x",LAMBDA(VAR "y",ITE(T,VAR "x",VAR "y"))),T)) = true;                      								(* true *)
isWellTyped(APP(VAR "y",VAR "y")) = false;                                                               								(* false *)
isWellTyped(APP(LAMBDA(VAR "x",ITE(T,VAR "y",F)),ITE(T,VAR "y",Z))) = false;                             								(* false *)
isWellTyped(APP(LAMBDA(VAR "x",ITE(VAR "y",VAR "y",VAR "x")),T)) = true;                                								(* true *)
isWellTyped(APP(LAMBDA(VAR "x",ITE(VAR "y",VAR "y",VAR "x")),Z)) = false;                                								(* false *)
isWellTyped(APP(LAMBDA(VAR "x",LAMBDA(VAR "y",APP(VAR "y",VAR "y"))),LAMBDA(VAR "x",LAMBDA(VAR "y",APP(VAR "x",VAR "y"))))) = false; 	(* false *)

isWellTyped(ITE(T,APP (LAMBDA (VAR "x",VAR "x"),Z),APP (LAMBDA (VAR "x",VAR "x"),Z))) = true; (* true *)

isWellTyped(ITE (T, ITE (T, VAR "x", T), ITE(T, VAR "x",Z))) = false; (* false *)

isWellTyped(LAMBDA (VAR "x",ITE (T, VAR "x", Z))) = true; (* true *)

isWellTyped(APP(T,T)) = false;  (* false *)

isWellTyped(APP(LAMBDA(VAR "x", ITE(T, VAR "y", F)), ITE(T, VAR "y", Z))) = false; (* false *)

isWellTyped(ITE(T, ITE(F, VAR "p", F),ITE(T, S(P(Z)), VAR "p"))) = false; (* false *)

isWellTyped(ITE(T, ITE(F, VAR "p", Z),ITE(T, S(P(Z)), VAR "p"))) = true; (* true *)

isWellTyped(ITE(F, ITE(T, ITE(F, VAR "y", VAR "x"),ITE(T, S(P(Z)), VAR "p")), ITE(T, VAR "x", T))) = false; (* false *)

isWellTyped(ITE(F, ITE(T, ITE(F, VAR "y", VAR "x"),ITE(T, S(P(Z)), VAR "p")), ITE(T, VAR "x", Z))) = true; (* true *)

isWellTyped(ITE(F, ITE(T, ITE(F, VAR "y", VAR "x"), ITE(VAR "k", S(P(Z)), VAR "p")), ITE(T, VAR "x", Z))) = true; (* true *)

isWellTyped(fromString("((LAMBDA x[LAMBDA y[y]] i) j)")) = true; (* true *) *)


(* FOR BETANF *)
(*
betanf(P (APP (LAMBDA (VAR "x",ITE(T,S (VAR "x"),Z)),Z)));
betanf(LAMBDA (VAR "x",ITE(IZ (P(S (VAR "x"))),IZ Z,T)));																	(* true *)
betanf(APP(APP(LAMBDA(VAR "x", LAMBDA(VAR"y",APP(VAR "x", VAR "y"))),LAMBDA(VAR "x", VAR"x")),LAMBDA(VAR "x",Z)));			(* true *)
betanf(P (APP (LAMBDA (VAR "x",ITE(T,S (VAR "x"),Z)),Z)));																	(* true *)
betanf(LAMBDA (VAR "x",ITE(IZ (P(S (VAR "x"))),IZ Z,T)));                                   								(* true *)
betanf(APP(LAMBDA (VAR "x",ITE(IZ (P(S (VAR "x"))),IZ Z,T)),P (S Z)));                      								(* true *)
betanf(APP(LAMBDA(VAR "x",LAMBDA(VAR "y",ITE(T,VAR "x",VAR "y"))),T));                      								(* true *)
betanf(APP(LAMBDA(VAR "x",ITE(VAR "y",VAR "y",VAR "x")),T));                                								(* true *)
betanf(ITE(T,APP (LAMBDA (VAR "x",VAR "x"),Z),APP (LAMBDA (VAR "x",VAR "x"),Z))); 											(* true *)
betanf(LAMBDA (VAR "x",ITE (T, VAR "x", Z))); 																				(* true *)
betanf(ITE(T, ITE(F, VAR "p", Z),ITE(T, S(P(Z)), VAR "p"))); 																(* true *)
betanf(ITE(F, ITE(T, ITE(F, VAR "y", VAR "x"),ITE(T, S(P(Z)), VAR "p")), ITE(T, VAR "x", Z))); 								(* true *)
betanf(ITE(F, ITE(T, ITE(F, VAR "y", VAR "x"), ITE(VAR "k", S(P(Z)), VAR "p")), ITE(T, VAR "x", Z))); 						(* true *)
betanf(fromString("((LAMBDA x[LAMBDA y[y]] i) j)")); 																		(* true *) *)
