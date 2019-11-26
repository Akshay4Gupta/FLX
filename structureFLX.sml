use "signatureFLX.sml";
structure Flx : FLX = 
struct
exception Not_wellformed
exception Not_nf
exception Not_int
(*1) fromInt(toInt(fromString("(S (S Z))")));
2) toInt(fromInt(5));
3) toInt(fromInt(~5));
4) toInt(fromInt(0));
5) fromString(toString(ITE (ITE (T,F,T),ITE (F,F,T),ITE (F,F,F))))*)
datatype term = VAR of string (* variable *)
                  | Z           (* zero *)
                  | T           (* true *)
                  | F           (* false *)
                  | P of term   (* Predecessor *)
                  | S of term   (* Successor *)
                  | ITE of term * term * term   (* If then else *)
                  | IZ of term  (* is zero *)
                  | GTZ of term (* is greater than zero *)
local
	fun checkOtherConstructor z = (case z of 
									Z => F
									| S z' => checkOtherConstructor z'
									| P z' => checkOtherConstructor z'
									| ITE(T,Z,x) => F
									| ITE(F,x,Z) => F
									| _ => T
									)
in
	fun normalize Z = Z
	|	normalize T = T
	|	normalize F = F
	|	normalize (VAR x)  = (VAR x) 
	|	normalize (S p) =
						let val nfp = normalize p
						in (case nfp of
							Z => S Z
							|	S nfp' => S nfp
							|	P nfp' => nfp'
							|	_ => S nfp
							)
						end
	|	normalize (P p) =
						let val nfp = normalize p
						in (case nfp of
						Z => P Z
						|	S nfp' => nfp'
						|	P nfp' => P nfp
						|	_ => P nfp
						)
						end
	|	normalize (ITE(c, x, y)) = let
										val c' = normalize(c)
										val x' = normalize(x)
										val y' = normalize(y)
									in
									(case c' of
									  T => x'
									| F => y'
									| _ => if(x' = y') then x' else ITE(c',x',y')
									)
									end
	|	normalize (IZ(x)) = let
								val z = normalize(x)
								val check = checkOtherConstructor(z)
							in
								( case z of 
								Z => T
								| _ => if(check = T) then IZ(z) else F
								)
							end
	|	normalize (GTZ(x)) = let
								val z = normalize(x)
								val check = checkOtherConstructor(z)
							in 
								if(check = T) then GTZ(z) else (case z of 
															S z' => T
															| _ => F)
							end
end;
(* normalize ITE(T,VAR x,VAR y)*)

local
	fun checkOtherConstructor z = (case z of 
									Z => T
									| S z' => checkOtherConstructor z'
									| P z' => checkOtherConstructor z'
									| _ => F
									)
	fun solveS x =  (case x of
					Z => 0
					| S x' => (solveS x') + 1
					| P x' => raise Not_nf
					| _ => raise Not_nf
					)
	fun solveP x = (case x of
					Z => 0
					| P x' => (solveP x') - 1
					| S x' => raise Not_nf
					| _ => raise Not_nf
					)
in
	fun toInt x = let
					val check = checkOtherConstructor(x)
					in
					if(check = F) then raise Not_int
					else
					(case x of
					Z => 0
					| S x' => solveS x
					| P x' => solveP x
					| _ => raise Not_nf
					)
					end
end;

fun fromInt i = if i = 0 then Z
				else if i > 0 then (S (fromInt (i-1)))
				else (P (fromInt (i+1)));

fun toString (t) = (case t of
					VAR x => x
					| Z => "Z"
					| T => "T"
					| F => "F"
					| P x => "(P "^toString(x)^")"
					| S x => "(S "^toString(x)^")"
					| IZ x => "(IZ "^toString(x)^")"
					| GTZ x => "(GTZ "^toString(x)^")"
					| ITE(c,x,y) => "(ITE <"^toString(c)^","^toString(x)^","^toString(y)^">)"
					);
local
	fun returnX([],l) = ([],l)
	|	returnX(h::t, l) = if(Char.isAlpha(h)) then let val (x,l1) = returnX(t,l) in (h::x, l1) end else ([],h::t);

	fun tokenGenerator ([]) = []
	| tokenGenerator (h::t) = (case h of 
								#" " => tokenGenerator(t)
							   | #"(" => str(h)::(tokenGenerator(t))
							   | #")" => str(h)::(tokenGenerator(t))
							   | #"<" => str(h)::(tokenGenerator(t))
							   | #">" => str(h)::(tokenGenerator(t))
							   | #"," => str(h)::(tokenGenerator(t))
							   | #"T" => if not(Char.isAlpha(hd(t))) then str(h)::(tokenGenerator(t)) else let val (x,l1) = returnX(h::t, []) in (implode(x))::tokenGenerator(l1) end
							   | #"F" => if not(Char.isAlpha(hd(t))) then str(h)::(tokenGenerator(t)) else let val (x,l1) = returnX(h::t, []) in (implode(x))::tokenGenerator(l1) end
							   | #"Z" => if not(Char.isAlpha(hd(t))) then str(h)::(tokenGenerator(t)) else let val (x,l1) = returnX(h::t, []) in (implode(x))::tokenGenerator(l1) end
							   | #"P" => if((length(t) >= 2) andalso (hd(t) = #" ")) then str(h)::(tokenGenerator(tl(t))) else let val (x,l1) = returnX(h::t, []) in (implode(x))::tokenGenerator(l1) end
							   | #"S" => if((length(t) >= 2) andalso (hd(t) = #" ")) then str(h)::(tokenGenerator(tl(t))) else let val (x,l1) = returnX(h::t, []) in (implode(x))::tokenGenerator(l1) end
							   | #"G" => if((length(t) >= 4) andalso (hd(t) = #"T") andalso (hd(tl(t)) = #"Z") andalso (hd(tl(tl(t))) = #" ")) then "GTZ"::(tokenGenerator(tl(tl(tl(t))))) else let val (x,l1) = returnX(h::t, []) in (implode(x))::tokenGenerator(l1) end 
							   | #"I" => if((length(t) >= 3) andalso (hd(t) = #"Z") andalso (hd(tl(t)) = #" "))
											then "IZ"::(tokenGenerator(tl(tl(t))))
										else if ((length(t) >= 4) andalso (hd(t) = #"T") andalso (hd(tl(t)) = #"E") andalso (hd(tl(tl(t))) = #" "))
											then "ITE"::(tokenGenerator(tl(tl(tl(t)))))
										else let val (x,l1) = returnX(h::t, []) in (implode(x))::tokenGenerator(l1) end
							   | _ => let val (x,l1) = returnX(h::t,[]) in implode(x)::tokenGenerator(l1) end
								)

	(*var String is not defined*)

	fun giveMeTermFn(x) = (case x of
							"P" => P
							| "S" => S
							| "IZ" => IZ
							| "GTZ" => GTZ
							| _	=> raise Not_wellformed
						)

	fun HaiLower [] = true
	|	HaiLower(h::t) = if(Char.isLower(h)) then HaiLower(t) else raise Not_wellformed;

	fun giveMeTerm(x) = (case x of
							"T" => T
							| "F" => F
							| "Z" => Z
							| _ => if(HaiLower(explode(x))) then VAR x else raise Not_wellformed
						)

	fun termFrom(s, inter) = let
								val t = hd(s)
								val x = if(tl(s) <> nil) then hd(tl(s)) else raise Not_wellformed
							  in
								if(x <> "(") then
									if (x = "P" orelse x = "S" orelse x = "GTZ" orelse x = "IZ") then
										if(tl(tl(s)) <> nil andalso hd(tl(tl(s))) = "(") then (tl(tl(tl(s))),SOME(giveMeTermFn(x) (giveMeTerm(t))))(**)
										else raise Not_wellformed
									else raise Not_wellformed
								else if (inter = NONE) then (tl(tl(s)),SOME (giveMeTerm(t))) else (tl(tl(s)),SOME(giveMeTermFn(t) (valOf(inter))))(**)
							  end;


	fun translate(s, inter:term option, x) = if (s = nil andalso x = nil) then (inter,x)
								else if(s <> nil andalso x = nil) then (*(inter,x)*)raise Not_wellformed
								else if(length(x) >=3 andalso hd(x) = "ITE" andalso hd(tl(x)) = "<") then let
																											val n = if(length(s)>=1 andalso hd(s) = "(") then 5 else raise Not_wellformed
																											val a = if(tl(tl(x)) <> nil) then translate([]:string list, NONE:term option,tl(tl(x))) else raise Not_wellformed
																											val b = if(hd(#2(a)) = "," andalso tl(#2(a)) <> nil) then translate([]:string list, NONE:term option,tl(#2(a))) else raise Not_wellformed
																											val c = if(hd(#2(b)) = "," andalso tl(#2(b)) <> nil) then translate([]:string list, NONE:term option,tl(#2(b))) else raise Not_wellformed
																										  in
																											if(hd(#2(c)) = ">" andalso tl(#2(c)) <> nil(* andalso inter = NONE*) andalso hd(tl(#2(c))) = ")")then translate(tl(s), (SOME(ITE(valOf(#1(a)),valOf(#1(b)),valOf(#1(c))))),tl(tl(#2(c)))) else raise Not_wellformed
																										  end
								else if(hd(x) = ",") then  if(s = nil andalso x <> nil) then (inter,x) else raise Not_wellformed
								else if(hd(x) = ">") then  if(s = nil andalso x <> nil) then (inter,x) else raise Not_wellformed
								else if(hd(x) = "(") then translate(hd(x)::s,inter,tl(x))
								 else if(s <> nil andalso hd(x) = ")") then let val (leftOverS, t) = termFrom(s,inter) in translate(leftOverS, t, tl(x)) end
								 else if(s <> nil andalso x = nil) then raise Not_wellformed
								 (*else if(hd(x) = "T") then if(inter = NONE) then (SOME T,tl(x)) else raise Not_wellformed
								 else if(hd(x) = "F") then if(inter = NONE) then (SOME F,tl(x)) else raise Not_wellformed
								 else if(hd(x) = "Z") then if(inter = NONE) then (SOME Z,tl(x)) else raise Not_wellformed*)
								 (*else if (s = nil andalso x <> nil) then raise Not_wellformed*)
								else translate(hd(x)::s,inter,tl(x))

	fun ad(h::t, x) = if(h = "<" andalso length(t)>=1 andalso hd(t) <> "(") then  h::"("::ad(t,1)
					  else if(h = "," andalso length(t)>=1 andalso hd(t) <> "(") then if(x = 1) then ")"::h::"("::ad(t,1) else h::"("::ad(t,1)
					  else if(h = "," andalso length(t)>=1 andalso hd(t) = "(") then if(x = 1) then ")"::h::ad(t,0) else h::ad(t,0) 
					  else if(h = "<" andalso length(t)>=1 andalso hd(t) = "(") then h::ad(t,0)
					  else if(h = ">") then if(x = 1) then ")"::h::ad(t,0) else h::ad(t,0)
					  else h::ad(t,x)
	|	ad([],x) = if(x = 1) then [")"] else [];
in

	fun fromString "Z" = Z
	|	fromString "T" = T
	|	fromString "F" = F
	|	fromString "" = raise Not_wellformed
	|	fromString x = let
							val x1 = if(String.isPrefix "(" x) then x else ("("^x^")") 
							val x' = explode(x1)
							
							val tokens = ad(tokenGenerator(x'), 0)
							
							val result = (translate([], NONE:term option, tokens))
						in
						if(#2(result) <> nil) then raise Not_wellformed else valOf(#1(result))
						end;
end;
end;