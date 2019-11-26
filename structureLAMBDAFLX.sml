use "signatureLAMBDAFLX.sml";
structure LambdaFlx : LAMBDAFLX =
struct
exception Not_wellformed
exception Not_nf
exception Not_int
exception Not_welltyped

datatype lterm = term (* term from FLX *)
			   | VAR of string      (* variables *)
			   | Z                  (* zero *)
			   | T                  (* true *)
			   | F                  (* false *)
			   | P of lterm         (* Predecessor *)
			   | S of lterm         (* Successor *)
			   | ITE of lterm * lterm * lterm       (* If then else *)
			   | IZ of lterm        (* is zero *)
			   | GTZ of lterm       (* is greater than zero *)
			   | LAMBDA of lterm * lterm    (* lambda x [lterm] *)
			   | APP of lterm * lterm       (* application of lambda terms, i.e. (L M) *)


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
(*---------------------------------------------Doubt regarding variable name---------------------------------------------------*)
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
					| LAMBDA(x, y) => "LAMBDA "^toString(x)^"["^toString(y)^"]"
					| APP(x, y) => "("^toString(x)^" "^toString(y)^")"
					);
(*--------------------------------------------------------------------------------------*)
local
	fun returnX([],l) = ([],l)
	|	returnX(h::t, l) = if(Char.isAlpha(h)) then let val (x,l1) = returnX(t,l) in (h::x, l1) end else ([],h::t);

	fun tokenGenerator ([]) = []
	| tokenGenerator (h::t) = (case h of
								#" " => tokenGenerator(t)
							   | #"(" => str(h)::(tokenGenerator(t))
							   | #")" => str(h)::(tokenGenerator(t))
							   | #"[" => str(h)::(tokenGenerator(t))
							   | #"]" => str(h)::(tokenGenerator(t))
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
							   | #"L" => if(length(t) >= 6 andalso hd(t) = #"M" andalso hd(tl(t)) = #"B" andalso hd(tl(tl(t))) = #"D" andalso hd(tl(tl(tl(t)))) = #"A" andalso hd(tl(tl(tl(tl(t))))) = #" ")
							    			then "LAMBDA"::(tokenGenerator(tl(tl(tl(tl(tl(t)))))))
										else let val (x,l1) = returnX(h::t, []) in (implode(x))::tokenGenerator(l1) end
							   | _ => let val (x,l1) = returnX(h::t,[]) in "("::implode(x)::")"::tokenGenerator(l1) end
								)

	(*var String is not defined*)


	fun HaiLower [] = true
	|	HaiLower(h::t) = if(Char.isLower(h)) then HaiLower(t) else raise Not_wellformed;

	fun giveMeTermFn(x) = (case x of
							"P" => (SOME P, true)
							| "S" => (SOME S, true)
							| "IZ" => (SOME IZ, true)
							| "GTZ" => (SOME GTZ, true)
							| _	=>  (NONE, false)
						)

	fun giveMeTerm(x) = (case x of
							"T" => T
							| "F" => F
							| "Z" => Z
							| _ => if(HaiLower(explode(x))) then VAR x else raise Not_wellformed
						)

	fun termFrom(s, inter:lterm list) = let
								val x = hd(s)
							  in
								if(x <> "(") then
									if(tl(s) <> nil andalso hd(tl(s)) = "(") then
										let
											val c = giveMeTermFn(x)
										in
											if (#2(c)) then
												(tl(tl(s)),(valOf(#1(c))(hd(inter))), tl(inter))
											else (tl(tl(s)),giveMeTerm(x), inter)
										end
									else raise Not_wellformed
								else
									(tl(s), APP(hd(tl(inter)),hd(inter)), tl(tl(inter)))
							  end;



	fun isVar(v) = case v of
						VAR _ => true
					|	_	=>	false;


	fun takeOutVar(x) = let
							val r = if(length(x) >= 3 andalso hd(x) = "(" andalso hd(tl(tl(x))) = ")") then giveMeTerm(hd(tl(x))) else raise Not_wellformed
						in
							if(isVar(r)) then (r,tl(tl(tl(x)))) else raise Not_wellformed
						end;

	fun translate(s, inter:lterm list, x) = if(s = nil andalso x = nil) then (inter, x)
											else if(s <> nil andalso x = nil) then raise Not_welltyped
											else if(hd(x) = "LAMBDA") then
												 let
												   val a = if(tl(x) <> nil) then let val r = takeOutVar(tl(x)) in (#1(r)::inter,#2(r)) end else raise Not_wellformed
												   val b = if(hd(#2(a)) = "[" andalso tl(#2(a)) <> nil) then translate([]:string list, #1(a),tl(#2(a))) else raise Not_wellformed
												   val c = if (hd(#2(b)) = "]") then tl(#2(b)) else raise Not_wellformed
												 in
												   translate(s, (LAMBDA(hd(tl(#1(b))),hd(#1(b))))::(tl(tl(#1(b)))) ,c)
												 end
											else if(length(x) >=3 andalso hd(x) = "ITE" andalso hd(tl(x)) = "<") then
												let
												 val n = if(length(s)>=1 andalso hd(s) = "(") then 5 else raise Not_wellformed
												 val a = if(tl(tl(x)) <> nil) then translate([]:string list, inter,tl(tl(x))) else raise Not_wellformed
												 val b = if(hd(#2(a)) = "," andalso tl(#2(a)) <> nil) then translate([]:string list, #1(a),tl(#2(a))) else raise Not_wellformed
												 val c = if(hd(#2(b)) = "," andalso tl(#2(b)) <> nil) then translate([]:string list, #1(b),tl(#2(b))) else raise Not_wellformed
											 	in
												 if(hd(#2(c)) = ">" andalso tl(#2(c)) <> nil andalso hd(tl(#2(c))) = ")")then translate(tl(s), ((ITE((hd(tl(tl(#1(c))))),(hd(tl(#1(c)))),(hd(#1(c))))))::(tl(tl(tl(#1(c))))),tl(tl(#2(c)))) else raise Not_wellformed
											 	end
											else if(hd(x) = "[" orelse hd(x) = ">" orelse hd(x) = "," orelse hd(x) = "]") then  if(s = nil) then (inter,x) else raise Not_wellformed
											else if(hd(x) = "(") then translate(hd(x)::s,inter,tl(x))
											else if(s <> nil andalso hd(x) = ")") then let val (leftOverS, t, interm) = termFrom(s,inter) in translate(leftOverS, t::interm, tl(x)) end
											else if(s <> nil andalso x = nil) then raise Not_wellformed
											else translate(hd(x)::s,inter,tl(x));

	fun ad(h::t, x) = if(h = "<" andalso length(t)>=1 andalso hd(t) <> "(" andalso hd(t) <> "LAMBDA") then  h::"("::ad(t,1)
					  else if(h = "," andalso length(t)>=1 andalso hd(t) <> "(") then if(x = 1) then if(hd(t) <> "LAMBDA") then ")"::h::"("::ad(t,1) else ")"::h::ad(t,0) else if(hd(t) <> "LAMBDA") then h::"("::ad(t,1) else h::ad(t,0)
					  else if(h = "," andalso length(t)>=1 andalso hd(t) = "(") then if(x = 1) then ")"::h::ad(t,0) else h::ad(t,0)
					  else if(h = "<" andalso length(t)>=1 andalso hd(t) = "(") then h::ad(t,0)
					  else if(h = ">") then if(x = 1) then ")"::h::ad(t,0) else h::ad(t,0)
					  else h::ad(t,x)
	|	ad([],x) = if(x = 1) then [")"] else [];

	fun funda(h::t) = if(h = "LAMBDA" andalso length(t)>=1 andalso hd(t) <> "(" andalso hd(t) <> "LAMBDA") then  h::"("::funda(t)

					  else if(h <> ")" andalso h <> "]" andalso length(t)>=1 andalso hd(t) = "[") then h::")"::funda(t)
					  else if(h = "[" andalso length(t)>=1 andalso hd(t) <> "(" andalso hd(t) <> "LAMBDA") then h::"("::funda(t)
					  else if(h <> ")" andalso h <> "]" andalso length(t)>=1 andalso hd(t) = "]" ) then h::")"::funda(t)
					  else h::funda(t)
	|	funda([]) = [];


	fun change([]) = []
	|	change("("::"T"::")"::t) = "("::"T"::")"::change(t)
	|	change("("::"Z"::")"::t) = "("::"Z"::")"::change(t)
	|	change("("::"F"::")"::t) = "("::"F"::")"::change(t)
	|	change(h::t) = if(h = "T" orelse h = "F" orelse h = "Z") then ("(")::h::(")")::change(t) else h::change(t);
in
	fun fromString "Z" = Z
	|	fromString "T" = T
	|	fromString "F" = F
	|	fromString "" = raise Not_wellformed
	|	fromString x = let
							val x1 = if(String.isPrefix "(" x orelse String.isPrefix "LAMBDA" x) then x else ("("^x^")")
							val x' = explode(x1)
							val tokens = ad(tokenGenerator(x'), 0)
							val xtokens = change(tokens)
							val token = funda(xtokens)
							val result = (translate([], []:lterm list, token))
						in
							if(#2(result) <> nil) then raise Not_wellformed else (hd(#1(result)))
						end;
end;


fun HaiLower [] = true
|	HaiLower(h::t) = if(Char.isLower(h)) then HaiLower(t) else false;

fun isThere(x, []) = false
|	isThere(x, h::t) = if(x = h) then true else isThere(x, t)

fun reall(x, L) =  (case x of
 							S y => reall(y, L)
						|	P y => reall(y, L)
						|	T => true
						|	F => true
						|	Z => true
						|	IZ y => reall(y, L)
						|	GTZ y => reall(y, L)
						|	LAMBDA(a, b) => if(not(isThere(a, L))) then reall(b, a::L) else false
						|	ITE(a,b,c) => if(reall(a, L) andalso reall(b, L) andalso reall(x, L)) then true else false
						|	APP(a, b) => if(reall(a, L) andalso reall(b, L)) then true else false
						|	VAR y => if(HaiLower(explode(y))) then true else false
					);

fun varName(x, []) = ([(x, 0)], x^"0")
|	varName(x, h::t) = if(x = #1(h)) then ((x,#2(h)+1)::t, x^Int.toString(#2(h)+1)) else  let val c = varName(x, t) in (h::(#1(c)), #2(c))  end;

fun changeName(x, v, r) =  (case x of
							S y => (S (changeName(y, v, r)))
						|	P y => (P (changeName(y, v, r)))
						|	T => T
						|	F => F
						|	Z => Z
						|	IZ y => (IZ (changeName(y, v, r)))
						|	GTZ y => (GTZ (changeName(y, v, r)))
						|	LAMBDA(a, b) => LAMBDA(a, (changeName(b, v, r)))
						|	ITE(a,b,c) => ITE((changeName(a, v, r)),(changeName(b, v, r)),(changeName(c, v, r)))
						|	APP(a, b) => APP((changeName(a, v, r)),(changeName(b, v, r)))
						|	VAR y => if(y = v) then VAR r else VAR y
					);


fun getVar(x) = (case x of
						VAR Y => Y
				);

fun rename(x, L) =  (case x of
							S y => let val (t, l) = (rename(y, L)) in ((S t), l) end
						|	P y => let val (t, l) = (rename(y, L)) in ((P t), l) end
						|	T => (T, L)
						|	F => (F, L)
						|	Z => (Z, L)
						|	IZ y =>  let val (t, l) = (rename(y, L)) in ((IZ t), l) end
						|	GTZ y =>  let val (t, l) = (rename(y, L)) in ((GTZ t), l) end
						|	LAMBDA(a, b) => let
												val v = getVar(a)
												val (l, r) = varName(v,L)
												val k = (changeName(b, v, r))
												val (t, l1) = rename(k, l)
											in
												(LAMBDA(VAR r, t), l1)
											end
						|	ITE(a,b,c) =>  let val (t1, l1) = (rename(a, L)) val (t2, l2) = (rename(b, l1)) val (t3, l3) = (rename(c, l2)) in (ITE(t1,t2,t3), l3) end
						|	APP(a, b) => let val (t1, l1) = (rename(a, L)) val (t2, l2) = (rename(b, l1)) in (APP(t1,t2), l2) end
						|	VAR y => (VAR y, L)
					);

local
local
	fun varName(x, []) = ([(x, 0)], x^"0")
	|	varName(x, h::t) = if(x = #1(h)) then ((x,#2(h)+1)::t, x^Int.toString(#2(h)+1)) else  let val c = varName(x, t) in (h::(#1(c)), #2(c))  end;

	fun changeName(x, v, r) =  (case x of
								S y => (S (changeName(y, v, r)))
							|	P y => (P (changeName(y, v, r)))
							|	T => T
							|	F => F
							|	Z => Z
							|	IZ y => (IZ (changeName(y, v, r)))
							|	GTZ y => (GTZ (changeName(y, v, r)))
							|	LAMBDA(a, b) => LAMBDA(a, (changeName(b, v, r)))
							|	ITE(a,b,c) => ITE((changeName(a, v, r)),(changeName(b, v, r)),(changeName(c, v, r)))
							|	APP(a, b) => APP((changeName(a, v, r)),(changeName(b, v, r)))
							|	VAR y => if(y = v) then VAR r else VAR y
						);


	fun getVar(x) = (case x of
							VAR Y => Y
					);

	fun rename(x, L) =  (case x of
								S y => let val (t, l) = (rename(y, L)) in ((S t), l) end
							|	P y => let val (t, l) = (rename(y, L)) in ((P t), l) end
							|	T => (T, L)
							|	F => (F, L)
							|	Z => (Z, L)
							|	IZ y =>  let val (t, l) = (rename(y, L)) in ((IZ t), l) end
							|	GTZ y =>  let val (t, l) = (rename(y, L)) in ((GTZ t), l) end
							|	LAMBDA(a, b) => let
													val v = getVar(a)
													val (l, r) = varName(v,L)
													val k = (changeName(b, v, r))
													val (t, l1) = rename(k, l)
												in
													(LAMBDA(VAR r, t), l1)
												end
							|	ITE(a,b,c) =>  let val (t1, l1) = (rename(a, L)) val (t2, l2) = (rename(b, l1)) val (t3, l3) = (rename(c, l2)) in (ITE(t1,t2,t3), l3) end
							|	APP(a, b) => let val (t1, l1) = (rename(a, L)) val (t2, l2) = (rename(b, l1)) in (APP(t1,t2), l2) end
							|	VAR y => (VAR y, L)
						);

	fun checkOtherConstructor z = (case z of
									Z => F
									| S z' => checkOtherConstructor z'
									| P z' => checkOtherConstructor z'
									| ITE(T,Z,x) => F
									| ITE(F,x,Z) => F
									| _ => T
									)

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
									| _ => ITE(c',x',y')
									)
									end
	|	normalize (APP(x, y)) = let
										val x' = normalize(x)
										val y' = normalize(y)
									in
										APP(x',y')
									end
	|	normalize (LAMBDA(x, y)) = let
										val y' = normalize(y)
									in
										LAMBDA(x,y')
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

	fun replave(x, VAR v, r) =  (case x of
	 							S y => (S (replave(y, VAR v, r)))
							|	P y => (P (replave(y, VAR v, r)))
							|	T => T
							|	F => F
							|	Z => Z
							|	IZ y => (IZ (replave(y, VAR v, r)))
							|	GTZ y => (GTZ (replave(y, VAR v, r)))
							|	LAMBDA(a, b) => LAMBDA(a, (replave(b, VAR v, r)))
							|	ITE(a,b,c) => ITE((replave(a, VAR v, r)),(replave(b, VAR v, r)),(replave(c, VAR v, r)))
							|	APP(a, b) => APP((replave(a, VAR v, r)),(replave(b, VAR v, r)))
							|	VAR y => if(y = v) then r else VAR y
						);
in
	fun betanfmodified(t) =  let
						val x = normalize(t)
					in
						(case x of
	 							S y => let val y1 = normalize(y) val y2 = (betanfmodified(y1)) val y3 = normalize(S y2) in y3 end
							|	P y => let val y1 = normalize(y) val y2 = (betanfmodified(y1)) val y3 = normalize(P y2) in y3 end
							|	T => T
							|	F => F
							|	Z => Z
							|	IZ y =>  let val y1 = normalize(y) val y2 = (betanfmodified(y1)) val y3 = normalize(IZ y2) in y3 end
							|	GTZ y =>  let val y1 = normalize(y) val y2 = (betanfmodified(y1)) val y3 = normalize(GTZ y2) in y3 end
							|	ITE(a, b, c) => let
													val a1 = normalize(a)
													val a2 = betanfmodified(a1)
													val b1 = normalize(b)
													val b2 = betanfmodified(b1)
													val c1 = normalize(c)
													val c2 = betanfmodified(c1)
													val f = normalize(ITE(a2,b2,c2))
												in
													f
												end
							|	LAMBDA(a, b) => let
													val a1 = normalize(a)
													val a2 = betanfmodified(a1)
													val b1 = normalize(b)
													val b2 = betanfmodified(b1)
													val f = normalize(LAMBDA(a2, b2))
												in
													f
												end
							|	APP(a, b) => let
												val a1 = normalize(a)
												val a2 = betanfmodified(a1)
												val b1 = normalize(b)
												val b2 = betanfmodified(b1)
												val f = (case a2 of
															LAMBDA(m, n) => replave(n, m, b2)
															| 	_ => a2
														)
											 in
											 	normalize(f)
											 end
							|	VAR y => VAR y
							|	_	=> raise Not_wellformed
						)
					end
end;(*betanfmodified*)


val count = 2
val rc = ref count

fun bahr [] = []
| bahr (x::xs) = x::bahr(List.filter (fn y => y <> x) xs)

fun replaceType(toReplace, h::t, value) = if #2(h) = toReplace then (#1(h),value)::replaceType(toReplace,t,value)
                                      else h::replaceType(toReplace,t,value)
|   replaceType(toReplace,[],value) = []

fun changeList(toReplace,out,h::t,by) =  if #2(h)=toReplace then (changeList(toReplace,(#1(h),by)::out,t,by))
                                     else changeList(toReplace,h::out,t,by)
|   changeList(_,out,[],_) = bahr(out)

fun change(VAR x,h::t,present,L)  = if #1(h)=VAR x andalso present>1 then (true,#2(h),(VAR x,#2(h))::t)
                                 else if #1(h) = VAR x andalso present>(~1) andalso present<2 then
                                      let
                                          val temp = changeList(#2(h),[],L,present)
                                      in
                                        (true,present,temp)
                                      end
                                      else
                                        let
                                            val v = change(VAR x,t,present,L)
                                        in
                                            (#1(v),#2(v),h::(#3(v)))
                                        end
|   change(VAR x,[],present,L) = (true,present,[(VAR x,present)])


fun checkType(k,L,expected) = case k of
										T => (true,0,L)
   									|	F => (true,0,L)
   									|	Z => (true,1,L)
   									|	IZ term1 => if #1(checkType(term1,L,1))=true andalso #2(checkType(term1,L,1))=1 then (true,0,L)
                                                 else if #1(checkType(term1,L,expected))=true andalso #2(checkType(term1,L,expected))>1 then (true,0,replaceType(!rc,L,1))
                                                 else (false,~1,L)
   									|	GTZ term1 =>  if #1(checkType(term1,L,1))=true andalso #2(checkType(term1,L,1))=1 then (true,0,L)
                                                  else if #1(checkType(term1,L,expected))=true andalso #2(checkType(term1,L,expected))>1 then (true,0,replaceType(!rc,L,1))
                                                  else (false,~1,L)
   									|	P term1 => if #1(checkType(term1,L,1))=true andalso #2(checkType(term1,L,1))=1 then (true,1,L)
                                                else if #1(checkType(term1,L,1))=true andalso #2(checkType(term1,L,1))>1 then (true,1,replaceType(!rc,L,1))
                                                else (false,~1,L)
   									|	S term1 => let
                                                     val temp1 = checkType(term1,L,1)
                                                 in
                                                     if #1(temp1)=true andalso #2(temp1)=1 then (true,1,#3(temp1))
                                                    else if #1(temp1)=true andalso #2(temp1)>1 then (true,1,replaceType(!rc,L,1))
                                                    else (false,~1,L)
                                                end
   									|	VAR x => if expected>(~1) andalso expected<2 then change(VAR x,L,expected,L) else change(VAR x,L,!rc,L)
									|	ITE(LAMBDA(_,_), term1, term2) => (false, ~1, [])
									|	ITE(term1, LAMBDA(_,_), term2) => (false, ~1, [])
									|	ITE(term1, term2, LAMBDA(_,_)) => (false, ~1, [])
									|	ITE(term1,term2,term3) => let
	                                                                 val temp1 = checkType(term1,L,0)
	                                                                 val temp2 = checkType(term2,#3(temp1),expected)
	                                                                 val temp3 = checkType(term3,#3(temp2),expected)
	                                                              in
	                                                                 rc:= (!rc) + 1;
	                                                                 if #1(temp1)=false orelse #1(temp2)=false orelse #1(temp3)=false then
	                                                                    (false,~1,#3(temp3))
	                                                                 else if #2(temp1)=0 then
	                                                                     if #2(temp2)= #2(temp3) then (true,#2(temp2),#3(temp3))
	                                                                     else if #2(temp2)<2 andalso #2(temp3)<2 then (false,~1,#3(temp3))
	                                                                     else if #2(temp2)> #2(temp3)  then (true,#2(temp3),changeList(#2(temp2),[],#3(temp3),#2(temp3)))
	                                                                     else if #2(temp2)< #2(temp3) then (true,#2(temp2),changeList(#2(temp3),[],#3(temp3),#2(temp2)))
	                                                                     else (false,~1,#3(temp3))
	                                                                 else if #2(temp1)=1 then (false,~1,#3(temp3))
	                                                                 else (false,~1,#3(temp3))
	                                                              end
									|   LAMBDA(VAR x,term2) => checkType(term2,L,expected)
									|   LAMBDA(term1,term2) => raise Not_wellformed
									|   APP(APP(term1,term2),term3) => let
                                                                         val temp1 = checkType(term3,L,expected)
                                                                         val temp2 = checkType(APP(term1,term2),#3(temp1),expected)
                                                                     in
                                                                       if #1(temp1)=true andalso #1(temp2)=true then
                                                                               checkType(betanfmodified(APP(APP(term1,term2),term3)),[],expected)
                                                                       else
                                                                         (false,~1,[])
                                                                     end
									|   APP(LAMBDA(VAR x,term2),term3) => let
                                                                             val temp1 = checkType(term3,L,expected)
                                                                             val temp2 = checkType(term2,#3(temp1),expected)
                                                                        in
                                                                             if #1(temp1)=true andalso #1(temp2)=true then
                                                                               checkType(betanfmodified(APP(LAMBDA(VAR x,term2),term3)),[],expected)
                                                                             else
                                                                               (false,~1,[])
                                                                       end
									|	APP(term1 as VAR x,term2) =>  if checkType(term1,L,expected)=checkType(term2,L,expected) then (false,~1,[])
			                                                           else if #2(checkType(term1,L,expected)) >1 andalso #2(checkType(term2,L,expected))>1 then (true,~1,[])
			                                                           else checkType(betanfmodified(APP(term1,term2)),L,expected)
									|   APP(LAMBDA(term1,term2),term3) => raise Not_wellformed
									|   APP(_,_) => (false,~1,[])

in
   fun isWellTyped(term1) = let
   								(* val term = rename(term1 , []) *)
								val t = checkType(term1,[],!rc)
							in
								if #1(checkType(term1,[],!rc)) = true then true else false
							end
end;(*isWellTyped*)







local
	fun checkOtherConstructor z = (case z of
									Z => F
									| S z' => checkOtherConstructor z'
									| P z' => checkOtherConstructor z'
									| ITE(T,Z,x) => F
									| ITE(F,x,Z) => F
									| _ => T
									)

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
									| _ => ITE(c',x',y')
									)
									end
	|	normalize (APP(x, y)) = let
										val x' = normalize(x)
										val y' = normalize(y)
									in
										APP(x',y')
									end
	|	normalize (LAMBDA(x, y)) = let
										val y' = normalize(y)
									in
										LAMBDA(x,y')
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

	fun replave(x, VAR v, r) =  (case x of
	 							S y => (S (replave(y, VAR v, r)))
							|	P y => (P (replave(y, VAR v, r)))
							|	T => T
							|	F => F
							|	Z => Z
							|	IZ y => (IZ (replave(y, VAR v, r)))
							|	GTZ y => (GTZ (replave(y, VAR v, r)))
							|	LAMBDA(a, b) => LAMBDA(a, (replave(b, VAR v, r)))
							|	ITE(a,b,c) => ITE((replave(a, VAR v, r)),(replave(b, VAR v, r)),(replave(c, VAR v, r)))
							|	APP(a, b) => APP((replave(a, VAR v, r)),(replave(b, VAR v, r)))
							|	VAR y => if(y = v) then r else VAR y
						);
in
	fun betanf(t) =  let
						val (main, lis) = rename(t, [])
						val x = if(isWellTyped(main)) then normalize(main) else raise Not_welltyped
					in
						(case x of
	 							S y => let val y1 = normalize(y) val y2 = (betanf(y1)) val y3 = normalize(S y2) in y3 end
							|	P y => let val y1 = normalize(y) val y2 = (betanf(y1)) val y3 = normalize(P y2) in y3 end
							|	T => T
							|	F => F
							|	Z => Z
							|	IZ y =>  let val y1 = normalize(y) val y2 = (betanf(y1)) val y3 = normalize(IZ y2) in y3 end
							|	GTZ y =>  let val y1 = normalize(y) val y2 = (betanf(y1)) val y3 = normalize(GTZ y2) in y3 end
							|	ITE(a, b, c) => let
													val a1 = normalize(a)
													val a2 = betanf(a1)
													val b1 = normalize(b)
													val b2 = betanf(b1)
													val c1 = normalize(c)
													val c2 = betanf(c1)
													val f = normalize(ITE(a2,b2,c2))
												in
													f
												end
							|	LAMBDA(a, b) => let
													val a1 = normalize(a)
													val a2 = betanf(a1)
													val b1 = normalize(b)
													val b2 = betanf(b1)
													val f = normalize(LAMBDA(a2, b2))
												in
													f
												end
							|	APP(a, b) => let
												val a1 = normalize(a)
												val a2 = betanf(a1)
												val b1 = normalize(b)
												val b2 = betanf(b1)
												val f = (case a2 of
															LAMBDA(m, n) => replave(n, m, b2)
															| 	_ => a2
														)
											 in
											 	normalize(f)
											 end
							|	VAR y => VAR y
						)
					end
end;(*betanf*)
end;(*struct*)
