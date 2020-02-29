type ide = string;;
type exp = Eint of int | Ebool of bool | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
	Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp*exp | And of exp*exp | Not of exp |
	Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
	Letrec of ide * exp * exp
	| ETree of tree (* gli alberi sono anche espressioni *)
	| ApplyOver of exp * exp (* applicazione di funzione ai nodi *)
	| Update of (ide list) * exp * exp (* aggiornamento di un nodo *)
	| Select of (ide list)* exp * exp (* selezione condizionale di un nodo *)
and tree = Empty (* albero vuoto *)
	| Node of ide * exp * tree * tree;; (* albero binario *)
(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT = Int of int | Bool of bool | Unbound | FunVal of evFun | RecFunVal of ide * evFun | TreeVal of treeVal
and evFun = ide * exp * evT env
and treeVal = Empty | ValNode of ide * evT * treeVal * treeVal;;

(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
	"int" -> (match v with
		Int(_) -> true |
		_ -> false) |
	"bool" -> (match v with
		Bool(_) -> true |
		_ -> false) |
	_ -> failwith("not a valid type");;

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n*u))
	else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n+u))
	else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n-u))
	else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Bool(n=u))
	else failwith("Type error");;

let minus x = if (typecheck "int" x) 
	then (match x with
	   	Int(n) -> Int(-n))
	else failwith("Type error");;

let iszero x = if (typecheck "int" x)
	then (match x with
		Int(n) -> Bool(n=0))
	else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> (Bool(b||e)))
	else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> Bool(b&&e))
	else failwith("Type error");;

let non x = if (typecheck "bool" x)
	then (match x with
		Bool(true) -> Bool(false) |
		Bool(false) -> Bool(true))
	else failwith("Type error");;

(*interprete*)
let rec eval (e : exp) (r : evT env) : evT =
	match e with
	Eint n -> Int n |
	Ebool b -> Bool b |
	IsZero a -> iszero (eval a r) |
	Den i -> applyenv r i |
	Eq(a, b) -> eq (eval a r) (eval b r) |
	Prod(a, b) -> prod (eval a r) (eval b r) |
	Sum(a, b) -> sum (eval a r) (eval b r) |
	Diff(a, b) -> diff (eval a r) (eval b r) |
	Minus a -> minus (eval a r) |
	And(a, b) -> et (eval a r) (eval b r) |
	Or(a, b) -> vel (eval a r) (eval b r) |
	Not a -> non (eval a r) |
	Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") |
	Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
	Fun(i, a) -> FunVal(i, a, r) |
	FunCall(f, eArg) -> 
		let fClosure = (eval f r) in
			(match fClosure with
				FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) |
				RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in
						let rEnv = (bind fDecEnv g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								eval fBody aEnv |
				_ -> failwith("non functional value")) |
        Letrec(f, funDef, letBody) ->
        		(match funDef with
            		Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                         			                eval letBody r1 |
            		_ -> failwith("non functional def"))
    |ETree tree -> TreeVal(treeEval tree r) 
    |ApplyOver (exf,ext) -> (match ext with
    			ETree tree ->TreeVal(exfVal exf tree r)
    			|_-> failwith("Error: tree expected"))
    |Update (idl , exf ,ext ) -> (match ext with
    		ETree tree -> TreeVal(updateVal idl exf tree r)
    			|_-> failwith("Error : tree expected"))
    |Select(idl , exf, ext) -> (match ext with
    			ETree tree -> TreeVal(selectVal idl exf tree r)
    			|_-> failwith("Error: tree expected"))
and treeEval t r = match t with
  				Empty -> Empty
    			| Node (id,exp,left,right) -> ValNode(id,eval exp r, treeEval left r, treeEval right r)
and exfVal exf t r = match t with
					Empty->Empty
					| Node (id,exp,left,right) -> ValNode(id,eval (FunCall(exf, exp)) r,exfVal exf left r,exfVal exf right r)
and updateVal idl exf t r = match t with
					Empty->Empty
					|Node (id,exp,left,right)->
							(match idl with
								[]-> ValNode(id,eval exp r,updateVal idl exf left r,updateVal idl exf right r)
								|x::[]-> if (x = id)
												then ValNode(id,eval(FunCall(exf,exp)) r, updateVal [] exf left r, updateVal [] exf right r)
												else ValNode(id,eval exp r, updateVal [] exf left r,updateVal [] exf right r)
								|x::xs-> if (x = id)
												then ValNode(id,eval(FunCall(exf,exp))r,updateVal xs exf left r,updateVal xs exf right r)
												else ValNode(id, eval exp r,updateVal xs exf left r, updateVal xs exf right r))
and selectVal idl exf t r = match t with
					Empty-> Empty
					|Node (id,exp,left,right)->
								(match idl with
									[]->Empty
									|x::[]->if (x=id)
														then if((eval (FunCall(exf,exp)) r)=Bool(true))
																		then ValNode(id, eval exp r, treeEval left r, treeEval right r)
																		else Empty
														else Empty
									|x::xs->if (x=id)
														then if((eval (FunCall(exf,exp)) r)=Bool(true))
																		then ValNode(id,eval exp r,treeEval left r,treeEval right r)
																		else let save = selectVal xs exf left r in
																if (save = Empty) then let save2 = selectVal xs exf right r in
																	if (save2 = Empty) then Empty
																	else save2
																else save
														else Empty);;

(*-----------------------------------------------Test---------------------------------------------------------*)
				

let env0 = emptyenv Unbound;;
let albero= ETree(Node("a",Prod(Eint 0, Eint(1)),
			Node("b",Eint(2),Empty,Empty),
			Node("c",Eint(3),Empty,Empty)));;
let div = eval albero env0;;
let e1 = ApplyOver(Fun("y", Sum(Den "y", Eint 1)),albero);;
let div2 = eval e1 env0;;

(* questa update non modifica alcun nodo dell'albero perchè nessun elemento della lista corrisponde con un nodo dell'
	 albero *)
let e2 = Update(["f";"g";"h"],Fun ("y",Prod(Den "y",Eint 4)),albero);;
let div3 = eval e2 env0;;

(* gli elementi della lista di Select sono identici ai nodi dell'albero e la funzione trova nella radice un valore che 
   la soddisfa *)
let e3 = Select(["a";"b";"c"],Fun("y",IsZero(Den "y")),albero);;
let div4 = eval e3 env0;;


(*
let env1 = emptyenv Unbound;;
let albero= ETree(Node("a",Prod(Eint 0, Eint(1)),
			Node("b",Eint(2),Empty,Empty),
			Node("c",Eint(3),Empty,Empty)));;
let div = eval albero env1;;
let e1 = ApplyOver(Fun("y", Sum(Den "y", Eint 1)),albero);;
let div2 = eval e1 env1;;

(* vengono modificati tutti i nodi dell'albero *)
let e2 = Update(["a";"b";"c"],Fun ("y",Prod(Den "y",Eint 4)),albero);;
let div3 = eval e2 env1;;

(* risultato della Select sarà Empty perchè gli elementi della lista sono tutti diversi dai nodi dell'albero *)
let e3 = Select(["f";"g";"h"],Fun("y",IsZero(Den "y")),albero);;
let div4 = eval e3 env1;;
*)


(*
let env2 = emptyenv Unbound;;
let albero= ETree(Node("a",Prod(Eint 1, Eint(1)),
			Node("b",Eint(2),Empty,Empty),
			Node("c",Eint(3),Empty,Empty)));;
let div = eval albero env2;;
let e1 = ApplyOver(Fun("y", Sum(Den "y", Eint 1)),albero);;
let div2 = eval e1 env2;;

let e2 = Update(["a";"b";"c"],Fun ("y",Prod(Den "y",Eint 4)),albero);;
let div3 = eval e2 env2;;

(* la Select restituira Empty perchè nessun valore dei nodi soddisfa la funzione *)
let e3 = Select(["a";"b";"c"],Fun("y",IsZero(Den "y")),albero);;
let div4 = eval e3 env2;;
*)


