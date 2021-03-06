(* Lang has no types. Just raw AST *)
structure Lang =
struct

  structure Id = Identifier
  structure IdTable = TreeTable(Id)
  type var = Id.t
  (* type typ = Type.t *)

  type loc = Id.t

  val bogusLoc = Id.new "bogus"

  datatype exp =
    Var of var
  | Loc of loc (* "internal"; not visible to other langs *)

  | Ref of exp
  | Upd of exp * exp
  | Bang of exp

  | Array of exp list
  | Alloc of exp
  | AUpd of exp * exp * exp
  | ASub of exp * exp
  | Length of exp

  | Nil
  | IsNil of exp  (* returns 0 or 1 as a hack. sorry. *)
  | Tail of exp
  | Head of exp
  | Cons of exp * exp

  | Seq of exp * exp
  | App of exp * exp
  | Par of exp list   (* arbitrarily wide tuples *)
  | Tuple of exp list (* arbitrarily wide tuples *)
  | Select of int * exp
  | Let of var * exp * exp
  | Lambda of var * exp
  | Func of var * var * exp (* function name, argument, function body *)
  | Num of int
  | IfZero of exp * exp * exp
  | Op of string * (int * int -> int) * exp * exp

  | PushPromotionReady of exp * exp * exp
  | PopPromotionReady
  | Wait of exp

  | Spawn of exp
  | Sync of exp


  fun OpAdd (e1, e2) = Op ("+", op+, e1, e2)
  fun OpSub (e1, e2) = Op ("-", op-, e1, e2)
  fun OpMul (e1, e2) = Op ("*", op*, e1, e2)
  fun OpDiv (e1, e2) = Op ("/", fn (x, y) => x div y, e1, e2)

  fun parens s = "(" ^ s ^ ")"

  fun toString e =
    case e of
      Var v => Id.toString v
    | Num n => Int.toString n
    | Loc l => Id.toString l
    | Ref e' => "ref " ^ toStringP e'
    | Bang e' => "!" ^ toStringP e'
    | Upd (e1, e2) => toStringP e1 ^ " := " ^ toStringP e2

    | Array es => "[" ^ String.concatWith ", " (List.map toStringP es) ^ "]"
    | Alloc e' => "alloc " ^ toStringP e'
    | AUpd (e1, e2, e3) =>
        toStringP e1 ^ "[" ^ toString e2 ^ "] := " ^ toString e3
    | ASub (e1, e2) =>
        toStringP e1 ^ "[" ^ toString e2 ^ "]"
    | Length e' => "length " ^ toStringP e'

    | App (e1, e2) =>
        toStringP e1 ^ " " ^ toStringP e2
    | Seq (e1, e2) =>
        toStringP e1 ^ " ; " ^ toStringP e2
    | Par es =>
        "(" ^ String.concatWith " || " (List.map toString es) ^ ")"
    | Tuple es =>
        "(" ^ String.concatWith ", " (List.map toString es) ^ ")"
    | Select (n, e') => "#" ^ Int.toString n ^ " " ^ toStringP e'
    | Let (v, e1, e2) =>
        "let " ^ Id.toString v ^ " = " ^ toString e1 ^ " in " ^ toString e2
    | Lambda (arg, body) =>
        "fn " ^ Id.toString arg ^ " => " ^ toString body
    | Func (func, arg, body) =>
        "fun " ^ Id.toString func ^ " " ^ Id.toString arg ^ " is " ^ toString body
    | Op (name, _, e1, e2) =>
        toStringP e1 ^ " " ^ name ^ " " ^ toStringP e2
    | IfZero (e1, e2, e3) =>
        "ifz " ^ toString e1 ^ " then " ^ toString e2 ^ " else " ^ toString e3

    | Nil => "nil"
    | IsNil e => "isNil " ^ toStringP e
    | Head e => "hd " ^ toStringP e
    | Tail e => "tl " ^ toStringP e
    | Cons (e1, e2) => toStringP e1 ^ " :: " ^ toStringP e2

    | Spawn e => "spawn " ^ toStringP e
    | Sync e => "sync " ^ toStringP e

    | PushPromotionReady _ => "(PushPR)"
    | PopPromotionReady => "(PopPR)"
    | Wait _ => "(WAIT)"

  and toStringP e =
    let
      val needsP =
        case e of
          App _ => true
        | Op _ => true
        | Alloc _ => true
        | AUpd _ => true
        | ASub _ => true
        | Length _ => true
        | IfZero _ => true
        | Select _ => true
        | Let _ => true
        | Lambda _ => true
        | Func _ => true
        | Upd _ => true
        | Ref _ => true
        | Bang _ => true
        | Seq _ => true
        | Head _ => true
        | Tail _ => true
        | Cons _ => true
        | IsNil _ => true
        | Spawn _ => true
        | Sync _ => true
        | _ => false
    in
      if needsP then parens (toString e) else toString e
    end

  fun isFunc e = case e of Func _ => true | _ => false
  fun isLambda e = case e of Lambda _ => true | _ => false

  fun deFunc e = case e of Func x => x | _ => raise Fail "deFunc"
  fun deLambda e = case e of Lambda x => x | _ => raise Fail "deLambda"
  fun deNum e = case e of Num x => x | _ => raise Fail "deNum"
  fun deLoc e = case e of Loc l => l | _ => raise Fail "deLoc"
  fun deTuple e = case e of Tuple x => x | _ => raise Fail "deTuple"
  fun deRef e = case e of Ref x => x | _ => raise Fail "deRef"
  fun deArray e = case e of Array x => x | _ => raise Fail "deArray"

  (* substitute [e'/x]e *)
  fun subst (e', x) e =
    let
      (* val _ = print ("[" ^ toString e' ^ " / " ^ Id.toString x ^ "]" ^ toString e ^ "\n") *)
      val doit = subst (e', x)
    in
      case e of
        Var v => if Id.eq (v, x) then e' else Var v
      | Num n => Num n
      | Loc l => Loc l
      | Ref e' => Ref (doit e')
      | Upd (e1, e2) => Upd (doit e1, doit e2)
      | Bang e' => Bang (doit e')

      | Array es => Array (List.map doit es)
      | Alloc e' => Alloc (doit e')
      | AUpd (e1, e2, e3) => AUpd (doit e1, doit e2, doit e3)
      | ASub (e1, e2) => ASub (doit e1, doit e2)
      | Length e' => Length (doit e')

      | App (e1, e2) => App (doit e1, doit e2)
      | Par es => Par (List.map doit es)
      | Seq (e1, e2) => Seq (doit e1, doit e2)
      | Tuple es => Tuple (List.map doit es)
      | Select (n, e') => Select (n, doit e')
      | Let (v, e1, e2) => Let (v, doit e1, doit e2)
      | Lambda (arg, body) => Lambda (arg, doit body)
      | Func (func, arg, body) => Func (func, arg, doit body)
      | Op (name, f, e1, e2) => Op (name, f, doit e1, doit e2)
      | IfZero (e1, e2, e3) => IfZero (doit e1, doit e2, doit e3)

      | Nil => Nil
      | IsNil e => IsNil (doit e)
      | Head e => Head (doit e)
      | Tail e => Tail (doit e)
      | Cons (e1, e2) => Cons (doit e1, doit e2)

      | Spawn e => Spawn (doit e)
      | Sync e => Sync (doit e)

      | PushPromotionReady (e1, e2, e3) =>
          PushPromotionReady (doit e1, doit e2, doit e3)
      | PopPromotionReady => PopPromotionReady

      | Wait e => Wait (doit e)
    end

  (* =======================================================================
   * let-normal form
   * "A-normal" form??
   *)

  fun normalizeMany (exps: exp list) (makeBase: exp list -> exp) =
    let
      (* first, generate identifiers and normalize where needed *)
      val exps =
        List.map
          (fn Var v => {var = v, exp = Var v, fresh = false}
            | e     => {var = Id.new "xxx", exp = letNormalize e, fresh = true})
        exps

      fun makeNext ({var, exp, fresh}, base) =
        if fresh then
          Let (var, exp, base)
        else
          base

      val vars = List.map (Var o #var) exps
    in
      List.foldr makeNext (makeBase vars) exps
    end

  and normalize1 e (mb: exp -> exp) =
    normalizeMany [e] (fn [e'] => mb e'
                        | _ => raise Fail "normalize1")
  and normalize2 (e1, e2) (mb: exp * exp -> exp) =
    normalizeMany [e1, e2] (fn [e1', e2'] => mb (e1', e2')
                             | _ => raise Fail "normalize2")
  and normalize3 (e1, e2, e3) (mb: exp * exp * exp -> exp) =
    normalizeMany [e1, e2, e3] (fn [e1', e2', e3'] => mb (e1', e2', e3')
                                 | _ => raise Fail "normalize3")

  and letNormalize exp =
    case exp of
      Var v                  => exp
    | Num n                  => exp
    | Loc l                  => exp
    | Let (v, e1, e2)        => Let (v, letNormalize e1, letNormalize e2)
    | Lambda (arg, body)     => Lambda (arg, letNormalize body)
    | Func (func, arg, body) => Func (func, arg, letNormalize body)
    | Par es                 => Par (List.map letNormalize es)
    | Ref e                  => normalize1 e Ref
    | Upd (e1, e2)           => normalize2 (e1, e2) Upd
    | Bang e                 => normalize1 e Bang
    | Array es               => normalizeMany es Array
    | Alloc e                => normalize1 e Alloc
    | AUpd (e1, e2, e3)      => normalize3 (e1, e2, e3) AUpd
    | ASub (e1, e2)          => normalize2 (e1, e2) ASub
    | Length e               => normalize1 e Length
    | App (e1, e2)           => normalize2 (e1, e2) App
    | Seq (e1, e2)           => normalize2 (e1, e2) Seq
    | Tuple es               => normalizeMany es Tuple
    | Select (n, e)          => normalize1 e (fn e' => Select (n, e'))
    | IfZero (e1, e2, e3)    =>
        normalize1 e1 (fn e1' => IfZero (e1', letNormalize e2, letNormalize e3))
    | Op (name, f, e1, e2) =>
        normalize2 (e1, e2) (fn (e1', e2') => Op (name, f, e1', e2'))

  fun isVar (Var _) = true
    | isVar _ = false

  fun isLetNormal exp =
    case exp of
      Var v                  => true
    | Num n                  => true
    | Loc l                  => true
    | Seq (e1, e2)           => isLetNormal e1 andalso isLetNormal e2
    | Let (v, e1, e2)        => isLetNormal e1 andalso isLetNormal e2
    | Lambda (arg, body)     => isLetNormal body
    | Func (func, arg, body) => isLetNormal body
    | Par es                 => List.all isLetNormal es
    | Ref e                  => isVar e
    | Upd (e1, e2)           => isVar e1 andalso isVar e2
    | Bang e                 => isVar e
    | Array es               => List.all isVar es
    | Alloc e                => isVar e
    | AUpd (e1, e2, e3)      => isVar e1 andalso isVar e2 andalso isVar e3
    | ASub (e1, e2)          => isVar e1 andalso isVar e2
    | Length e               => isVar e
    | App (e1, e2)           => isVar e1 andalso isVar e2
    | Tuple es               => List.all isVar es
    | Select (n, e)          => isVar e
    | IfZero (e1, e2, e3)    => isVar e1 andalso isLetNormal e2 andalso isLetNormal e3
    | Op (name, f, e1, e2)   => isVar e1 andalso isVar e2

  (* =======================================================================
   * execution
   *)

  (* mapping of locations to expressions *)
  type memory = exp IdTable.t

  fun getLoc loc mem =
    case IdTable.lookup loc mem of
      NONE => raise Fail ("getLoc " ^ Id.toString loc)
    | SOME x => x

  fun stepApp step m (e1, e2) =
    case step (m, e1) of
      SOME (m', e1') => (m', App (e1', e2))
    | NONE =>
        case step (m, e2) of
          SOME (m', e2') => (m', App (e1, e2'))
        | NONE =>
            case getLoc (deLoc e1) m of
              Func (func, arg, body) =>
                (m, subst (e1, func) (subst (e2, arg) body))
            | Lambda (arg, body) =>
                (m, subst (e2, arg) body)
            | _ =>
                raise Fail "stepApp"

  (* Walk through es, trying to step each expression, from left to right.
   * as soon as we find an e -> e', we replace e with e' and back out,
   * returning the updated memory. If no expression can step, then we
   * are done stepping this group of expressions. This is used to implement
   * both Tuple stepping, and Par stepping. Really, Par stepping should be
   * parallel or interleaved, but whatever.
   *)
  fun stepFirstThatCan
        (step: memory * exp -> (memory * exp) option)
        (m: memory)
        (es: exp list)
        : (memory * (exp list)) option
    =
    case es of
      [] => NONE
    | e :: rest =>
        case step (m, e) of
          SOME (m', e') => SOME (m', e' :: rest)
        | NONE =>
            case stepFirstThatCan step m rest of
              SOME (m', rest') => SOME (m', e :: rest')
            | NONE => NONE

  fun stepPar step m es =
    case stepFirstThatCan step m es of
      SOME (m', es') => (m', Par es')
    | NONE => (m, Tuple es)

  fun stepTuple step m es =
    case stepFirstThatCan step m es of
      SOME (m', es') => (m', Tuple es')
    | NONE =>
        let
          val l = Id.loc ()
        in
          (IdTable.insert (l, Tuple es) m, Loc l)
        end

  fun stepArray step m es =
    case stepFirstThatCan step m es of
      SOME (m', es') => (m', Array es')
    | NONE =>
        let
          val l = Id.loc ()
        in
          (IdTable.insert (l, Array es) m, Loc l)
        end

  fun stepAlloc step m e =
    case step (m, e) of
      SOME (m', e') => (m', Alloc e')
    | NONE =>
        let
          val n = deNum e

          (* cheat by initializing with a bunch of bogus pointers *)
          val es = List.tabulate (n, fn _ => Loc bogusLoc)
          val l = Id.loc ()
        in
          (IdTable.insert (l, Array es) m, Loc l)
        end

  fun stepAUpd step m (e1, e2, e3) =
    case step (m, e1) of
      SOME (m', e1') => (m', AUpd (e1', e2, e3))
    | NONE =>
        case step (m, e2) of
          SOME (m', e2') => (m', AUpd (e1, e2', e3))
        | NONE =>
            case step (m, e3) of
                SOME (m', e3') => (m', AUpd (e1, e2, e3'))
              | NONE =>
                  let
                    val l = deLoc e1
                    val es = deArray (getLoc l m)
                    val idx = deNum e2

                    (* jump to idx fun replace step with e3 *)
                    val es' =
                      List.take (es, idx) @ (e3 :: List.drop (es, idx+1))
                  in
                    (IdTable.insert (l, Array es') m, e3)
                  end

  fun stepASub step m (e1, e2) =
    case step (m, e1) of
      SOME (m', e1') => (m', ASub (e1', e2))
    | NONE =>
        case step (m, e2) of
          SOME (m', e2') => (m', ASub (e1, e2'))
        | NONE =>
            let
              val l = deLoc e1
              val es = deArray (getLoc l m)
              val idx = deNum e2
            in
              (m, List.nth (es, idx))
            end

  fun stepLength step m e =
    case step (m, e) of
      SOME (m', e') => (m', Length e')
    | NONE =>
        let
          val es = deArray (getLoc (deLoc e) m)
        in
          (m, Num (List.length es))
        end

  fun stepSelect step m (n, e) =
    case step (m, e) of
      SOME (m', e') => (m', Select (n, e'))
    | NONE =>
        (m, List.nth (deTuple (getLoc (deLoc e) m), n-1))

  fun stepLet step m (v, e1, e2) =
    case step (m, e1) of
      SOME (m', e1') => (m', Let (v, e1', e2))
    | NONE => (m, subst (e1, v) e2)

  fun stepOp step m (name, oper, e1, e2) =
    case step (m, e1) of
      SOME (m', e1') => (m', Op (name, oper, e1', e2))
    | NONE =>
        case step (m, e2) of
          SOME (m', e2') => (m', Op (name, oper, e1, e2'))
        | NONE =>
            let
              val n1 = deNum e1
              val n2 = deNum e2
            in
              (m, Num (oper (n1, n2)))
            end

  fun stepIfZero step m (e1, e2, e3) =
    case step (m, e1) of
      SOME (m', e1') => (m', IfZero (e1', e2, e3))
    | NONE =>
        if deNum e1 = 0 then (m, e2) else (m, e3)

  fun stepLambda step m (arg, body) =
    let
      val l = Id.loc ()
    in
      (IdTable.insert (l, Lambda (arg, body)) m, Loc l)
    end

  fun stepFunc step m (func, arg, body) =
    let
      val l = Id.loc ()
    in
      (IdTable.insert (l, Func (func, arg, body)) m, Loc l)
    end

  fun stepRef step m e =
    case step (m, e) of
      SOME (m', e') => (m', Ref e')
    | NONE =>
        let
          val l = Id.loc ()
        in
          (IdTable.insert (l, Ref e) m, Loc l)
        end

  fun stepBang step m e =
    case step (m, e) of
      SOME (m', e') => (m', Bang e')
    | NONE =>
        (m, deRef (getLoc (deLoc e) m))

  fun stepUpd step m (e1, e2) =
    case step (m, e1) of
      SOME (m', e1') => (m', Upd (e1', e2))
    | NONE =>
        case step (m, e2) of
          SOME (m', e2') => (m', Upd (e1, e2'))
        | NONE =>
            (IdTable.insert (deLoc e1, Ref e2) m, e2)

  fun stepSeq step m (e1, e2) =
    case step (m, e1) of
      SOME (m', e1') => (m', Seq (e1', e2))
    | NONE => (m, e2)

  fun stepNil step m =
    let
      val l = Id.loc ()
    in
      (IdTable.insert (l, Nil) m, Loc l)
    end

  fun stepIsNil step m e =
    case step (m, e) of
      SOME (m', e') => (m', IsNil e')
    | NONE =>
        case getLoc (deLoc e) m of
          Nil => (m, Num 1)
        | Cons _ => (m, Num 0)
        | _ => raise Fail "IsNil (???)"

  fun stepHead step m e =
    case step (m, e) of
      SOME (m', e') => (m', Head e')
    | NONE =>
        case getLoc (deLoc e) m of
          Nil => raise Fail "Head Nil"
        | Cons (first, _) => (m, first)
        | _ => raise Fail "Head (???)"

  fun stepTail step m e =
    case step (m, e) of
      SOME (m', e') => (m', Tail e')
    | NONE =>
        case getLoc (deLoc e) m of
          Nil => (m, e)
        | Cons (_, rest) => (m, rest)
        | _ => raise Fail "Tail (???)"

  fun stepCons step m (e1, e2) =
    case step (m, e1) of
      SOME (m', e1') => (m', Cons (e1', e2))
    | NONE =>
        case step (m, e2) of
          SOME (m', e2') => (m', Cons (e1, e2'))
        | NONE =>
            let
              val l = Id.loc ()
            in
              (IdTable.insert (l, Cons (e1, e2)) m, Loc l)
            end

  fun stepSpawn step m e =
    (m, e)

  fun stepSync step m e =
    (m, e)

  fun dispatchStep stepper (m, e) =
    case e of
      Var x    => NONE
    | Num x    => NONE
    | Loc x    => NONE
    | App x    => SOME (stepApp stepper m x)
    | Par x    => SOME (stepPar stepper m x)
    | Tuple x  => SOME (stepTuple stepper m x)
    | Select x => SOME (stepSelect stepper m x)
    | Let x    => SOME (stepLet stepper m x)
    | Op x     => SOME (stepOp stepper m x)
    | IfZero x => SOME (stepIfZero stepper m x)
    | Lambda x => SOME (stepLambda stepper m x)
    | Func x   => SOME (stepFunc stepper m x)
    | Ref x    => SOME (stepRef stepper m x)
    | Bang x   => SOME (stepBang stepper m x)
    | Upd x    => SOME (stepUpd stepper m x)
    | Seq x    => SOME (stepSeq stepper m x)
    | Array x  => SOME (stepArray stepper m x)
    | Alloc x  => SOME (stepAlloc stepper m x)
    | AUpd x   => SOME (stepAUpd stepper m x)
    | ASub x   => SOME (stepASub stepper m x)
    | Length x => SOME (stepLength stepper m x)
    | Nil      => SOME (stepNil stepper m)
    | IsNil x  => SOME (stepIsNil stepper m x)
    | Tail x   => SOME (stepTail stepper m x)
    | Head x   => SOME (stepHead stepper m x)
    | Cons x   => SOME (stepCons stepper m x)
    | Spawn x  => SOME (stepSpawn stepper m x)
    | Sync x   => SOME (stepSync stepper m x)

    | PushPromotionReady _ => SOME (m, Loc bogusLoc)
    | PopPromotionReady => SOME (m, Loc bogusLoc)
    | Wait x => SOME (m, Loc bogusLoc)


  fun step (m, e) = dispatchStep step (m, e)

  fun exec' doPrint e =
    let
      fun p s = if doPrint then print s else ()
      fun loop (m, e) =
        let
          val _ = p (IdTable.toString (fn e => " " ^ toString e ^ "\n") m ^ "\n")
          val _ = p (toString e ^ "\n\n")
        in
          case step (m, e) of
            NONE => (m, e)
          | SOME (m', e') => loop (m', e')
        end

      val (m, e) = loop (IdTable.empty, e)
    in
      case e of
        Loc l => print ("RESULT: " ^ toString (getLoc l m) ^ "\n")
      | Num n => print ("RESULT: " ^ Int.toString n ^ "\n")
      | _ => print ("ERROR\n");

      (* (m, e) *)
      ()
    end

  fun exec e = exec' true e

  (* ======================================================================= *)

  fun Fst e = Select (1, e)
  fun Snd e = Select (2, e)
  fun IfNil (e1, e2, e3) = IfZero (IsNil e1, e3, e2)

  val fact: exp =
    let
      val f = Id.new "fact"
      val n = Id.new "n"
      val body =
        IfZero (Var n, Num 1, OpMul (Var n, App (Var f, OpSub (Var n, Num 1))))
    in
      Func (f, n, body)
    end

  val doubleFirst: exp =
    let
      val f = Id.new "f"
      val x = Id.new "x"
      val y = Id.new "y"
    in
      Func (f, x, Let (y, Fst (Var x), OpAdd (Var y, Var y)))
    end

  val doesntTypeCheck: exp =
    let
      val f = Id.new "f"
      val x = Id.new "x"
      val ff = Id.new "ff"
      val idFunc =
        Func (f, x, Var x)
    in
      (* make f the identity function, but apply it to two different
       * arguments. we don't have polymorphism! *)
      Let (ff, idFunc, Par [App (Var ff, Num 1), App (Var ff, (Par [Num 2, Num 3]))])
    end

  val parAdd: exp =
    let
      val left = OpAdd (Num 1, Num 2)
      val right = OpAdd (Num 3, Num 4)
      val x = Id.new "x"
    in
      Let (x, Par [left, right], OpAdd (Select (1, Var x), Select (2, Var x)))
    end

  val iterFib: exp =
    let
      (* iterFib takes x = (a, b, n) where a and b are the two most recent *)
      val iterFib = Id.new "iterFib"
      val x = Id.new "x"
      val a = Select (1, Var x)
      val b = Select (2, Var x)
      val n = Select (3, Var x)
      val elseBranch =
        App (Var iterFib, Tuple [b, OpAdd (a, b), OpSub (n, Num 1)])
      val body = IfZero (n, a, elseBranch)
    in
      Func (iterFib, x, body)
    end

  val fib: exp =
    let
      val fib = Id.new "fib"
      val n = Id.new "n"
    in
      Func (fib, n, App (iterFib, Tuple [Num 0, Num 1, Var n]))
    end

  val impFib: exp =
    let
      val a = Id.new "a"
      val b = Id.new "b"
      val aa = Id.new "aa"

      val loop = Id.new "loop"
      val loop' = Id.new "loop"
      val n = Id.new "n"

      val updStmt =
        Let (aa, Bang (Var a),
          Upd (Var b, OpAdd (Var aa, Upd (Var a, Bang (Var b)))))

      val loopFunc =
        Func (loop, n, IfZero (Var n, Bang (Var a),
          Seq (updStmt, App (Var loop, OpSub (Var n, Num 1)))))

      val impFib = Id.new "impFib"
      val x = Id.new "x"
    in
      Func (impFib, x,
        Let (a, Ref (Num 0),
        Let (b, Ref (Num 1),
        Let (loop', loopFunc,
        App (Var loop', Var x)))))
    end

  val sum: exp =
    let
      val sum = Id.new "sum"
      val range = Id.new "range"
      val i = Id.new "i"
      val j = Id.new "j"
      val mid = Id.new "mid"
      val c = Id.new "c"

      val body =
        Let (i, Select (1, Var range),
        Let (j, Select (2, Var range),
          IfZero (OpSub (Var j, Var i), Num 0,
          IfZero (OpSub (Var j, OpAdd (Var i, Num 1)), Var i,
          Let (mid, OpAdd (Var i, OpDiv (OpSub (Var j, Var i), Num 2)),
          Let (c, Par [App (Var sum, Tuple [Var i, Var mid]),
                       App (Var sum, Tuple [Var mid, Var j])],
            OpAdd (Select (1, Var c), Select (2, Var c))))))))
    in
      Func (sum, range, body)
    end

  val sumArray: exp =
    let
      val sumRange = Id.new "sumRange"
      val range = Id.new "range"
      val i = Id.new "i"
      val j = Id.new "j"
      val a = Id.new "a"
      val mid = Id.new "mid"
      val c = Id.new "c"

      val body =
        Let (i, Select (1, Var range),
        Let (j, Select (2, Var range),
          IfZero (OpSub (Var j, Var i), Num 0,
          IfZero (OpSub (Var j, OpAdd (Var i, Num 1)), ASub (Var a, Var i),
          Let (mid, OpAdd (Var i, OpDiv (OpSub (Var j, Var i), Num 2)),
          Let (c, Par [App (Var sumRange, Tuple [Var i, Var mid]),
                       App (Var sumRange, Tuple [Var mid, Var j])],
            OpAdd (Select (1, Var c), Select (2, Var c))))))))

      val sumArray = Id.new "sumArray"
    in
      Func (sumArray, a,
        App (Func (sumRange, range, body),
             Tuple [Num 0, Length (Var a)]))
    end

  (* (fn x => x+x) 42 *)
  val applyLamExample: exp =
    let
      val x = Id.new "x"
      val body = OpAdd (Var x, Var x)
    in
      App (Lambda (x, body), Num 42)
    end

  val makeRef: exp =
    let
      val x = Id.new "x"
    in
      Let (x, Ref applyLamExample, Var x)
    end

  val idFunc: exp =
    let
      val x = Id.new "x"
    in
      Lambda (x, Var x)
    end

  val listTabulate: exp =
    let
      val n = Id.new "n"
      val f = Id.new "f"
      val loop1 = Id.new "loop"
      val loop2 = Id.new "loop"
      val i = Id.new "i"
    in
      Lambda (f,
      Lambda (n,
      Let (loop1,
        Func (loop2, i,
          IfZero (OpSub (Var n, Var i),
            Nil,
            Cons (App (Var f, Var i), App (Var loop2, OpAdd (Var i, Num 1))))),
      App (Var loop1, Num 0))))
    end

  val listSum: exp =
    let
      val listSum = Id.new "listSum"
      val xs = Id.new "xs"
    in
      Func (listSum, xs,
        IfNil (Var xs,
          Num 0,
          OpAdd (Head (Var xs), App (Var listSum, Tail (Var xs)))))
    end

end
