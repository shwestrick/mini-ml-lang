(* "promotion stack passing style" *)
structure PSPS:
sig
  val convert: Lang.exp -> Lang.exp
end =
struct

  open Lang

  fun hasPar e =
    case e of
      Par _ => true
    | Var v => false
    | Num n => false
    | Loc l => false
    | Ref e' => hasPar e'
    | Upd (e1, e2) => List.exists hasPar [e1, e2]
    | Bang e' => hasPar e'
    | Array es => List.exists hasPar es
    | Alloc e' => hasPar e'
    | AUpd (e1, e2, e3) => List.exists hasPar [e1, e2, e3]
    | ASub (e1, e2) => List.exists hasPar [e1, e2]
    | Length e' => hasPar e'
    | App (e1, e2) => List.exists hasPar [e1, e2]
    | Seq (e1, e2) => List.exists hasPar [e1, e2]
    | Tuple es => List.exists hasPar es
    | Select (n, e') => hasPar e'
    | Let (v, e1, e2) => List.exists hasPar [e1, e2]
    | Lambda (arg, body) => hasPar body
    | Func (func, arg, body) => hasPar body
    | Op (name, f, e1, e2) => List.exists hasPar [e1, e2]
    | IfZero (e1, e2, e3) => List.exists hasPar [e1, e2, e3]
    | Nil => false
    | IsNil e => hasPar e
    | Head e => hasPar e
    | Tail e => hasPar e
    | Cons (e1, e2) => List.exists hasPar [e1, e2]


  fun patch1 constructor e =
    let
      val p = Id.new "p"
      val vp = Id.new "vp"
    in
      Lambda (p,
      Let (vp, App (e, Var p),
      Tuple [constructor (Fst (Var vp)), Snd (Var vp)]))
    end

  fun patch2 constructor (e1, e2) =
    let
      val p = Id.new "p"
      val vp1 = Id.new "vp"
      val vp2 = Id.new "vp"
    in
      Lambda (p,
      Let (vp1, App (e1, Var p),
      Let (vp2, App (e2, Snd (Var vp1)),
      Tuple [constructor (Fst (Var vp1), Fst (Var vp2)), Snd (Var vp2)])))
    end

  fun patch3 constructor (e1, e2, e3) =
    let
      val p = Id.new "p"
      val vp1 = Id.new "vp"
      val vp2 = Id.new "vp"
      val vp3 = Id.new "vp"
    in
      Lambda (p,
      Let (vp1, App (e1, Var p),
      Let (vp2, App (e2, Snd (Var vp1)),
      Let (vp3, App (e3, Snd (Var vp2)),
      Tuple
        [ constructor (Fst (Var vp1), Fst (Var vp2), Fst (Var vp3))
        , Snd (Var vp3)
        ]))))
    end


  fun patchN constructor es =
    let
      val p = Id.new "p"

      fun loop pexp vps es =
        case es of
          [] => Tuple [constructor (List.map (Fst o Var) (List.rev vps)), pexp]
        | e :: rest =>
            let
              val vp = Id.new "vp"
            in
              Let (vp, App (e, pexp),
              loop (Snd (Var vp)) (vp :: vps) rest)
            end
    in
      Lambda (p, loop (Var p) [] es)
    end


  fun patchSimple e =
    let
      val p = Id.new "p"
    in
      Lambda (p, Tuple [e, Var p])
    end


  fun convert e =
    convertHasPar e
    (* if hasPar e then
      convertHasPar e
    else
      let
        val p = Id.new "p"
      in
        Lambda (p, Tuple [e, Var p])
      end *)

  and convertHasPar e =
    case e of
      Nil =>
        patchSimple e

    | Num _ =>
        patchSimple e

    | Var _ =>
        patchSimple e

    | Ref e' =>
        patch1 Ref (convert e')

    | App (e1, e2) =>
        let
          val p = Id.new "p"
          val fp = Id.new "fp"
          val vp = Id.new "vp"
        in
          Lambda (p,
          Let (fp, App (convert e1, Var p),
          Let (vp, App (convert e2, Snd (Var fp)),
          App (App (Fst (Var fp), Fst (Var vp)), Snd (Var vp)))))
        end

    | Lambda (arg, body) =>
        let
          val p = Id.new "p"
        in
          Lambda (p,
          Tuple [Lambda (arg, convert body), Var p])
        end

    | Func (func, arg, body) =>
        let
          val p = Id.new "p"
        in
          Lambda (p,
          Tuple [Func (func, arg, convert body), Var p])
        end

    | Bang e' =>
        patch1 Ref (convert e')

    | Length e' =>
        patch1 Length (convert e')

    | Alloc e' =>
        patch1 Alloc (convert e')

    | Select (n, e') =>
        patch1 (fn x => Select (n, x)) (convert e')

    | Upd (e1, e2) =>
        patch2 Upd (convert e1, convert e2)

    | AUpd (e1, e2, e3) =>
        patch3 AUpd (convert e1, convert e2, convert e3)

    | ASub (e1, e2) =>
        patch2 ASub (convert e1, convert e2)

    | Op (name, f, e1, e2) =>
        patch2 (fn (a, b) => Op (name, f, a, b)) (convert e1, convert e2)

    | Seq (e1, e2) =>
        patch2 (fn (a, b) => b) (convert e1, convert e2)

    | IsNil e =>
        patch1 IsNil (convert e)

    | Head e =>
        patch1 Head (convert e)

    | Tail e =>
        patch1 Tail (convert e)

    | Cons (e1, e2) =>
        patch2 Cons (convert e1, convert e2)

    | IfZero (e1, e2, e3) =>
        let
          val p = Id.new "p"
          val bp = Id.new "bp"
        in
          Lambda (p,
          Let (bp, App (convert e1, Var p),
          IfZero (Fst (Var bp),
            App (convert e2, Snd (Var bp)),
            App (convert e3, Snd (Var bp)))))
        end

    | Let (v, e1, e2) =>
        let
          val p = Id.new "p"
          val vp = Id.new "vp"
        in
          Lambda (p,
          Let (vp, App (convert e1, Var p),
          Let (v, Fst (Var vp),
          App (convert e2, Snd (Var vp)))))
        end

    | Tuple es =>
        patchN Tuple (List.map convert es)

    | Array es =>
        patchN Array (List.map convert es)

    | Par es =>
        patchN Par (List.map convert es)

    | _ => raise Fail ("PSPS.convert not yet implemented for: " ^ toString e)


  val convert_ = convert

  fun convert e =
    let
      val e' = convert_ e
    in
      App (e', Nil)
    end
end
