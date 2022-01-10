structure CPS:
sig
  val convert: Lang.exp -> Lang.exp
end =
struct

  open Lang

  fun withNewVar name (f: var -> 'a) : 'a =
    f (Id.new name)

  fun idFunc () =
    withNewVar "thing" (fn x => Lambda (x, Var x))

  fun returnToCont e =
    withNewVar "K" (fn k => Lambda (k, App (Var k, e)))

  fun convert exp =
    case exp of
      Var x => returnToCont exp
    | Num n => returnToCont exp
    | Loc l => returnToCont exp

    | Let (v, e1, e2) =>
        withNewVar "K" (fn k =>
          Lambda (k,
            App (convert e1, Lambda (v, App (convert e2, Var k)))
          ))

    | IfZero (e1, e2, e3) =>
        let
          val k = Id.new "K"
          val tmp1 = Id.new "tmp"
        in
          Lambda (k,
            App (convert e1, Lambda (tmp1,
            IfZero (Var tmp1,
              App (convert e2, Var k),
              App (convert e3, Var k)
            ))))
        end

    | Lambda (arg, body) =>


    | _ => raise Fail "convert case not yet implemented"

    (*
    | Func (func, arg, body) =>
    | Par es =>
    | Ref e =>
    | Upd (e1, e2) =>
    | Bang e =>
    | Array es =>
    | Alloc e =>
    | AUpd (e1, e2, e3) =>
    | ASub (e1, e2) =>
    | Length e =>
    | App (e1, e2) =>
    | Seq (e1, e2) =>
    | Tuple es =>
    | Select (n, e) =>
    | IfZero (e1, e2, e3) =>
    | Op (name, f, e1, e2) =>
    *)

end
