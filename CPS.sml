structure CPS:
sig
  val convert: Lang.exp -> Lang.exp
end =
struct

  open Lang

  fun withNewVar name (f: var -> 'a) : 'a =
    f (Id.new name)

  fun idFunc () =
    withNewVar "tmp" (fn x => Lambda (x, Var x))

  fun continueWith e =
    withNewVar "K" (fn k => Lambda (k, App (Var k, e)))

  fun convertConstructor (c: exp -> exp) =
    continueWith (withNewVar "tmp" (fn x => Lambda (x, continueWith (c (Var x)))))

  fun convertOp (name, f) =
    continueWith (
      withNewVar "tmp" (fn x =>
      withNewVar "tmp" (fn y =>
        Lambda (x, Lambda (y, continueWith (Op (name, f, Var x, Var y))))
    )))

  fun convert' exp =
    case exp of
      Var x => continueWith exp
    | Num n => continueWith exp
    | Loc l => continueWith exp

    | Let (v, e1, e2) =>
        withNewVar "K" (fn k =>
          Lambda (k,
            App (convert' e1, Lambda (v, App (convert' e2, Var k)))
          ))

    | IfZero (e1, e2, e3) =>
        let
          val k = Id.new "K"
          val tmp = Id.new "tmp"
        in
          Lambda (k,
            App (convert' e1, Lambda (tmp,
            IfZero (Var tmp,
              App (convert' e2, Var k),
              App (convert' e3, Var k)
            ))))
        end

    | Lambda (arg, body) =>
        continueWith (Lambda (arg, convert' body))

    | App (e1, e2) =>
        let
          val k = Id.new "K"
          val tmp1 = Id.new "tmp"
          val tmp2 = Id.new "tmp"
        in
          Lambda (k,
            App (convert' e1, Lambda (tmp1,
            App (convert' e2, Lambda (tmp2,
            App (App (Var tmp1, Var tmp2), Var k)
          )))))
        end

    | Op (name, f, e1, e2) =>
        let
          val k = Id.new "K"
          val tmpOp = Id.new "tmp"
          val tmp1 = Id.new "tmp"
          val tmp2 = Id.new "tmp"
        in
          Lambda (k,
            App (convertOp (name, f), Lambda (tmpOp,
            App (convert' e1, Lambda (tmp1,
            App (convert' e2, Lambda (tmp2,
            App (App (App (Var tmpOp, Var tmp1), Var tmp2), Var k)
          )))))))
        end

    | Ref e =>
        let
          val k = Id.new "K"
          val tmp1 = Id.new "tmp"
          val tmp2 = Id.new "tmp"
        in
          Lambda (k,
            App (convertConstructor Ref, Lambda (tmp1,
            App (convert' e, Lambda (tmp2,
            App (App (Var tmp1, Var tmp2), Var k)
          )))))
        end


    | _ => raise Fail "convert case not yet implemented"

    (*
    | Func (func, arg, body) =>
    | Par es =>
    | Upd (e1, e2) =>
    | Bang e =>
    | Array es =>
    | Alloc e =>
    | AUpd (e1, e2, e3) =>
    | ASub (e1, e2) =>
    | Length e =>
    | Seq (e1, e2) =>
    | Tuple es =>
    | Select (n, e) =>
    *)


  fun convert e =
    App (convert' e, idFunc ())

end
