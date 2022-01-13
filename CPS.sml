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

  fun convertOp1 (c: exp -> exp) =
    continueWith (withNewVar "tmp" (fn x => Lambda (x, continueWith (c (Var x)))))

  fun convertOp2 (c: exp * exp -> exp) =
    continueWith (
      withNewVar "tmp" (fn x =>
      withNewVar "tmp" (fn y =>
        Lambda (x, Lambda (y, continueWith (c (Var x, Var y))))
    )))


  fun patch2 (e1, e2) =
    let
      val k = Id.new "K"
      val tmp1 = Id.new "tmp"
      val tmp2 = Id.new "tmp"
    in
      Lambda (k,
        App (e1, Lambda (tmp1,
        App (e2, Lambda (tmp2,
        App (App (Var tmp1, Var tmp2), Var k)
      )))))
    end


  fun patch3 (e1, e2, e3) =
    let
      val k = Id.new "K"
      val tmp1 = Id.new "tmp"
      val tmp2 = Id.new "tmp"
      val tmp3 = Id.new "tmp"
    in
      Lambda (k,
        App (e1, Lambda (tmp1,
        App (e2, Lambda (tmp2,
        App (e3, Lambda (tmp3,
        App (App (App (Var tmp1, Var tmp2), Var tmp3), Var k)
      )))))))
    end


  fun patchN (c: exp list -> exp) es =
    let
      val k = Id.new "K"
      val tmps = List.map (fn _ => Id.new "tmp") es
    in
      Lambda (k,
        foldr
          (fn ((e, tmp), body) => App (e, Lambda (tmp, body)))
          (App (Var k, c (List.map Var tmps)))
          (Util.zip es tmps)
      )
    end


  fun convert' exp =
    case exp of
      Var x => continueWith exp

    | Num n => continueWith exp

    | Loc l => continueWith exp

    | Lambda (arg, body) => continueWith (Lambda (arg, convert' body))

    | Func (fname, farg, body) =>
        continueWith (Func (fname, farg, convert' body))

    | Op (name, f, e1, e2) =>
        patch3
          ( convertOp2 (fn (x, y) => Op (name, f, x, y))
          , convert' e1
          , convert' e2
          )

    | Upd (e1, e2) =>
        patch3 (convertOp2 Upd, convert' e1, convert' e2)

    | ASub (e1, e2) =>
        patch3 (convertOp2 ASub, convert' e1, convert' e2)

    | App (e1, e2) =>
        patch2 (convert' e1, convert' e2)

    | Ref e =>
        patch2 (convertOp1 Ref, convert' e)

    | Length e =>
        patch2 (convertOp1 Length, convert' e)

    | Bang e =>
        patch2 (convertOp1 Bang, convert' e)

    | Alloc e =>
        patch2 (convertOp1 Alloc, convert' e)

    | Select (n, e) =>
        patch2 (convertOp1 (fn x => Select (n, x)), convert' e)

    | Let (v, e1, e2) =>
        withNewVar "K" (fn k =>
          Lambda (k,
            App (convert' e1, Lambda (v, App (convert' e2, Var k)))
          ))

    | Seq (e1, e2) =>
        let
          val k = Id.new "K"
          val tmp = Id.new "tmp"
        in
          Lambda (k,
            App (convert' e1, Lambda (tmp,
            App (convert' e2, Var k)
          )))
        end

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

    | Tuple es =>
        patchN Tuple (List.map convert' es)

    | Array es =>
        patchN Array (List.map convert' es)

    | Par [e1, e2] =>
        let
          val k = Id.new "K"
          val left1 = Id.new "left"
          val left2 = Id.new "left"
          val right1 = Id.new "right"
          val right2 = Id.new "right"
          val right3 = Id.new "right"
          val syncvar1 = Id.new "syncvar"
          val syncvar2 = Id.new "syncvar"
          val pp = Id.new "P"

          val e1' = convert' e1
          val e2' = convert' e2

          val normalCont =
            Lambda (left1,
            Seq (PopPromotionReady,
            App (e2', Lambda (right1,
            App (Var k, Tuple [Var left1, Var right1])))))

          val leftParCont =
            Lambda (syncvar1, Lambda (left2,
            Seq (PopPromotionReady,
            App (continueWith (Wait (Var syncvar1)), Lambda (right2,
            App (Var k, Tuple [Var left2, Var right2]))))))

          val rightParCont =
            Lambda (syncvar2,
            App (e2', Lambda (right3,
            Upd (Var syncvar2, Var right3))))
        in
          Lambda (k,
            Let (pp, Ref normalCont,
            Seq (PushPromotionReady (leftParCont, rightParCont, Var pp),
            App (e1', Bang (Var pp)))))
        end


  fun convert e =
    App (convert' e, idFunc ())

end
