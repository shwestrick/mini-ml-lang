structure ParOnlyCPS:
sig
  val convert: Lang.exp -> Lang.exp
end =
struct

  open Lang

  fun convert e =
    case e of

      Par [e1, e2] =>
        let
          val e1' = convert e1
          val e2' = convert e2

          val left1 = Id.new "left"
          val left2 = Id.new "left"
          val left3 = Id.new "left"
          val syncvar1 = Id.new "syncvar"
          val syncvar2 = Id.new "syncvar"
          val pp = Id.new "P"

          val normalCont =
            Lambda (left1,
            Seq (PopPromotionReady,
            Tuple [Var left1, e2']))

          val leftParCont =
            Lambda (syncvar1, Lambda (left2,
            Seq (PopPromotionReady,
            Tuple [Var left2, Wait (Var syncvar1)])))

          val rightParCont =
            Lambda (syncvar2,
            Upd (Var syncvar2, e2'))
        in
          Let (pp, Ref normalCont,
          Seq (PushPromotionReady (leftParCont, rightParCont, Var pp),
          Let (left3, e1',
          App (Bang (Var pp), Var left3))))
        end

    | Var v => Var v
    | Num n => Num n
    | Loc l => Loc l
    | Ref e' => Ref (convert e')
    | Upd (e1, e2) => Upd (convert e1, convert e2)
    | Bang e' => Bang (convert e')

    | Array es => Array (List.map convert es)
    | Alloc e' => Alloc (convert e')
    | AUpd (e1, e2, e3) => AUpd (convert e1, convert e2, convert e3)
    | ASub (e1, e2) => ASub (convert e1, convert e2)
    | Length e' => Length (convert e')

    | App (e1, e2) => App (convert e1, convert e2)
    | Par es => Par (List.map convert es)
    | Seq (e1, e2) => Seq (convert e1, convert e2)
    | Tuple es => Tuple (List.map convert es)
    | Select (n, e') => Select (n, convert e')
    | Let (v, e1, e2) => Let (v, convert e1, convert e2)
    | Lambda (arg, body) => Lambda (arg, convert body)
    | Func (func, arg, body) => Func (func, arg, convert body)
    | Op (name, f, e1, e2) => Op (name, f, convert e1, convert e2)
    | IfZero (e1, e2, e3) => IfZero (convert e1, convert e2, convert e3)

    | _ => raise Fail "ParOnlyCPS.convert: error: should not have gotten to this case"

end
