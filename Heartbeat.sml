structure Heartbeat:
sig
  (** requires exp is already CPS.convert'ed *)
  val exec: {heartbeat: int} -> Lang.exp -> unit
end =
struct

  open Lang

  type mem = exp Lang.IdTable.t

  structure HBStack:
  sig
    type elem = exp * exp * exp
    type t
    val empty: t
    val push: elem -> t -> t
    val pop: t -> t
    val promoteOldest: t -> (t * elem) option
  end =
  struct
    type elem = (exp * exp * exp)
    datatype t = HBS of {ready: elem list, alreadyPromoted: elem list}

    val empty = HBS {ready = [], alreadyPromoted = []}

    fun push x (HBS {ready, alreadyPromoted}) =
      HBS {ready = x :: ready, alreadyPromoted = alreadyPromoted}

    fun pop (HBS {ready, alreadyPromoted=ap}) =
      case ready of
        x :: rest => HBS {ready = rest, alreadyPromoted = ap}
      | [] =>
      case ap of
        x :: rest => HBS {ready = [], alreadyPromoted = rest}
      | [] => raise Fail "HBStack.pop: empty"

    fun promoteOldest (HBS {ready=r, alreadyPromoted=ap}) =
      case Util.splitLast r of
        SOME (r', x) =>
          SOME (HBS {ready = r', alreadyPromoted = x :: ap}, x)
      | NONE =>
          NONE
  end

  type hbstack = HBStack.t

  type m =
    { memory: mem
    , hbstack: hbstack
    }

  datatype 'a step_result =
    Next of 'a
  | Blocked
  | Done


  (** ======================================================================
    * rewriting normal steps... tedious...
    *)

  fun stepApp step (m: m) (e1, e2) =
    case step (m, e1) of
      Next (m', e1') => Next (m', App (e1', e2))
    | Blocked => Blocked
    | Done =>
        case step (m, e2) of
          Next (m', e2') => Next (m', App (e1, e2'))
        | Blocked => Blocked
        | Done =>
            case getLoc (deLoc e1) (#memory m) of
              Func (func, arg, body) =>
                Next (m, subst (e1, func) (subst (e2, arg) body))
            | Lambda (arg, body) =>
                Next (m, subst (e2, arg) body)
            | e =>
                raise Fail ("Heartbeat.stepApp, non-function: " ^ Lang.toString e)

  fun stepFirstThatCan
        (step: m * exp -> (m * exp) step_result)
        (m: m)
        (es: exp list)
        : (m * (exp list)) step_result
    =
    case es of
      [] => Done
    | e :: rest =>
        case step (m, e) of
          Next (m', e') => Next (m', e' :: rest)
        | Blocked => Blocked
        | Done =>
            case stepFirstThatCan step m rest of
              Next (m', rest') => Next (m', e :: rest')
            | Blocked => Blocked
            | Done => Done

  fun stepPar step m es =
    case stepFirstThatCan step m es of
      Next (m', es') => Next (m', Par es')
    | Blocked => Blocked
    | Done => Next (m, Tuple es)

  fun stepTuple step m es =
    case stepFirstThatCan step m es of
      Next (m', es') => Next (m', Tuple es')
    | Blocked => Blocked
    | Done =>
        let
          val l = Id.loc ()
        in
          Next
            ( { memory = IdTable.insert (l, Tuple es) (#memory m)
              , hbstack = #hbstack m
              }
            , Loc l
            )
        end

  fun stepArray step m es =
    case stepFirstThatCan step m es of
      Next (m', es') => Next (m', Array es')
    | Blocked => Blocked
    | Done =>
        let
          val l = Id.loc ()
        in
          Next
            ( { memory = IdTable.insert (l, Array es) (#memory m)
              , hbstack = #hbstack m
              }
            , Loc l
            )
        end

  fun stepAlloc step (m: m) e =
    case step (m, e) of
      Next (m', e') => Next (m', Alloc e')
    | Blocked => Blocked
    | Done =>
        let
          val n = deNum e

          (* cheat by initializing with a bunch of bogus pointers *)
          val es = List.tabulate (n, fn _ => Loc bogusLoc)
          val l = Id.loc ()
        in
          Next
            ( { memory = IdTable.insert (l, Array es) (#memory m)
              , hbstack = #hbstack m
              }
            , Loc l
            )
        end


  fun stepAUpd step (m: m) (e1, e2, e3) =
    case step (m, e1) of
      Next (m', e1') => Next (m', AUpd (e1', e2, e3))
    | Blocked => Blocked
    | Done =>
        case step (m, e2) of
          Next (m', e2') => Next (m', AUpd (e1, e2', e3))
        | Blocked => Blocked
        | Done =>
            case step (m, e3) of
                Next (m', e3') => Next (m', AUpd (e1, e2, e3'))
              | Blocked => Blocked
              | Done =>
                  let
                    val l = deLoc e1
                    val es = deArray (getLoc l (#memory m))
                    val idx = deNum e2

                    (* jump to idx fun replace step with e3 *)
                    val es' =
                      List.take (es, idx) @ (e3 :: List.drop (es, idx+1))
                  in
                    Next
                      ( { memory = IdTable.insert (l, Array es') (#memory m)
                        , hbstack = #hbstack m
                        }
                      , e3
                      )
                  end

  fun stepASub step (m: m) (e1, e2) =
    case step (m, e1) of
      Next (m', e1') => Next (m', ASub (e1', e2))
    | Blocked => Blocked
    | Done =>
        case step (m, e2) of
          Next (m', e2') => Next (m', ASub (e1, e2'))
        | Blocked => Blocked
        | Done =>
            let
              val l = deLoc e1
              val es = deArray (getLoc l (#memory m))
              val idx = deNum e2
            in
              Next (m, List.nth (es, idx))
            end

  fun stepLength step (m: m) e =
    case step (m, e) of
      Next (m', e') => Next (m', Length e')
    | Blocked => Blocked
    | Done =>
        let
          val es = deArray (getLoc (deLoc e) (#memory m))
        in
          Next (m, Num (List.length es))
        end

  fun stepSelect step (m: m) (n, e) =
    case step (m, e) of
      Next (m', e') => Next (m', Select (n, e'))
    | Blocked => Blocked
    | Done =>
        Next (m, List.nth (deTuple (getLoc (deLoc e) (#memory m)), n-1))

  fun stepLet step (m: m) (v, e1, e2) =
    case step (m, e1) of
      Next (m', e1') => Next (m', Let (v, e1', e2))
    | Blocked => Blocked
    | Done => Next (m, subst (e1, v) e2)

  fun stepOp step (m: m) (name, oper, e1, e2) =
    case step (m, e1) of
      Next (m', e1') => Next (m', Op (name, oper, e1', e2))
    | Blocked => Blocked
    | Done =>
        case step (m, e2) of
          Next (m', e2') => Next (m', Op (name, oper, e1, e2'))
        | Blocked => Blocked
        | Done =>
            let
              val n1 = deNum e1
              val n2 = deNum e2
            in
              Next (m, Num (oper (n1, n2)))
            end

  fun stepIfZero step (m: m) (e1, e2, e3) =
    case step (m, e1) of
      Next (m', e1') => Next (m', IfZero (e1', e2, e3))
    | Blocked => Blocked
    | Done =>
        Next (if deNum e1 = 0 then (m, e2) else (m, e3))


  fun stepLambda step (m: m) (arg, body) =
    let
      val l = Id.loc ()
    in
      Next
        ( { memory = IdTable.insert (l, Lambda (arg, body)) (#memory m)
          , hbstack = #hbstack m
          }
        , Loc l
        )
    end

  fun stepFunc step (m: m) (func, arg, body) =
    let
      val l = Id.loc ()
    in
      Next
        ( { memory = IdTable.insert (l, Func (func, arg, body)) (#memory m)
          , hbstack = #hbstack m
          }
        , Loc l
        )
    end

  fun stepRef step (m: m) e =
    case step (m, e) of
      Next (m', e') => Next (m', Ref e')
    | Blocked => Blocked
    | Done =>
        let
          val l = Id.loc ()
        in
          Next
            ( { memory = IdTable.insert (l, Ref e) (#memory m)
              , hbstack = #hbstack m
              }
            , Loc l
            )
        end

  fun stepBang step (m: m) e =
    case step (m, e) of
      Next (m', e') => Next (m', Bang e')
    | Blocked => Blocked
    | Done =>
        Next (m, deRef (getLoc (deLoc e) (#memory m)))

  fun stepUpd step (m: m) (e1, e2) =
    case step (m, e1) of
      Next (m', e1') => Next (m', Upd (e1', e2))
    | Blocked => Blocked
    | Done =>
        case step (m, e2) of
          Next (m', e2') => Next (m', Upd (e1, e2'))
        | Blocked => Blocked
        | Done =>
            Next
              ( { memory = IdTable.insert (deLoc e1, Ref e2) (#memory m)
                , hbstack = #hbstack m
                }
              , e2
              )


  fun stepSeq step (m: m) (e1, e2) =
    case step (m, e1) of
      Next (m', e1') => Next (m', Seq (e1', e2))
    | Blocked => Blocked
    | Done => Next (m, e2)

  (** ====================================================================== *)


  fun stepPushPR m (e1, e2, e3) =
    case hbstep (m, e1) of
      Next (m', e1') => Next (m', PushPromotionReady (e1', e2, e3))
    | Blocked => Blocked
    | Done =>
    case hbstep (m, e2) of
      Next (m', e2') => Next (m', PushPromotionReady (e1, e2', e3))
    | Blocked => Blocked
    | Done =>
    case hbstep (m, e3) of
      Next (m', e3') => Next (m', PushPromotionReady (e1, e2, e3'))
    | Blocked => Blocked
    | Done =>
        ( (*print ("pushPR\n");*)
        Next
          ( { memory = #memory m
            , hbstack = HBStack.push (e1, e2, e3) (#hbstack m)
            }
          , Tuple []
          )
        )

  and stepPopPR m =
    ( (*print ("popPR\n");*)
    Next
      ( {memory = #memory m, hbstack = HBStack.pop (#hbstack m)}
      , Tuple []
      )
    )

  and stepWait m e =
    case hbstep (m, e) of
      Next (m', e') => Next (m', Wait e')
    | Blocked => Blocked
    | Done =>
        let
          val contents = deRef (getLoc (deLoc e) (#memory m))
        in
          case contents of
            Loc l =>
              if Id.eq (l, Lang.bogusLoc) then
                Blocked
              else
                Next (m, contents)
          | _ =>
            Next (m, contents)
        end

  and hbstep (m, e) =
    case e of
      PushPromotionReady x => stepPushPR m x
    | PopPromotionReady => stepPopPR m
    | Wait x => stepWait m x

    | Var x    => Done
    | Num x    => Done
    | Loc x    => Done
    | App x    => stepApp hbstep m x
    | Par x    => stepPar hbstep m x
    | Tuple x  => stepTuple hbstep m x
    | Select x => stepSelect hbstep m x
    | Let x    => stepLet hbstep m x
    | Op x     => stepOp hbstep m x
    | IfZero x => stepIfZero hbstep m x
    | Lambda x => stepLambda hbstep m x
    | Func x   => stepFunc hbstep m x
    | Ref x    => stepRef hbstep m x
    | Bang x   => stepBang hbstep m x
    | Upd x    => stepUpd hbstep m x
    | Seq x    => stepSeq hbstep m x
    | Array x  => stepArray hbstep m x
    | Alloc x  => stepAlloc hbstep m x
    | AUpd x   => stepAUpd hbstep m x
    | ASub x   => stepASub hbstep m x
    | Length x => stepLength hbstep m x


  fun doPromotions mem activeThreads =
    let
      (* val _ = print ("heartbeat\n") *)
      fun doPromotion mem hbstack =
        ( (*print ("trying to promote, hbstack size = " ^ Int.toString (List.length hbstack) ^ "\n");*)
        case HBStack.promoteOldest hbstack of
          NONE => NONE
        | SOME (hbstack', oldest as (e1, e2, e3)) =>
            let
              (* val _ = print "promoting...\n"
              val _ = print ("  e1 = " ^ Lang.toString e1 ^ "\n")
              val _ = print ("  e2 = " ^ Lang.toString e2 ^ "\n")
              val _ = print ("  e3 = " ^ Lang.toString e3 ^ "\n") *)
              val leftParCont = getLoc (deLoc e1) mem
              val rightParCont = getLoc (deLoc e2) mem
              val leftContRefLoc = deLoc e3

              val newLeftContLoc = Id.loc ()
              val syncvarLoc = Id.loc ()
              val syncvar = Loc syncvarLoc

              val tmp = Id.new "tmp"
              val newLeftCont =
                Lambda (tmp, App (App (leftParCont, syncvar), Var tmp))

              val rightSideThread =
                (HBStack.empty, App (rightParCont, syncvar))

              val mem = IdTable.insert (syncvarLoc, Ref (Loc bogusLoc)) mem
              val mem = IdTable.insert (newLeftContLoc, newLeftCont) mem
              val mem = IdTable.insert (leftContRefLoc, Ref (Loc newLeftContLoc)) mem
              (* val _ = print "finished promotion\n" *)
            in
              SOME (mem, hbstack', rightSideThread)
            end)

      fun loop mem done newThreads todo =
        case todo of
          [] => (mem, newThreads @ List.rev done)
        | (hbstack, exp) :: todo' =>
            case doPromotion mem hbstack of
              NONE =>
                loop mem ((hbstack, exp) :: done) newThreads todo'
            | SOME (mem', hbstack', newThread) =>
                loop
                  mem'
                  ((hbstack', exp) :: done)
                  (newThread :: newThreads)
                  todo'

      val (mem, threads) = loop mem [] [] activeThreads
    in
      (mem, threads)
    end


  fun filterTrySteps mem threads =
    let
      fun loop mem active blocked threads =
        case threads of
          [] => (mem, List.rev active, List.rev blocked)
        | (hbstack, exp) :: threads' =>
            case hbstep ({memory = mem, hbstack = hbstack}, exp) of
              Next ({memory = mem', hbstack = hbstack'}, exp') =>
                loop mem' ((hbstack', exp') :: active) blocked threads'
            | Blocked =>
                loop mem active ((hbstack, exp) :: blocked) threads'
            | Done =>
                loop mem active blocked threads'

      val (mem, active, blocked) = loop mem [] [] threads
    in
      (mem, active, blocked)
    end


  fun exec {heartbeat} exp =
    let
      fun loop numSteps maxActive mem threads =
        if List.null threads then
          (numSteps, maxActive, mem)
        else
        let
          val (mem, active, blocked) = filterTrySteps mem threads
          val numSteps' = numSteps+1
          val maxActive = Int.max (List.length active, maxActive)

          val (mem, active) =
            if numSteps' mod heartbeat = 0 then
              doPromotions mem active
            else
              (mem, active)
        in
          loop numSteps' maxActive mem (active @ blocked)
        end

      (** Write the final result into the memory at a predetermined location.
        * This makes it possible to ignore all results of threads, and we
        * don't need to keep track of which thread is the "main" thread.
        *)
      val resultLoc = Id.loc ()
      val initMem = IdTable.insert (resultLoc, Ref (Loc bogusLoc)) IdTable.empty
      val mainThread =
        ( HBStack.empty
        , Upd (Loc resultLoc, exp)
        )

      val (numSteps, maxActive, finalMem) = loop 0 1 initMem [mainThread]

      val result = deRef (getLoc resultLoc finalMem)
    in
      print ("num steps: " ^ Int.toString numSteps ^ "\n");
      print ("max active: " ^ Int.toString maxActive ^ "\n");
      case result of
        Loc l => print ("RESULT: " ^ toString (getLoc l finalMem) ^ "\n")
      | Num n => print ("RESULT: " ^ Int.toString n ^ "\n")
      | _ => print ("ERROR\n")
    end

end
