use "EVAL.sig";

functor Evaluation (syn : SYN) :> EVAL where syn = syn =
struct
  structure syn = syn
  open syn

  type 't evaluator = 't * (value name_env * env) -> value

  fun ceval (t, g) =
    case t of
      inf x       => ieval (x,g)
    | lam m       => vlam (fn x => ceval (m, (fn (e,d) => (e, x :: d)) g))
    | refl (a, x) => vrefl (ceval (a,g), ceval (x,g))

  and ieval (t, g) =
    case t of
      ann (c, _)   => ceval (c, g)
    | uni          => vuni
    | pi (s, t)    => vpi (ceval (s,g), fn x => ceval (s, (fn (e,d) => (e, x :: d)) g))
    | free n       => (case lookup (n, #1 g) of
                         NONE   => vfree n
                       | SOME x => x)
    | bound i      => List.nth (#2 g, i)
    | app (f, x)   => vapp (ieval (f, g), ceval (x, g))
    | eq (a, x, y) => veq (ceval (a, g), ceval (x, g), ceval (y, g))

end
