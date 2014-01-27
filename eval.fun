use "EVAL.sig";

functor Evaluation (syn : SYN) :> EVAL =
struct
  structure syn = syn

  type 't evaluator = 't * (syn.value syn.name_env * syn.env) -> syn.value

  fun ceval (t, g) =
    case t of
      syn.inf x       => ieval (x,g)
    | syn.lam m       => syn.vlam (fn x => ceval (m, (fn (e,d) => (e, x :: d)) g))
    | syn.refl (a, x) => syn.vrefl (ceval (a,g), ceval (x,g))

  and ieval (t, g) =
    case t of
      syn.ann (c, _)   => ceval (c, g)
    | syn.uni          => syn.vuni
    | syn.pi (s, t)    => syn.vpi (ceval (s,g), fn x => ceval (s, (fn (e,d) => (e, x :: d)) g))
    | syn.free n       => (case syn.lookup (n, #1 g) of
                            NONE   => syn.vfree n
                          | SOME x => x)
    | syn.bound i      => List.nth (#2 g, i)
    | syn.app (f, x)   => syn.vapp (ieval (f, g), ceval (x, g))
    | syn.eq (a, x, y) => syn.veq (ceval (a, g), ceval (x, g), ceval (y, g))

end
