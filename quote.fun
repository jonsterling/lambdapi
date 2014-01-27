use "QUOTE.sig";

functor Quotation (syn : SYN) =
struct
  structure syn = syn

  fun quote (i, x) =
    case x of
      syn.vlam f        => syn.lam (quote (i + 1, f (syn.vfree (syn.quote i))))
    | syn.vuni          => syn.inf syn.uni
    | syn.vpi (s, t)    => syn.inf (syn.pi (quote (i, s), quote (i + 1, t (syn.vfree (syn.quote i)))))
    | syn.vneutral n    => syn.inf (neutralQuote (i, n))
    | syn.vrefl (a, z)  => syn.refl (quote (i, a), quote (i, z))
    | syn.veq (a, m, n) => syn.inf (syn.eq (quote (i, a), quote (i, m), quote (i, n)))

  and neutralQuote (i, x) =
    case x of
      syn.nfree n     => boundFree (i, n)
    | syn.napp (f, x) => syn.app (neutralQuote (i, f), quote (i, x))

  and boundFree (i, n) =
    case n of
      syn.quote k => syn.bound (Int.max (i - k - 1, 0))
    | _           => syn.free n
end
:> QUOTE where syn = syn
