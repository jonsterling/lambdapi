use "QUOTE.sig";

functor Quotation (syn : SYN) :> QUOTE where syn = syn =
struct
  structure syn = syn
  open syn

  fun quote (i, x) =
    case x of
      vlam f        => lam (quote (i + 1, f (vfree (quoted i))))
    | vuni          => inf uni
    | vpi (s, t)    => inf (pi (quote (i, s), quote (i + 1, t (vfree (quoted i)))))
    | vneutral n    => inf (neutral_quote (i, n))
    | vrefl (a, z)  => refl (quote (i, a), quote (i, z))
    | veq (a, m, n) => inf (eq (quote (i, a), quote (i, m), quote (i, n)))

  and neutral_quote (i, x) =
    case x of
      nfree n     => bound_free (i, n)
    | napp (f, x) => app (neutral_quote (i, f), quote (i, x))

  and bound_free (i, n) =
    case n of
      quoted k => bound (Int.max (i - k - 1, 0))
    | _           => free n
end
