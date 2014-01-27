use "TYPING.sig";
use "EVAL.sig";
use "QUOTE.sig";

signature TYPINGDEPS =
sig
  structure syn   : SYN
  structure eval  : EVAL where syn = syn
  structure quote : QUOTE where syn = syn
end

functor Typing (deps : TYPINGDEPS) :> TYPING =
struct
  structure syn = deps.syn
  structure eval = deps.eval
  structure quote = deps.quote

  exception unknown_identifier of syn.name
  exception illegal_application of syn.iterm * syn.cterm
  exception cannot_synthesize_type
  exception mismatched_type of syn.value * (syn.value option)

  fun itype (i, g: syn.value syn.name_env * syn.ctx, x) =
    case x of
      syn.ann (e, t)   =>
        let
          val _ = ctype (i, g, t, syn.vuni)
          val t = eval.ceval (t, (#1 g, []))
          val _ = ctype (i, g, e, t)
        in
          t
        end
    | syn.uni          => syn.vuni
    | syn.pi (s, t)    =>
        let
          val _  = ctype (i, g, t, syn.vuni)
          val s' = eval.ceval (t, (#1 g, []))
          val _  = ctype (i + 1, ((fn (d,g) => (d, (syn.locl i, s') :: g)) g), csubst (0, syn.free (syn.locl i), t), syn.vuni)
        in
          syn.vuni
        end
    | syn.free x       =>
        (case syn.lookup (x, #2 g) of
          NONE    => raise unknown_identifier x
        | SOME ty => ty)
    | syn.app (f, x)   =>
        (case itype (i, g, f) of
          syn.vpi (s, t) => (ctype (i, g, x, s); t (eval.ceval (x, (#1 g, []))))
        | _              => raise illegal_application (f, x))
    | syn.eq (a, x, y) =>
        let
          val _  = ctype (i, g, a, syn.vuni)
          val a' = eval.ceval (a, (#1 g, []))
          val _  = ctype (i, g, x, a')
          val _  = ctype (i, g, y, a')
        in
          syn.vuni
        end
    | syn.bound x      => raise cannot_synthesize_type

  and ctype (i, g, x, t) =
    case x of
      syn.inf e =>
        let
          val t'  = itype (i, g, e)
          val qt  = quote.quote (0, t)
          val qt' = quote.quote (0, t')
        in
          if qt <> qt' then raise mismatched_type (t, SOME t') else ()
        end
    | syn.lam e =>
        (case t of
          syn.vpi (dom, cod) =>
            ctype (i + 1, ((fn (d,g) => (d, (syn.locl i, dom) :: g)) g), csubst (0, syn.free (syn.locl i), e), cod (syn.vfree (syn.locl i)))
        | _ => raise mismatched_type (t, NONE))
    | syn.refl (a,z) =>
        (case t of
          syn.veq (vb, vx, vy) =>
            let
              val _ = ctype (i, g, a, syn.vuni)
              val va = eval.ceval (a, (#1 g, []))
              val vz = eval.ceval (z, (#1 g, []))
              val qa = quote.quote (0, va)
              val qb = quote.quote (0, vb)
              val qz = quote.quote (0, vz)
              val qx = quote.quote (0, vx)
              val qy = quote.quote (0, vy)
            in
              if qa <> qb orelse qz <> qx orelse qz <> qy
              then
                raise mismatched_type (t, NONE)
              else
                ()
            end
        | _ => raise mismatched_type (t, NONE))

  and isubst (i, x, y) =
    case y of
      syn.ann (c, c')   => syn.ann (csubst (i, x, c), csubst (i, x, c'))
    | syn.uni           => syn.uni
    | syn.pi (dom, cod) => syn.pi (csubst (i, x, dom), csubst (i + 1, x, cod))
    | syn.bound j       => if i = j then x else syn.bound j
    | syn.free z        => syn.free z
    | syn.app (f, z)    => syn.app (isubst (i, x, f), csubst (i, x, z))
    | syn.eq (a, m, n)  => syn.eq (csubst (i, x, a), csubst (i, x, m), csubst (i, x, n))

  and csubst (i, x, y) =
    case y of
      syn.inf e       => syn.inf (isubst (i, x, e))
    | syn.lam e       => syn.lam (csubst (i + 1, x, e))
    | syn.refl (a, z) => syn.refl (csubst (i, x, a), csubst (i, x, z))
end

