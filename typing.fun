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
  open deps
  open syn eval quote

  exception unknown_identifier of name
  exception illegal_application of iterm * cterm
  exception cannot_synthesize_type
  exception mismatched_type of value * (value option)

  fun itype (i, g, x) =
    case x of
      ann (e, t)   =>
        let
          val _ = ctype (i, g, t, vuni)
          val t = ceval (t, (#1 g, []))
          val _ = ctype (i, g, e, t)
        in
          t
        end
    | uni          => vuni
    | pi (s, t)    =>
        let
          val _  = ctype (i, g, t, vuni)
          val s' = ceval (t, (#1 g, []))
          val _  = ctype (i + 1, ((fn (d,g) => (d, (locl i, s') :: g)) g), csubst (0, free (locl i), t), vuni)
        in
          vuni
        end
    | free x       =>
        (case lookup (x, #2 g) of
           NONE    => raise unknown_identifier x
         | SOME ty => ty)
    | app (f, x)   =>
        (case itype (i, g, f) of
           vpi (s, t) => (ctype (i, g, x, s); t (ceval (x, (#1 g, []))))
         | _              => raise illegal_application (f, x))
    | eq (a, x, y) =>
        let
          val _  = ctype (i, g, a, vuni)
          val a' = ceval (a, (#1 g, []))
          val _  = ctype (i, g, x, a')
          val _  = ctype (i, g, y, a')
        in
          vuni
        end
    | bound x      => raise cannot_synthesize_type

  and ctype (i, g, x, t) =
    case x of
      inf e =>
        let
          val t'  = itype (i, g, e)
          val qt  = quote (0, t)
          val qt' = quote (0, t')
        in
          if qt <> qt' then raise mismatched_type (t, SOME t') else ()
        end
    | lam e =>
        (case t of
           vpi (dom, cod) =>
             ctype (i + 1, ((fn (d,g) => (d, (locl i, dom) :: g)) g), csubst (0, free (locl i), e), cod (vfree (locl i)))
         | _ => raise mismatched_type (t, NONE))
    | refl (a,z) =>
        (case t of
           veq (vb, vx, vy) =>
             let
               val _ = ctype (i, g, a, vuni)
               val va = ceval (a, (#1 g, []))
               val vz = ceval (z, (#1 g, []))
               val qa = quote (0, va)
               val qb = quote (0, vb)
               val qz = quote (0, vz)
               val qx = quote (0, vx)
               val qy = quote (0, vy)
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
      ann (c, c')   => ann (csubst (i, x, c), csubst (i, x, c'))
    | uni           => uni
    | pi (dom, cod) => pi (csubst (i, x, dom), csubst (i + 1, x, cod))
    | bound j       => if i = j then x else bound j
    | free z        => free z
    | app (f, z)    => app (isubst (i, x, f), csubst (i, x, z))
    | eq (a, m, n)  => eq (csubst (i, x, a), csubst (i, x, m), csubst (i, x, n))

  and csubst (i, x, y) =
    case y of
      inf e       => inf (isubst (i, x, e))
    | lam e       => lam (csubst (i + 1, x, e))
    | refl (a, z) => refl (csubst (i, x, a), csubst (i, x, z))
end

