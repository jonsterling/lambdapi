use "TYPING.sig";

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

  exception hole

  exception unknown_identifier of syn.name
  exception illegal_application of syn.iterm * syn.cterm
  exception cannot_synthesize_type
  exception mismatched_type of syn.value * syn.value

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
    | syn.bound x      => raise cannot_synthesize_type
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

  and ctype (i, g, x, t) =
    case x of
      syn.inf e =>
        let
          val t' = itype (i, g, e)
        in
          raise hole
        end
    | _         => raise hole
  and isubst x = raise hole
  and csubst x = raise hole
end

