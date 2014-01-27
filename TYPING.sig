use "SYN.sig";

signature TYPING =
sig
  structure syn : SYN

  val itype : int * (syn.value syn.name_env * syn.ctx) * syn.iterm -> syn.ty
  val ctype : int * (syn.value syn.name_env * syn.ctx) * syn.cterm * syn.ty -> unit

  val isubst : int * syn.iterm * syn.iterm -> syn.iterm
  val csubst : int * syn.iterm * syn.cterm -> syn.cterm

  exception unknown_identifier of syn.name
  exception illegal_application of syn.iterm * syn.cterm
  exception cannot_synthesize_type
  exception mismatched_type of syn.value * (syn.value option)
end
