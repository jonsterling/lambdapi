use "SYN.sig";

signature EVAL =
sig
  structure syn : SYN

  type 't evaluator = 't * (syn.value syn.name_env * syn.env) -> syn.value
  val ceval : syn.cterm evaluator
  val ieval : syn.iterm evaluator
end
