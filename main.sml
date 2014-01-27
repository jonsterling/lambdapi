use "syntax.sml";
use "quote.fun";
use "eval.fun";
use "typing.fun";

structure deps =
struct
  structure syn = Syntax
  structure quote = Quotation(syn)
  structure eval = Evaluation(syn)
end

structure typing = Typing(deps)


