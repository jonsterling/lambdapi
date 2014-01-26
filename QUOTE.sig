use "SYN.sig";

signature QUOTE =
sig
  structure syn : SYN

  val quote        : int * syn.value -> syn.cterm
  val neutralQuote : int * syn.neutral -> syn.iterm
  val boundFree    : int * syn.name -> syn.iterm
end
