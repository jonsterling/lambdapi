use "SYN.sig";

signature QUOTE =
sig
  structure syn : SYN
  val quote : int * syn.value -> syn.cterm
end
