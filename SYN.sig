signature SYN =
sig
  datatype iterm
    = ann of cterm * cterm
    | bound of int
    | free of name
    | app of iterm * cterm
    | uni
    | pi of cterm * cterm
    | eq of cterm * cterm * cterm

  and cterm
    = inf of iterm
    | lam of cterm
    | refl of cterm * cterm

  and name
    = global of string
    | locl of int
    | quoted of int

  and value
    = vlam of value -> value
    | vuni
    | vpi of value * (value -> value)
    | vneutral of neutral
    | vrefl of value * value
    | veq of value * value * value

  and neutral
    = nfree of name
    | napp of neutral * value

  val vfree : name -> value
  val vapp : value * value -> value

  type ty = value
  type env = value list
  type 'a name_env = (name * 'a) list
  type ctx = ty name_env

  val lookup : name * 'a name_env -> 'a option

  exception vapp_impossible of value * value
end
