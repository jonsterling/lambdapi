use "SYN.sig";

structure Syntax :> SYN =
struct
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
    | quote of int

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

  exception vapp_impossible of value * value

  fun vfree n = vneutral (nfree n)
  fun vapp (f, v) =
    case f of
      vlam f     => f v
    | vneutral n => vneutral (napp (n, v))
    | _          => raise vapp_impossible (f, v)

  type ty = value
  type env = value list
  type 'a name_env = (name * 'a) list
  type ctx = ty name_env

  fun lookup (x : name, g) =
    case g of
      []            => NONE
    | ((n, v) :: d) => if (x = n) then SOME v else lookup (x, d)

end
