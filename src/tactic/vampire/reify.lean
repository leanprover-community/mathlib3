import tactic.vampire.form

namespace vampire

local notation `#`      := term.fn
local notation t `&t` s := term.tp t s
local notation t `&v` k := term.vp t k

local notation `$`      := atom.rl
local notation a `^t` t := atom.tp a t
local notation a `^v` t := atom.vp a t

local notation `-*`     := lit.atom ff
local notation `+*`     := lit.atom tt
local notation t `=*` s := lit.eq tt t s
local notation t `≠*` s := lit.eq ff t s

local notation `⟪` l `⟫`       := form.lit l
local notation p `∨*` q        := form.bin tt p q
local notation p `∧*` q        := form.bin ff p q
local notation `∃*`            := form.qua tt
local notation `∀*`            := form.qua ff

@[derive decidable_eq]
meta inductive preterm : Type
| var : bool → nat → preterm
| exp : expr → preterm
| app : preterm → preterm → preterm

meta def preterm.repr : preterm → string
| (preterm.var tt k) := "X" ++ k.to_subs
| (preterm.var ff k) := "S" ++ k.to_subs
| (preterm.exp x)    := (to_fmt x).to_string
| (preterm.app t s)  := "(" ++ t.repr ++ " " ++ s.repr ++ ")"

meta inductive preatom : Type
| rel : preterm → preatom
| eq  : preterm → preterm → preatom

meta def preatom.repr : preatom → string
| (preatom.rel t)  := t.repr
| (preatom.eq t s) := "(" ++ t.repr ++ " = " ++ s.repr ++ ")"

meta inductive preform : Type
| lit : bool → preatom → preform
| bin : bool → preform → preform → preform
| qua : bool → preform → preform

meta def preform.repr : preform → string
| (preform.lit tt a)   := a.repr
| (preform.lit ff a)   := "¬" ++ a.repr
| (preform.bin tt f g) := "(" ++ f.repr ++ " ∨ " ++ g.repr ++ ")"
| (preform.bin ff f g) := "(" ++ f.repr ++ " ∧ " ++ g.repr ++ ")"
| (preform.qua ff f) := "∀ " ++ f.repr
| (preform.qua tt f) := "∃ " ++ f.repr

meta instance preform.has_to_format : has_to_format preform :=
⟨λ x, x.repr⟩

open tactic expr

meta def to_preterm : expr → tactic preterm
| (var k) :=
  return (preterm.var tt k)
| (app x y) :=
  do t ← to_preterm x,
     s ← to_preterm y,
     return (preterm.app t s)
| x := return (preterm.exp x)

meta def to_preatom : expr → tactic preatom
| `(%%tx = %%sx) :=
  do t ← to_preterm tx,
     s ← to_preterm sx,
     return (preatom.eq t s)
| ax :=
  do t ← to_preterm ax,
     return (preatom.rel t)

meta def to_preform : expr → tactic preform
| `(%%px ∨ %%qx) :=
  do φ ← to_preform px,
     χ ← to_preform qx,
     return (preform.bin tt φ χ)
| `(%%px ∧ %%qx) :=
  do φ ← to_preform px,
     χ ← to_preform qx,
     return (preform.bin ff φ χ)
| (pi _ _ _ px) :=
  do φ ← to_preform px,
     return (preform.qua ff φ)
| `(Exists %%(expr.lam _ _ _ px)) :=
  do φ ← to_preform px,
     return (preform.qua tt φ)
| `(Exists %%prx) :=
  do φ ← to_preform (app (prx.lift_vars 0 1) (var 0)),
     return (preform.qua tt φ)
| `(¬ %%px) :=
  do a ← to_preatom px,
     return (preform.lit ff a)
| px        :=
  do a ← to_preatom px,
     return (preform.lit tt a)

meta def to_term : preterm → tactic term
| (preterm.var ff k) := return (# k)
| (preterm.var tt k) := failed
| (preterm.exp x)    := failed
| (preterm.app pt (preterm.var tt k)) :=
  do t ← to_term pt,
     return (t &v k)
| (preterm.app pt ps) :=
  do t ← to_term pt,
     s ← to_term ps,
     return (t &t s)

meta def to_exterm : preterm → tactic exterm
| (preterm.var tt k) := return (exterm.vr k)
| pt :=
  do t ← to_term pt,
     return (exterm.tm t)

meta def to_atom : preterm → tactic atom
| (preterm.var ff k) := return ($ k)
| (preterm.var tt k) := failed
| (preterm.exp x)    := failed
| (preterm.app pt (preterm.var tt k)) :=
  do a ← to_atom pt,
     return (a ^v k)
| (preterm.app pt ps) :=
  do a ← to_atom pt,
     t ← to_term ps,
     return (a ^t t)

meta def to_lit (b : bool) : preatom → tactic lit
| (preatom.rel pt) :=
  do a ← to_atom pt,
     return (lit.atom b a)
| (preatom.eq pt ps) :=
  do t ← to_exterm pt,
     s ← to_exterm ps,
     return (lit.eq b t s)

meta def to_form : preform → tactic form
| foo@(preform.lit b pa)   :=
  do l ← to_lit b pa,
     return (form.lit l)
| foo@(preform.bin b pf pg) :=
  do f ← to_form pf,
     g ← to_form pg,
     return (form.bin b f g)
| foo@(preform.qua b pf) :=
  do f ← to_form pf,
     return (form.qua b f)

meta def is_sym_type (b : bool) (αx : expr) : expr → bool
| `(%%x → %%y) := (x = αx) && (is_sym_type y)
| x            := if b then x = `(Prop) else x = αx

meta def preterm.to_expr : preterm → tactic expr
| (preterm.exp x) := return x
| (preterm.app t s) :=
  do x ← t.to_expr,
     y ← s.to_expr,
     return (app x y)
| _ := failed

meta def preterm.is_sym (b : bool) (αx) (t : preterm) : tactic unit :=
do tx ← t.to_expr >>= infer_type,
   if is_sym_type b αx tx
   then skip
   else failed

meta def preterm.get_sym (b : bool) (αx : expr) : preterm → tactic preterm
| r@(preterm.app t s) :=
  t.get_sym <|>
  s.get_sym <|>
  (r.is_sym b αx >> return r)
| t := t.is_sym b αx >> return t

meta def preatom.get_sym (b : bool) (αx : expr) : preatom → tactic preterm
| (preatom.rel t)  := t.get_sym b αx
| (preatom.eq t s) := t.get_sym b αx <|> s.get_sym b αx

meta def preform.get_sym (b : bool) (αx : expr) : preform → tactic preterm
| (preform.lit _ x)   := x.get_sym b αx
| (preform.bin _ x y) := x.get_sym <|> y.get_sym
| (preform.qua _ x)   := x.get_sym

meta def preterm.subst (s : preterm) (k : nat) : preterm → preterm
| t@(preterm.app t1 t2) :=
  if t = s
  then preterm.var ff k
  else preterm.app t1.subst t2.subst
| t :=
  if t = s
  then preterm.var ff k
  else t

meta def preatom.subst (r : preterm) (k : nat) : preatom → preatom
| (preatom.rel t)  := preatom.rel (preterm.subst r k t)
| (preatom.eq t s) := preatom.eq (preterm.subst r k t) (preterm.subst r k s)

meta def preform.subst (s : preterm) (k : nat) : preform → preform
| (preform.lit b l)   := preform.lit b (l.subst s k)
| (preform.bin b f g) := preform.bin b f.subst g.subst
| (preform.qua b f)   := preform.qua b f.subst

meta def abst (αx : expr) : bool → nat → preform → tactic preform
| b k f :=
  (do s ← f.get_sym b αx,
      abst b (k + 1) (f.subst s k)) <|>
  (if b then return f else abst tt 0 f)

meta def reify (αx : expr) : tactic form :=
do t ← target,
   x ← to_preform t,
   y ← abst αx ff 0 x,
   z ← to_form y,
   return z

end vampire
