import tactic.vampire.alt.form

namespace alt

local notation `#`      := term.fn
local notation t `&t` s := term.tp t s
local notation t `&v` k := term.vp t k

local notation `$`      := atom.rl
local notation a `^t` t := atom.tp a t
local notation a `^v` t := atom.vp a t

local notation `-*` := lit.neg
local notation `+*` := lit.pos

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

meta inductive preform : Type
| lit : bool → preterm → preform
| bin : bool → preform → preform → preform
| qua : bool → preform → preform

open tactic expr

meta def to_preterm : expr → tactic preterm
| (var k) :=
  return (preterm.var tt k)
| (app x y) :=
  do t ← to_preterm x,
     s ← to_preterm y,
     return (preterm.app t s)
| x := return (preterm.exp x)

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
  do t ← to_preterm px,
     return (preform.lit ff t)
| px        :=
  do t ← to_preterm px,
     return (preform.lit tt t)

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

meta def to_form : preform → tactic form
| (preform.lit b pt)   :=
  do a ← to_atom pt,
     return (form.lit (if b then +* a else -* a))
| (preform.bin b pf pg) :=
  do f ← to_form pf,
     g ← to_form pg,
     return (form.bin b f g)
| (preform.qua b pf) :=
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

meta def preform.subst (s : preterm) (k : nat) : preform → preform
| (preform.lit b t)   := preform.lit b (preterm.subst s k t)
| (preform.bin b f g) := preform.bin b f.subst g.subst
| (preform.qua b f)   := preform.qua b f.subst

meta def abst (αx : expr) : bool → nat → preform → tactic preform
| b k f :=
  (do s ← f.get_sym b αx,
      abst b (k + 1) (f.subst s k)) <|>
  (if b then return f else abst tt 0 f)

meta def reify (αx : expr) : tactic form :=
target >>= to_preform >>= abst αx ff 0 >>= to_form

end alt
