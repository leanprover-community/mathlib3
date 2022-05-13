/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import tactic.norm_num

/-!
# The `abel` tactic

Evaluate expressions in the language of additive, commutative monoids and groups.


-/

namespace tactic
namespace abel

/-- The `context` for a call to `abel`.

Stores a few options for this call, and caches some common subexpressions
such as typeclass instances and `0 : α`.
-/
meta structure context :=
(red : transparency)
(α : expr)
(univ : level)
(α0 : expr)
(is_group : bool)
(inst : expr)

/-- Populate a `context` object for evaluating `e`, up to reducibility level `red`. -/
meta def mk_context (red : transparency) (e : expr) : tactic context :=
do α ← infer_type e,
   c ← mk_app ``add_comm_monoid [α] >>= mk_instance,
   cg ← try_core (mk_app ``add_comm_group [α] >>= mk_instance),
   u ← mk_meta_univ,
   infer_type α >>= unify (expr.sort (level.succ u)),
   u ← get_univ_assignment u,
   α0 ← expr.of_nat α 0,
   match cg with
   | (some cg) := return ⟨red, α, u, α0, tt, cg⟩
   | _ := return ⟨red, α, u, α0, ff, c⟩
   end

/-- Apply the function `n : ∀ {α} [inst : add_whatever α], _` to the
implicit parameters in the context, and the given list of arguments. -/
meta def context.app (c : context) (n : name) (inst : expr) : list expr → expr :=
(@expr.const tt n [c.univ] c.α inst).mk_app

/-- Apply the function `n : ∀ {α} [inst α], _` to the implicit parameters in the
context, and the given list of arguments.

Compared to `context.app`, this takes the name of the typeclass, rather than an
inferred typeclass instance.
-/
meta def context.mk_app (c : context) (n inst : name) (l : list expr) : tactic expr :=
do m ← mk_instance ((expr.const inst [c.univ] : expr) c.α), return $ c.app n m l

/-- Add the letter "g" to the end of the name, e.g. turning `term` into `termg`.

This is used to choose between declarations taking `add_comm_monoid` and those
taking `add_comm_group` instances.
-/
meta def add_g : name → name
| (name.mk_string s p) := name.mk_string (s ++ "g") p
| n := n

/-- Apply the function `n : ∀ {α} [add_comm_{monoid,group} α]` to the given
list of arguments.

Will use the `add_comm_{monoid,group}` instance that has been cached in the context.
-/
meta def context.iapp (c : context) (n : name) : list expr → expr :=
c.app (if c.is_group then add_g n else n) c.inst

def term {α} [add_comm_monoid α] (n : ℕ) (x a : α) : α := n • x + a
def termg {α} [add_comm_group α] (n : ℤ) (x a : α) : α := n • x + a

/-- Evaluate a term with coefficient `n`, atom `x` and successor terms `a`. -/
meta def context.mk_term (c : context) (n x a : expr) : expr := c.iapp ``term [n, x, a]

/-- Interpret an integer as a coefficient to a term. -/
meta def context.int_to_expr (c : context) (n : ℤ) : tactic expr :=
expr.of_int (if c.is_group then `(ℤ) else `(ℕ)) n

meta inductive normal_expr : Type
| zero (e : expr) : normal_expr
| nterm (e : expr) (n : expr × ℤ) (x : expr) (a : normal_expr) : normal_expr

meta def normal_expr.e : normal_expr → expr
| (normal_expr.zero e) := e
| (normal_expr.nterm e _ _ _) := e

meta instance : has_coe normal_expr expr := ⟨normal_expr.e⟩
meta instance : has_coe_to_fun normal_expr (λ _, expr → expr) := ⟨λ e, ⇑(e : expr)⟩

meta def normal_expr.term' (c : context) (n : expr × ℤ) (x : expr) (a : normal_expr) :
  normal_expr :=
normal_expr.nterm (c.mk_term n.1 x a) n x a

meta def normal_expr.zero' (c : context) : normal_expr := normal_expr.zero c.α0

meta def normal_expr.to_list : normal_expr → list (ℤ × expr)
| (normal_expr.zero _) := []
| (normal_expr.nterm _ (_, n) x a) := (n, x) :: a.to_list

open normal_expr

meta def normal_expr.to_string (e : normal_expr) : string :=
" + ".intercalate $ (to_list e).map $
λ ⟨n, e⟩, to_string n ++ " • (" ++ to_string e ++ ")"

meta def normal_expr.pp (e : normal_expr) : tactic format :=
do l ← (to_list e).mmap (λ ⟨n, e⟩, do
  pe ← pp e, return (to_fmt n ++ " • (" ++ pe ++ ")")),
  return $ format.join $ l.intersperse ↑" + "

meta instance : has_to_tactic_format normal_expr := ⟨normal_expr.pp⟩

meta def normal_expr.refl_conv (e : normal_expr) : tactic (normal_expr × expr) :=
do p ← mk_eq_refl e, return (e, p)

theorem const_add_term {α} [add_comm_monoid α] (k n x a a') (h : k + a = a') :
  k + @term α _ n x a = term n x a' := by simp [h.symm, term]; ac_refl

theorem const_add_termg {α} [add_comm_group α] (k n x a a') (h : k + a = a') :
  k + @termg α _ n x a = termg n x a' := by simp [h.symm, termg]; ac_refl

theorem term_add_const {α} [add_comm_monoid α] (n x a k a') (h : a + k = a') :
  @term α _ n x a + k = term n x a' := by simp [h.symm, term, add_assoc]

theorem term_add_constg {α} [add_comm_group α] (n x a k a') (h : a + k = a') :
  @termg α _ n x a + k = termg n x a' := by simp [h.symm, termg, add_assoc]

theorem term_add_term {α} [add_comm_monoid α] (n₁ x a₁ n₂ a₂ n' a')
  (h₁ : n₁ + n₂ = n') (h₂ : a₁ + a₂ = a') :
  @term α _ n₁ x a₁ + @term α _ n₂ x a₂ = term n' x a' :=
by simp [h₁.symm, h₂.symm, term, add_nsmul]; ac_refl

theorem term_add_termg {α} [add_comm_group α] (n₁ x a₁ n₂ a₂ n' a')
  (h₁ : n₁ + n₂ = n') (h₂ : a₁ + a₂ = a') :
  @termg α _ n₁ x a₁ + @termg α _ n₂ x a₂ = termg n' x a' :=
by simp [h₁.symm, h₂.symm, termg, add_zsmul]; ac_refl

theorem zero_term {α} [add_comm_monoid α] (x a) : @term α _ 0 x a = a :=
by simp [term, zero_nsmul, one_nsmul]

theorem zero_termg {α} [add_comm_group α] (x a) : @termg α _ 0 x a = a :=
by simp [termg]

meta def eval_add (c : context) : normal_expr → normal_expr → tactic (normal_expr × expr)
| (zero _) e₂ := do
  p ← mk_app ``zero_add [e₂],
  return (e₂, p)
| e₁ (zero _) := do
  p ← mk_app ``add_zero [e₁],
  return (e₁, p)
| he₁@(nterm e₁ n₁ x₁ a₁) he₂@(nterm e₂ n₂ x₂ a₂) :=
  (do
    is_def_eq x₁ x₂ c.red,
    (n', h₁) ← mk_app ``has_add.add [n₁.1, n₂.1] >>= norm_num.eval_field,
    (a', h₂) ← eval_add a₁ a₂,
    let k := n₁.2 + n₂.2,
    let p₁ := c.iapp ``term_add_term [n₁.1, x₁, a₁, n₂.1, a₂, n', a', h₁, h₂],
    if k = 0 then do
      p ← mk_eq_trans p₁ (c.iapp ``zero_term [x₁, a']),
      return (a', p)
    else return (term' c (n', k) x₁ a', p₁))
  <|> if expr.lex_lt x₁ x₂ then do
    (a', h) ← eval_add a₁ he₂,
    return (term' c n₁ x₁ a', c.iapp ``term_add_const [n₁.1, x₁, a₁, e₂, a', h])
  else do
    (a', h) ← eval_add he₁ a₂,
    return (term' c n₂ x₂ a', c.iapp ``const_add_term [e₁, n₂.1, x₂, a₂, a', h])

theorem term_neg {α} [add_comm_group α] (n x a n' a')
  (h₁ : -n = n') (h₂ : -a = a') :
  -@termg α _ n x a = termg n' x a' :=
by simp [h₂.symm, h₁.symm, termg]; ac_refl

meta def eval_neg (c : context) : normal_expr → tactic (normal_expr × expr)
| (zero e) := do
  p ← c.mk_app ``neg_zero ``subtraction_monoid [],
  return (zero' c, p)
| (nterm e n x a) := do
  (n', h₁) ← mk_app ``has_neg.neg [n.1] >>= norm_num.eval_field,
  (a', h₂) ← eval_neg a,
  return (term' c (n', -n.2) x a',
    c.app ``term_neg c.inst [n.1, x, a, n', a', h₁, h₂])

def smul {α} [add_comm_monoid α] (n : ℕ) (x : α) : α := n • x
def smulg {α} [add_comm_group α] (n : ℤ) (x : α) : α := n • x

theorem zero_smul {α} [add_comm_monoid α] (c) : smul c (0 : α) = 0 :=
by simp [smul, nsmul_zero]

theorem zero_smulg {α} [add_comm_group α] (c) : smulg c (0 : α) = 0 :=
by simp [smulg, zsmul_zero]

theorem term_smul {α} [add_comm_monoid α] (c n x a n' a')
  (h₁ : c * n = n') (h₂ : smul c a = a') :
  smul c (@term α _ n x a) = term n' x a' :=
by simp [h₂.symm, h₁.symm, term, smul, nsmul_add, mul_nsmul]

theorem term_smulg {α} [add_comm_group α] (c n x a n' a')
  (h₁ : c * n = n') (h₂ : smulg c a = a') :
  smulg c (@termg α _ n x a) = termg n' x a' :=
by simp [h₂.symm, h₁.symm, termg, smulg, zsmul_add, mul_zsmul]

meta def eval_smul (c : context) (k : expr × ℤ) :
  normal_expr → tactic (normal_expr × expr)
| (zero _) := return (zero' c, c.iapp ``zero_smul [k.1])
| (nterm e n x a) := do
  (n', h₁) ← mk_app ``has_mul.mul [k.1, n.1] >>= norm_num.eval_field,
  (a', h₂) ← eval_smul a,
  return (term' c (n', k.2 * n.2) x a',
    c.iapp ``term_smul [k.1, n.1, x, a, n', a', h₁, h₂])

theorem term_atom {α} [add_comm_monoid α] (x : α) : x = term 1 x 0 :=
by simp [term]

theorem term_atomg {α} [add_comm_group α] (x : α) : x = termg 1 x 0 :=
by simp [termg]

meta def eval_atom (c : context) (e : expr) : tactic (normal_expr × expr) :=
do n1 ← c.int_to_expr 1,
   return (term' c (n1, 1) e (zero' c), c.iapp ``term_atom [e])

lemma unfold_sub {α} [subtraction_monoid α] (a b c : α) (h : a + -b = c) : a - b = c :=
by rw [sub_eq_add_neg, h]

theorem unfold_smul {α} [add_comm_monoid α] (n) (x y : α)
  (h : smul n x = y) : n • x = y := h

theorem unfold_smulg {α} [add_comm_group α] (n : ℕ) (x y : α)
  (h : smulg (int.of_nat n) x = y) : (n : ℤ) • x = y := h

theorem unfold_zsmul {α} [add_comm_group α] (n : ℤ) (x y : α)
  (h : smulg n x = y) : n • x = y := h

lemma subst_into_smul {α} [add_comm_monoid α]
  (l r tl tr t) (prl : l = tl) (prr : r = tr)
  (prt : @smul α _ tl tr = t) : smul l r = t :=
by simp [prl, prr, prt]

lemma subst_into_smulg {α} [add_comm_group α]
  (l r tl tr t) (prl : l = tl) (prr : r = tr)
  (prt : @smulg α _ tl tr = t) : smulg l r = t :=
by simp [prl, prr, prt]

lemma subst_into_smul_upcast {α} [add_comm_group α]
  (l r tl zl tr t) (prl₁ : l = tl) (prl₂ : ↑tl = zl) (prr : r = tr)
  (prt : @smulg α _ zl tr = t) : smul l r = t :=
by simp [← prt, prl₁, ← prl₂, prr, smul, smulg]

/-- Normalize a term `orig` of the form `smul e₁ e₂` or `smulg e₁ e₂`.
  Normalized terms use `smul` for monoids and `smulg` for groups,
  so there are actually four cases to handle:
  * Using `smul` in a monoid just simplifies the pieces using `subst_into_smul`
  * Using `smulg` in a group just simplifies the pieces using `subst_into_smulg`
  * Using `smul a b` in a group requires converting `a` from a nat to an int and
    then simplifying `smulg ↑a b` using `subst_into_smul_upcast`
  * Using `smulg` in a monoid is impossible (or at least out of scope),
    because you need a group argument to write a `smulg` term -/
meta def eval_smul' (c : context) (eval : expr → tactic (normal_expr × expr))
  (is_smulg : bool) (orig e₁ e₂ : expr) : tactic (normal_expr × expr) :=
do (e₁', p₁) ← norm_num.derive e₁ <|> refl_conv e₁,
  match if is_smulg then e₁'.to_int else coe <$> e₁'.to_nat with
  | some n := do
    (e₂', p₂) ← eval e₂,
    if c.is_group = is_smulg then do
      (e', p) ← eval_smul c (e₁', n) e₂',
      return (e', c.iapp ``subst_into_smul [e₁, e₂, e₁', e₂', e', p₁, p₂, p])
    else do
      guardb c.is_group,
      ic ← mk_instance_cache `(ℤ),
      nc ← mk_instance_cache `(ℕ),
      (ic, zl) ← ic.of_int n,
      (_, _, _, p₁') ← norm_num.prove_nat_uncast ic nc zl,
      (e', p) ← eval_smul c (zl, n) e₂',
      return (e', c.app ``subst_into_smul_upcast c.inst [e₁, e₂, e₁', zl, e₂', e', p₁, p₁', p₂, p])
  | none := eval_atom c orig
  end

meta def eval (c : context) : expr → tactic (normal_expr × expr)
| `(%%e₁ + %%e₂) := do
  (e₁', p₁) ← eval e₁,
  (e₂', p₂) ← eval e₂,
  (e', p') ← eval_add c e₁' e₂',
  p ← c.mk_app ``norm_num.subst_into_add ``has_add [e₁, e₂, e₁', e₂', e', p₁, p₂, p'],
  return (e', p)
| `(%%e₁ - %%e₂) := do
  e₂' ← mk_app ``has_neg.neg [e₂],
  e ← mk_app ``has_add.add [e₁, e₂'],
  (e', p) ← eval e,
  p' ← c.mk_app ``unfold_sub ``subtraction_monoid [e₁, e₂, e', p],
  return (e', p')
| `(- %%e) := do
  (e₁, p₁) ← eval e,
  (e₂, p₂) ← eval_neg c e₁,
  p ← c.mk_app ``norm_num.subst_into_neg ``has_neg [e, e₁, e₂, p₁, p₂],
  return (e₂, p)
| `(add_monoid.nsmul %%e₁ %%e₂) := do
  n ← if c.is_group then mk_app ``int.of_nat [e₁] else return e₁,
  (e', p) ← eval $ c.iapp ``smul [n, e₂],
  return (e', c.iapp ``unfold_smul [e₁, e₂, e', p])
| `(sub_neg_monoid.zsmul %%e₁ %%e₂) := do
  guardb c.is_group,
  (e', p) ← eval $ c.iapp ``smul [e₁, e₂],
  return (e', c.app ``unfold_zsmul c.inst [e₁, e₂, e', p])
| e@`(@has_scalar.smul nat _ add_monoid.has_scalar_nat %%e₁ %%e₂) :=
  eval_smul' c eval ff e e₁ e₂
| e@`(@has_scalar.smul int _ sub_neg_monoid.has_scalar_int %%e₁ %%e₂) :=
  eval_smul' c eval tt e e₁ e₂
| e@`(smul %%e₁ %%e₂) := eval_smul' c eval ff e e₁ e₂
| e@`(smulg %%e₁ %%e₂) := eval_smul' c eval tt e e₁ e₂
| e@`(@has_zero.zero _ _) := mcond (succeeds (is_def_eq e c.α0))
  (mk_eq_refl c.α0 >>= λ p, pure (zero' c, p))
  (eval_atom c e)
| e := eval_atom c e

meta def eval' (c : context) (e : expr) : tactic (expr × expr) :=
do (e', p) ← eval c e, return (e', p)

@[derive has_reflect]
inductive normalize_mode | raw | term

instance : inhabited normalize_mode := ⟨normalize_mode.term⟩

meta def normalize (red : transparency) (mode := normalize_mode.term) (e : expr) :
  tactic (expr × expr) := do
pow_lemma ← simp_lemmas.mk.add_simp ``pow_one,
let lemmas := match mode with
| normalize_mode.term :=
  [``term.equations._eqn_1, ``termg.equations._eqn_1, ``add_zero, ``one_nsmul, ``one_zsmul,
    ``zsmul_zero]
| _ := []
end,
lemmas ← lemmas.mfoldl simp_lemmas.add_simp simp_lemmas.mk,
(_, e', pr) ← ext_simplify_core () {}
  simp_lemmas.mk (λ _, failed) (λ _ _ _ _ e, do
    c ← mk_context red e,
    (new_e, pr) ← match mode with
    | normalize_mode.raw := eval' c
    | normalize_mode.term := trans_conv (eval' c)
                               (λ e, do (e', prf, _) ← simplify lemmas [] e, return (e', prf))
    end e,
    guard (¬ new_e =ₐ e),
    return ((), new_e, some pr, ff))
   (λ _ _ _ _ _, failed) `eq e,
return (e', pr)

end abel

namespace interactive
open tactic.abel

setup_tactic_parser

/-- Tactic for solving equations in the language of
*additive*, commutative monoids and groups.
This version of `abel` fails if the target is not an equality
that is provable by the axioms of commutative monoids/groups.

`abel1!` will use a more aggressive reducibility setting to identify atoms.
This can prove goals that `abel` cannot, but is more expensive.
-/
meta def abel1 (red : parse (tk "!")?) : tactic unit :=
do `(%%e₁ = %%e₂) ← target,
  c ← mk_context (if red.is_some then semireducible else reducible) e₁,
  (e₁', p₁) ← eval c e₁,
  (e₂', p₂) ← eval c e₂,
  is_def_eq e₁' e₂',
  p ← mk_eq_symm p₂ >>= mk_eq_trans p₁,
  tactic.exact p

meta def abel.mode : lean.parser abel.normalize_mode :=
with_desc "(raw|term)?" $
do mode ← ident?, match mode with
| none       := return abel.normalize_mode.term
| some `term := return abel.normalize_mode.term
| some `raw  := return abel.normalize_mode.raw
| _          := failed
end

/--
Evaluate expressions in the language of *additive*, commutative monoids and groups.
It attempts to prove the goal outright if there is no `at`
specifier and the target is an equality, but if this
fails, it falls back to rewriting all monoid expressions into a normal form.
If there is an `at` specifier, it rewrites the given target into a normal form.

`abel!` will use a more aggressive reducibility setting to identify atoms.
This can prove goals that `abel` cannot, but is more expensive.
```lean
example {α : Type*} {a b : α} [add_comm_monoid α] : a + (b + a) = a + a + b := by abel
example {α : Type*} {a b : α} [add_comm_group α] : (a + b) - ((b + a) + a) = -a := by abel
example {α : Type*} {a b : α} [add_comm_group α] (hyp : a + a - a = b - b) : a = 0 :=
by { abel at hyp, exact hyp }
example {α : Type*} {a b : α} [add_comm_group α] : (a + b) - (id a + b) = 0 := by abel!
```
-/
meta def abel (red : parse (tk "!")?) (SOP : parse abel.mode) (loc : parse location) :
  tactic unit :=
match loc with
| interactive.loc.ns [none] := abel1 red
| _ := failed
end <|>
do ns ← loc.get_locals,
   let red := if red.is_some then semireducible else reducible,
   tt ← tactic.replace_at (normalize red SOP) ns loc.include_goal
      | fail "abel failed to simplify",
   when loc.include_goal $ try tactic.reflexivity

add_tactic_doc
{ name        := "abel",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.abel],
  tags        := ["arithmetic", "decision procedure"] }

end interactive
end tactic
