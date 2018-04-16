/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Evaluate expressions in the language of (semi-)rings.
Based on http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf .
-/
import algebra.group_power tactic.norm_num

universes u v w
open tactic

def horner {α} [comm_semiring α] (a x : α) (n : ℕ) (b : α) := a * x ^ n + b

namespace tactic
namespace ring

meta structure cache :=
(α : expr)
(univ : level)
(comm_semiring_inst : expr)

meta def mk_cache (e : expr) : tactic cache :=
do α ← infer_type e,
   c ← mk_app ``comm_semiring [α] >>= mk_instance,
   u ← mk_meta_univ,
   infer_type α >>= unify (expr.sort (level.succ u)),
   u ← get_univ_assignment u,
   return ⟨α, u, c⟩

meta def cache.cs_app (c : cache) (n : name) : list expr → expr :=
(@expr.const tt n [c.univ] c.α c.comm_semiring_inst).mk_app

meta inductive destruct_ty : Type
| const : ℚ → destruct_ty
| xadd : expr → expr → expr → ℕ → expr → destruct_ty
open destruct_ty

meta def destruct (e : expr) : option destruct_ty :=
match expr.to_rat e with
| some n := some $ const n
| none := match e with
  | `(horner %%a %%x %%n %%b) :=
    do n' ← expr.to_nat n,
       some (xadd a x n n' b)
  | _ := none
  end
end

meta def normal_form_to_string : expr → string
| e := match destruct e with
  | some (const n) := to_string n
  | some (xadd a x _ n b) :=
    "(" ++ normal_form_to_string a ++ ") * (" ++ to_string x ++ ")^"
        ++ to_string n ++ " + " ++ normal_form_to_string b
  | none := to_string e
  end

theorem zero_horner {α} [comm_semiring α] (x n b) :
  @horner α _ 0 x n b = b :=
by simp [horner]

theorem horner_horner {α} [comm_semiring α] (a₁ x n₁ n₂ b n')
  (h : n₁ + n₂ = n') :
  @horner α _ (horner a₁ x n₁ 0) x n₂ b = horner a₁ x n' b :=
by simp [h.symm, horner, pow_add, mul_assoc]

meta def refl_conv (e : expr) : tactic (expr × expr) :=
do p ← mk_eq_refl e, return (e, p)

meta def trans_conv (t₁ t₂ : expr → tactic (expr × expr)) (e : expr) :
  tactic (expr × expr) :=
(do (e₁, p₁) ← t₁ e,
  (do (e₂, p₂) ← t₂ e₁,
    p ← mk_eq_trans p₁ p₂, return (e₂, p)) <|>
  return (e₁, p₁)) <|> t₂ e

meta def eval_horner (c : cache) (a x n b : expr) : tactic (expr × expr) :=
do d ← destruct a, match d with
| const q := if q = 0 then
    return (b, c.cs_app ``zero_horner [x, n, b])
  else refl_conv $ c.cs_app ``horner [a, x, n, b]
| xadd a₁ x₁ n₁ _ b₁ :=
  if x₁ = x ∧ b₁.to_nat = some 0 then do
    (n', h) ← mk_app ``has_add.add [n₁, n] >>= norm_num,
    return (c.cs_app ``horner [a₁, x, n', b],
      c.cs_app ``horner_horner [a₁, x, n₁, n, b, n', h])
  else refl_conv $ c.cs_app ``horner [a, x, n, b]
end

theorem const_add_horner {α} [comm_semiring α] (k a x n b b') (h : k + b = b') :
  k + @horner α _ a x n b = horner a x n b' :=
by simp [h.symm, horner]

theorem horner_add_const {α} [comm_semiring α] (a x n b k b') (h : b + k = b') :
  @horner α _ a x n b + k = horner a x n b' :=
by simp [h.symm, horner]

theorem horner_add_horner_lt {α} [comm_semiring α] (a₁ x n₁ b₁ a₂ n₂ b₂ k b')
  (h₁ : n₁ + k = n₂) (h₂ : b₁ + b₂ = b') :
  @horner α _ a₁ x n₁ b₁ + horner a₂ x n₂ b₂ = horner (horner a₂ x k a₁) x n₁ b' :=
by simp [h₂.symm, h₁.symm, horner, pow_add, mul_add, mul_comm, mul_left_comm]

theorem horner_add_horner_gt {α} [comm_semiring α] (a₁ x n₁ b₁ a₂ n₂ b₂ k b')
  (h₁ : n₂ + k = n₁) (h₂ : b₁ + b₂ = b') :
  @horner α _ a₁ x n₁ b₁ + horner a₂ x n₂ b₂ = horner (horner a₁ x k a₂) x n₂ b' :=
by simp [h₂.symm, h₁.symm, horner, pow_add, mul_add, mul_comm, mul_left_comm]

theorem horner_add_horner_eq {α} [comm_semiring α] (a₁ x n b₁ a₂ b₂ a' b' t)
  (h₁ : a₁ + a₂ = a') (h₂ : b₁ + b₂ = b') (h₃ : horner a' x n b' = t) :
  @horner α _ a₁ x n b₁ + horner a₂ x n b₂ = t :=
by simp [h₃.symm, h₂.symm, h₁.symm, horner, add_mul, mul_comm]

meta def eval_add (c : cache) : expr → expr → tactic (expr × expr)
| e₁ e₂ := do d₁ ← destruct e₁, d₂ ← destruct e₂,
match d₁, d₂ with
| const n₁, const n₂ :=
  mk_app ``has_add.add [e₁, e₂] >>= norm_num
| const k, xadd a x n _ b :=
  if k = 0 then do
    p ← mk_app ``zero_add [e₂],
    return (e₂, p) else do
  (b', h) ← eval_add e₁ b,
  return (c.cs_app ``horner [a, x, n, b'],
    c.cs_app ``const_add_horner [e₁, a, x, n, b, b', h])
| xadd a x n _ b, const k :=
  if k = 0 then do
    p ← mk_app ``add_zero [e₁],
    return (e₁, p) else do
  (b', h) ← eval_add b e₂,
  return (c.cs_app ``horner [a, x, n, b'],
    c.cs_app ``horner_add_const [a, x, n, b, e₂, b', h])
| xadd a₁ x₁ en₁ n₁ b₁, xadd a₂ x₂ en₂ n₂ b₂ :=
  if expr.lex_lt x₁ x₂ then do
    (b', h) ← eval_add b₁ e₂,
    return (c.cs_app ``horner [a₁, x₁, en₁, b'],
      c.cs_app ``horner_add_const [a₁, x₁, en₁, b₁, e₂, b', h])
  else if x₁ ≠ x₂ then do
    (b', h) ← eval_add e₁ b₂,
    return (c.cs_app ``horner [a₂, x₂, en₂, b'],
      c.cs_app ``const_add_horner [e₁, a₂, x₂, en₂, b₂, b', h])
  else if n₁ < n₂ then do
    k ← expr.of_nat (expr.const `nat []) (n₂ - n₁),
    (_, h₁) ← mk_app ``has_add.add [en₁, k] >>= norm_num,
    (b', h₂) ← eval_add b₁ b₂,
    return (c.cs_app ``horner [c.cs_app ``horner [a₂, x₁, k, a₁], x₁, en₁, b'],
      c.cs_app ``horner_add_horner_lt [a₁, x₁, en₁, b₁, a₂, en₂, b₂, k, b', h₁, h₂])
  else if n₁ ≠ n₂ then do
    k ← expr.of_nat (expr.const `nat []) (n₁ - n₂),
    (_, h₁) ← mk_app ``has_add.add [en₂, k] >>= norm_num,
    (b', h₂) ← eval_add b₁ b₂,
    return (c.cs_app ``horner [c.cs_app ``horner [a₁, x₁, k, a₂], x₁, en₂, b'],
      c.cs_app ``horner_add_horner_gt [a₁, x₁, en₁, b₁, a₂, en₂, b₂, k, b', h₁, h₂])
  else do
    (a', h₁) ← eval_add a₁ a₂,
    (b', h₂) ← eval_add b₁ b₂,
    (t, h₃) ← eval_horner c a' x₁ en₁ b',
    return (t, c.cs_app ``horner_add_horner_eq
      [a₁, x₁, en₁, b₁, a₂, b₂, a', b', t, h₁, h₂, h₃])
end

theorem horner_neg {α} [comm_ring α] (a x n b a' b')
  (h₁ : -a = a') (h₂ : -b = b') :
  -@horner α _ a x n b = horner a' x n b' :=
by simp [h₂.symm, h₁.symm, horner]

meta def eval_neg (c : cache) : expr → tactic (expr × expr) | e :=
do d ← destruct e, match d with
| const _ :=
  mk_app ``has_neg.neg [e] >>= norm_num
| xadd a x n _ b := do
  (a', h₁) ← eval_neg a,
  (b', h₂) ← eval_neg b,
  p ← mk_app ``horner_neg [a, x, n, b, a', b', h₁, h₂],
  return (c.cs_app ``horner [a', x, n, b'], p)
end

theorem horner_const_mul {α} [comm_semiring α] (c a x n b a' b')
  (h₁ : c * a = a') (h₂ : c * b = b') :
  c * @horner α _ a x n b = horner a' x n b' :=
by simp [h₂.symm, h₁.symm, horner, mul_add, mul_assoc]

theorem horner_mul_const {α} [comm_semiring α] (a x n b c a' b')
  (h₁ : a * c = a') (h₂ : b * c = b') :
  @horner α _ a x n b * c = horner a' x n b' :=
by simp [h₂.symm, h₁.symm, horner, add_mul, mul_right_comm]

meta def eval_const_mul (c : cache) (k : expr) : expr → tactic (expr × expr) | e :=
do d ← destruct e, match d with
| const _ :=
  mk_app ``has_mul.mul [k, e] >>= norm_num
| xadd a x n _ b := do
  (a', h₁) ← eval_const_mul a,
  (b', h₂) ← eval_const_mul b,
  return (c.cs_app ``horner [a', x, n, b'],
    c.cs_app ``horner_const_mul [k, a, x, n, b, a', b', h₁, h₂])
end

theorem horner_mul_horner_zero {α} [comm_semiring α] (a₁ x n₁ b₁ a₂ n₂ aa t)
  (h₁ : @horner α _ a₁ x n₁ b₁ * a₂ = aa)
  (h₂ : horner aa x n₂ 0 = t) :
  horner a₁ x n₁ b₁ * horner a₂ x n₂ 0 = t :=
by rw [← h₂, ← h₁];
   simp [horner, mul_add, mul_comm, mul_left_comm, mul_assoc]

theorem horner_mul_horner {α} [comm_semiring α]
  (a₁ x n₁ b₁ a₂ n₂ b₂ aa haa ab bb t)
  (h₁ : @horner α _ a₁ x n₁ b₁ * a₂ = aa)
  (h₂ : horner aa x n₂ 0 = haa)
  (h₃ : a₁ * b₂ = ab) (h₄ : b₁ * b₂ = bb)
  (H : haa + horner ab x n₁ bb = t) :
  horner a₁ x n₁ b₁ * horner a₂ x n₂ b₂ = t :=
by rw [← H, ← h₂, ← h₁, ← h₃, ← h₄];
   simp [horner, mul_add, mul_comm, mul_left_comm, mul_assoc]

meta def eval_mul (c : cache) : expr → expr → tactic (expr × expr)
| e₁ e₂ := do d₁ ← destruct e₁, d₂ ← destruct e₂,
match d₁, d₂ with
| const n₁, const n₂ :=
  mk_app ``has_mul.mul [e₁, e₂] >>= norm_num
| const n₁, _ :=
  if n₁ = 0 then do
    α0 ← expr.of_nat c.α 0,
    p ← mk_app ``zero_mul [e₂],
    return (α0, p) else
  if n₁ = 1 then do
    p ← mk_app ``one_mul [e₂],
    return (e₂, p) else
  eval_const_mul c e₁ e₂
| _, const _ := do
  p₁ ← mk_app ``mul_comm [e₁, e₂],
  (e', p₂) ← eval_mul e₂ e₁,
  p ← mk_eq_trans p₁ p₂, return (e', p)
| xadd a₁ x₁ en₁ n₁ b₁, xadd a₂ x₂ en₂ n₂ b₂ :=
  if expr.lex_lt x₁ x₂ then do
    (a', h₁) ← eval_mul a₁ e₂,
    (b', h₂) ← eval_mul b₁ e₂,
    return (c.cs_app ``horner [a', x₁, en₁, b'],
      c.cs_app ``horner_mul_const [a₁, x₁, en₁, b₁, e₂, a', b', h₁, h₂])
  else if x₁ ≠ x₂ then do
    (a', h₁) ← eval_mul e₁ a₂,
    (b', h₂) ← eval_mul e₁ b₂,
    return (c.cs_app ``horner [a', x₂, en₂, b'],
      c.cs_app ``horner_const_mul [e₁, a₂, x₂, en₂, b₂, a', b', h₁, h₂])
  else do
    (aa, h₁) ← eval_mul e₁ a₂,
    α0 ← expr.of_nat c.α 0,
    (haa, h₂) ← eval_horner c aa x₁ en₂ α0,
    if b₂.to_nat = some 0 then do
      return (haa, c.cs_app ``horner_mul_horner_zero
        [a₁, x₁, en₁, b₁, a₂, en₂, aa, haa, h₁, h₂])
    else do
      (ab, h₃) ← eval_mul a₁ b₂,
      (bb, h₄) ← eval_mul b₁ b₂,
      (t, H) ← eval_add c haa (c.cs_app ``horner [ab, x₁, en₁, bb]),
      return (t, c.cs_app ``horner_mul_horner
        [a₁, x₁, en₁, b₁, a₂, en₂, b₂, aa, haa, ab, bb, t, h₁, h₂, h₃, h₄, H])
end

theorem horner_pow {α} [comm_semiring α] (a x n m n' a')
  (h₁ : n * m = n') (h₂ : a ^ m = a') :
  @horner α _ a x n 0 ^ m = horner a' x n' 0 :=
by simp [h₁.symm, h₂.symm, horner, mul_pow, pow_mul]

meta def eval_pow (c : cache) : expr → nat → tactic (expr × expr)
| e 0 := do
  α1 ← expr.of_nat c.α 1,
  p ← mk_app ``pow_zero [e],
  return (α1, p)
| e 1 := do
  p ← mk_app ``pow_one [e],
  return (e, p)
| e m := do d ← destruct e,
  let N : expr := expr.const `nat [],
  match d with
  | const _ := do
    e₂ ← expr.of_nat N m,
    mk_app ``monoid.pow [e, e₂] >>= norm_num.derive
  | xadd a x n _ b := match b.to_nat with
    | some 0 := do
      e₂ ← expr.of_nat N m,
      (n', h₁) ← mk_app ``has_mul.mul [n, e₂] >>= norm_num,
      (a', h₂) ← eval_pow a m,
      α0 ← expr.of_nat c.α 0,
      return (c.cs_app ``horner [a', x, n', α0],
        c.cs_app ``horner_pow [a, x, n, e₂, n', a', h₁, h₂])
    | _ := do
      e₂ ← expr.of_nat N (m-1),
      l ← mk_app ``monoid.pow [e, e₂],
      (tl, hl) ← eval_pow e (m-1),
      (t, p₂) ← eval_mul c tl e,
      hr ← mk_eq_refl e,
      p₂ ← mk_app ``norm_num.subst_into_prod [l, e, tl, e, t, hl, hr, p₂],
      p₁ ← mk_app ``pow_succ' [e, e₂],
      p ← mk_eq_trans p₁ p₂,
      return (t, p)
    end
  end

theorem horner_atom {α} [comm_semiring α] (x : α) : x = horner 1 x 1 0 :=
by simp [horner]

lemma subst_into_neg {α} [has_neg α] (a ta t : α) (pra : a = ta) (prt : -ta = t) : -a = t :=
by simp [pra, prt]

meta def eval_atom (c : cache) (e : expr) : tactic (expr × expr) :=
do α0 ← expr.of_nat c.α 0,
   α1 ← expr.of_nat c.α 1,
   n1 ← expr.of_nat (expr.const `nat []) 1,
   return (c.cs_app ``horner [α1, e, n1, α0], c.cs_app ``horner_atom [e])

lemma subst_into_pow {α} [monoid α] (l r tl tr t)
  (prl : (l : α) = tl) (prr : (r : ℕ) = tr) (prt : tl ^ tr = t) : l ^ r = t :=
by simp [prl, prr, prt]

meta def eval (c : cache) : expr → tactic (expr × expr)
| `(%%e₁ + %%e₂) := do
  (e₁', p₁) ← eval e₁,
  (e₂', p₂) ← eval e₂,
  (e', p') ← eval_add c e₁' e₂',
  p ← mk_app ``norm_num.subst_into_sum [e₁, e₂, e₁', e₂', e', p₁, p₂, p'],
  return (e', p)
| `(%%e₁ - %%e₂) := do
  e₂' ← mk_app ``has_neg.neg [e₂],
  mk_app ``has_add.add [e₁, e₂'] >>= eval
| `(- %%e) := do
  (e₁, p₁) ← eval e,
  (e₂, p₂) ← eval_neg c e₁,
  p ← mk_app ``subst_into_neg [e, e₁, e₂, p₁, p₂],
  return (e₂, p)
| `(%%e₁ * %%e₂) := do
  (e₁', p₁) ← eval e₁,
  (e₂', p₂) ← eval e₂,
  (e', p') ← eval_mul c e₁' e₂',
  p ← mk_app ``norm_num.subst_into_prod [e₁, e₂, e₁', e₂', e', p₁, p₂, p'],
  return (e', p)
| e@`(has_inv.inv %%_) := (do
    (e', p) ← norm_num.derive e,
    e'.to_rat,
    return (e', p)) <|> eval_atom c e
| e@`(%%e₁ / %%e₂) := do
  e₂' ← mk_app ``has_inv.inv [e₂],
  mk_app ``has_mul.mul [e₁, e₂'] >>= eval
| e@`(%%e₁ ^ %%e₂) := do
  (e₂', p₂) ← eval e₂,
  match e₂'.to_nat with
  | none := eval_atom c e
  | some k := do
    (e₁', p₁) ← eval e₁,
    (e', p') ← eval_pow c e₁' k,
    p ← mk_app ``subst_into_pow [e₁, e₂, e₁', e₂', e', p₁, p₂, p'],
    return (e', p)
  end
| e := match e.to_nat with
  | some _ := refl_conv e
  | none := eval_atom c e
  end

theorem horner_def' {α} [comm_semiring α] (a x n b) : @horner α _ a x n b = x ^ n * a + b :=
by simp [horner, mul_comm]

theorem mul_assoc_rev {α} [semigroup α] (a b c : α) : a * (b * c) = a * b * c :=
by simp [mul_assoc]

theorem pow_add_rev {α} [monoid α] (a b : α) (m n : ℕ) : a ^ m * a ^ n = a ^ (m + n) :=
by simp [pow_add]

theorem pow_add_rev_right {α} [monoid α] (a b : α) (m n : ℕ) : b * a ^ m * a ^ n = b * a ^ (m + n) :=
by simp [pow_add, mul_assoc]

theorem add_neg_eq_sub {α : Type u} [add_group α] (a b : α) : a + -b = a - b := rfl

@[derive has_reflect]
inductive normalize_mode | raw | SOP | horner

meta def normalize (mode := normalize_mode.horner) (e : expr) : tactic (expr × expr) := do
pow_lemma ← simp_lemmas.mk.add_simp ``pow_one,
let lemmas := match mode with
| normalize_mode.SOP :=
  [``horner_def', ``add_zero, ``mul_one, ``mul_add, ``mul_sub,
   ``mul_assoc_rev, ``pow_add_rev, ``pow_add_rev_right,
   ``mul_neg_eq_neg_mul_symm, ``add_neg_eq_sub]
| normalize_mode.horner :=
  [``horner.equations._eqn_1, ``add_zero, ``one_mul, ``pow_one,
   ``neg_mul_eq_neg_mul_symm, ``add_neg_eq_sub]
| _ := []
end,
lemmas ← lemmas.mfoldl simp_lemmas.add_simp simp_lemmas.mk,
(_, e', pr) ← ext_simplify_core () {}
  simp_lemmas.mk (λ _, failed) (λ _ _ _ _ e, do
    c ← mk_cache e,
    (new_e, pr) ← match mode with
    | normalize_mode.raw := eval c
    | normalize_mode.horner := trans_conv (eval c) (simplify lemmas [])
    | normalize_mode.SOP :=
      trans_conv (eval c) $
      trans_conv (simplify lemmas []) $
      simp_bottom_up' (λ e, norm_num e <|> pow_lemma.rewrite e)
    end e,
    guard (¬ new_e =ₐ e),
    return ((), new_e, some pr, ff))
   (λ _ _ _ _ _, failed) `eq e,
return (e', pr)

end ring

namespace interactive
open interactive interactive.types lean.parser
open tactic.ring

local postfix `?`:9001 := optional

/-- Tactic for solving equations in the language of rings.
  This version of `ring` fails if the target is not an equality
  that is provable by the axioms of commutative (semi)rings. -/
meta def ring1 : tactic unit :=
do `(%%e₁ = %%e₂) ← target,
  c ← mk_cache e₁,
  (e₁', p₁) ← eval c e₁,
  (e₂', p₂) ← eval c e₂,
  is_def_eq e₁' e₂',
  p ← mk_eq_symm p₂ >>= mk_eq_trans p₁,
  tactic.exact p

meta def ring.mode : lean.parser ring.normalize_mode :=
with_desc "(SOP|raw|horner)?" $
do mode ← ident?, match mode with
| none         := return ring.normalize_mode.horner
| some `horner := return ring.normalize_mode.horner
| some `SOP    := return ring.normalize_mode.SOP
| some `raw    := return ring.normalize_mode.raw
| _            := failed
end

/-- Tactic for solving equations in the language of rings.
  Attempts to prove the goal outright if there is no `at`
  specifier and the target is an equality, but if this
  fails it falls back to rewriting all ring expressions
  into a normal form. When writing a normal form,
  `ring SOP` will use sum-of-products form instead of horner form. -/
meta def ring (SOP : parse ring.mode) (loc : parse location) : tactic unit :=
match loc with
| interactive.loc.ns [none] := ring1
| _ := failed
end <|>
do ns ← loc.get_locals,
   tt ← tactic.replace_at (normalize SOP) ns loc.include_goal
      | fail "ring failed to simplify",
   when loc.include_goal $ try tactic.reflexivity

end interactive
end tactic

-- TODO(Mario): fix
-- example (x : ℤ) : x^3 + x^2 + x = x^3 + (x^2 + x) := by ring