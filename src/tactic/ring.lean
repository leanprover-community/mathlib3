/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Evaluate expressions in the language of commutative (semi)rings.
Based on http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf .
-/
import algebra.group_power tactic.norm_num
import tactic.converter.interactive

namespace tactic
namespace ring

def horner {α} [comm_semiring α] (a x : α) (n : ℕ) (b : α) := a * x ^ n + b

meta structure cache :=
(α : expr)
(univ : level)
(comm_semiring_inst : expr)
(red : transparency)

meta def ring_m (α : Type) : Type :=
reader_t cache (state_t (buffer expr) tactic) α

meta instance : monad ring_m := by dunfold ring_m; apply_instance
meta instance : alternative ring_m := by dunfold ring_m; apply_instance

meta def get_cache : ring_m cache := reader_t.read

meta def get_atom (n : ℕ) : ring_m expr :=
reader_t.lift $ (λ es : buffer expr, es.read' n) <$> state_t.get

meta def get_transparency : ring_m transparency :=
cache.red <$> get_cache

meta def add_atom (e : expr) : ring_m ℕ :=
do red ← get_transparency,
reader_t.lift ⟨λ es, (do
  n ← es.iterate failed (λ n e' t, t <|> (is_def_eq e e' red $> n)),
  return (n, es)) <|> return (es.size, es.push_back e)⟩

meta def lift {α} (m : tactic α) : ring_m α :=
reader_t.lift (state_t.lift m)

meta def ring_m.run (red : transparency) (e : expr) {α} (m : ring_m α) : tactic α :=
do α ← infer_type e,
   c ← mk_app ``comm_semiring [α] >>= mk_instance,
   u ← mk_meta_univ,
   infer_type α >>= unify (expr.sort (level.succ u)),
   u ← get_univ_assignment u,
   prod.fst <$> state_t.run (reader_t.run m ⟨α, u, c, red⟩) mk_buffer

meta def cache.cs_app (c : cache) (n : name) : list expr → expr :=
(@expr.const tt n [c.univ] c.α c.comm_semiring_inst).mk_app

meta def ring_m.mk_app (n inst : name) (l : list expr) : ring_m expr :=
do c ← get_cache,
   m ← lift $ mk_instance ((expr.const inst [c.univ] : expr) c.α),
   return $ (@expr.const tt n [c.univ] c.α m).mk_app l

meta inductive horner_expr : Type
| const (e : expr) : horner_expr
| xadd (e : expr) (a : horner_expr) (x : expr × ℕ) (n : expr × ℕ) (b : horner_expr) : horner_expr

meta def horner_expr.e : horner_expr → expr
| (horner_expr.const e) := e
| (horner_expr.xadd e _ _ _ _) := e

meta instance : has_coe horner_expr expr := ⟨horner_expr.e⟩

meta def horner_expr.xadd' (c : cache) (a : horner_expr)
  (x : expr × ℕ) (n : expr × ℕ) (b : horner_expr) : horner_expr :=
horner_expr.xadd (c.cs_app ``horner [a, x.1, n.1, b]) a x n b

open horner_expr

meta def horner_expr.to_string : horner_expr → string
| (const e) := to_string e
| (xadd e a x (_, n) b) :=
    "(" ++ a.to_string ++ ") * (" ++ to_string x ++ ")^"
        ++ to_string n ++ " + " ++ b.to_string

meta def horner_expr.pp : horner_expr → tactic format
| (const e) := pp e
| (xadd e a x (_, n) b) := do
  pa ← a.pp, pb ← b.pp, px ← pp x,
  return $ "(" ++ pa ++ ") * (" ++ px ++ ")^" ++ to_string n ++ " + " ++ pb

meta instance : has_to_tactic_format horner_expr := ⟨horner_expr.pp⟩

meta def horner_expr.refl_conv (e : horner_expr) : ring_m (horner_expr × expr) :=
do p ← lift $ mk_eq_refl e, return (e, p)

theorem zero_horner {α} [comm_semiring α] (x n b) :
  @horner α _ 0 x n b = b :=
by simp [horner]

theorem horner_horner {α} [comm_semiring α] (a₁ x n₁ n₂ b n')
  (h : n₁ + n₂ = n') :
  @horner α _ (horner a₁ x n₁ 0) x n₂ b = horner a₁ x n' b :=
by simp [h.symm, horner, pow_add, mul_assoc]

meta def eval_horner : horner_expr → expr × ℕ → expr × ℕ → horner_expr → ring_m (horner_expr × expr)
| ha@(const a) x n b := do
  c ← get_cache,
  if a.to_nat = some 0 then
    return (b, c.cs_app ``zero_horner [x.1, n.1, b])
  else (xadd' c ha x n b).refl_conv
| ha@(xadd a a₁ x₁ n₁ b₁) x n b := do
  c ← get_cache,
  if x₁.2 = x.2 ∧ b₁.e.to_nat = some 0 then do
    (n', h) ← lift $ mk_app ``has_add.add [n₁.1, n.1] >>= norm_num,
    return (xadd' c a₁ x (n', n₁.2 + n.2) b,
      c.cs_app ``horner_horner [a₁, x.1, n₁.1, n.1, b, n', h])
  else (xadd' c ha x n b).refl_conv

theorem const_add_horner {α} [comm_semiring α] (k a x n b b') (h : k + b = b') :
  k + @horner α _ a x n b = horner a x n b' :=
by simp [h.symm, horner]

theorem horner_add_const {α} [comm_semiring α] (a x n b k b') (h : b + k = b') :
  @horner α _ a x n b + k = horner a x n b' :=
by simp [h.symm, horner]

theorem horner_add_horner_lt {α} [comm_semiring α] (a₁ x n₁ b₁ a₂ n₂ b₂ k a' b')
  (h₁ : n₁ + k = n₂) (h₂ : (a₁ + horner a₂ x k 0 : α) = a') (h₃ : b₁ + b₂ = b') :
  @horner α _ a₁ x n₁ b₁ + horner a₂ x n₂ b₂ = horner a' x n₁ b' :=
by simp [h₂.symm, h₃.symm, h₁.symm, horner, pow_add, mul_add, mul_comm, mul_left_comm]

theorem horner_add_horner_gt {α} [comm_semiring α] (a₁ x n₁ b₁ a₂ n₂ b₂ k a' b')
  (h₁ : n₂ + k = n₁) (h₂ : (horner a₁ x k 0 + a₂ : α) = a') (h₃ : b₁ + b₂ = b') :
  @horner α _ a₁ x n₁ b₁ + horner a₂ x n₂ b₂ = horner a' x n₂ b' :=
by simp [h₂.symm, h₃.symm, h₁.symm, horner, pow_add, mul_add, mul_comm, mul_left_comm]

theorem horner_add_horner_eq {α} [comm_semiring α] (a₁ x n b₁ a₂ b₂ a' b' t)
  (h₁ : a₁ + a₂ = a') (h₂ : b₁ + b₂ = b') (h₃ : horner a' x n b' = t) :
  @horner α _ a₁ x n b₁ + horner a₂ x n b₂ = t :=
by simp [h₃.symm, h₂.symm, h₁.symm, horner, add_mul, mul_comm]

meta def eval_add : horner_expr → horner_expr → ring_m (horner_expr × expr)
| (const e₁) (const e₂) := do
  (e, p) ← lift $ mk_app ``has_add.add [e₁, e₂] >>= norm_num,
  return (const e, p)
| he₁@(const e₁) he₂@(xadd e₂ a x n b) := do
  c ← get_cache,
  if e₁.to_nat = some 0 then do
    p ← lift $ mk_app ``zero_add [e₂],
    return (he₂, p)
  else do
    (b', h) ← eval_add he₁ b,
    return (xadd' c a x n b',
      c.cs_app ``const_add_horner [e₁, a, x.1, n.1, b, b', h])
| he₁@(xadd e₁ a x n b) he₂@(const e₂) := do
  c ← get_cache,
  if e₂.to_nat = some 0 then do
    p ← lift $ mk_app ``add_zero [e₁],
    return (he₁, p)
  else do
    (b', h) ← eval_add b he₂,
    return (xadd' c a x n b',
      c.cs_app ``horner_add_const [a, x.1, n.1, b, e₂, b', h])
| he₁@(xadd e₁ a₁ x₁ n₁ b₁) he₂@(xadd e₂ a₂ x₂ n₂ b₂) := do
  c ← get_cache,
  if x₁.2 < x₂.2 then do
    (b', h) ← eval_add b₁ he₂,
    return (xadd' c a₁ x₁ n₁ b',
      c.cs_app ``horner_add_const [a₁, x₁.1, n₁.1, b₁, e₂, b', h])
  else if x₁.2 ≠ x₂.2 then do
    (b', h) ← eval_add he₁ b₂,
    return (xadd' c a₂ x₂ n₂ b',
      c.cs_app ``const_add_horner [e₁, a₂, x₂.1, n₂.1, b₂, b', h])
  else if n₁.2 < n₂.2 then do
    let k := n₂.2 - n₁.2,
    ek ← lift $ expr.of_nat (expr.const `nat []) k,
    (_, h₁) ← lift $ mk_app ``has_add.add [n₁.1, ek] >>= norm_num,
    α0 ← lift $ expr.of_nat c.α 0,
    (a', h₂) ← eval_add a₁ (xadd' c a₂ x₁ (ek, k) (const α0)),
    (b', h₃) ← eval_add b₁ b₂,
    return (xadd' c a' x₁ n₁ b',
      c.cs_app ``horner_add_horner_lt [a₁, x₁.1, n₁.1, b₁, a₂, n₂.1, b₂, ek, a', b', h₁, h₂, h₃])
  else if n₁.2 ≠ n₂.2 then do
    let k := n₁.2 - n₂.2,
    ek ← lift $ expr.of_nat (expr.const `nat []) k,
    (_, h₁) ← lift $ mk_app ``has_add.add [n₂.1, ek] >>= norm_num,
    α0 ← lift $ expr.of_nat c.α 0,
    (a', h₂) ← eval_add (xadd' c a₁ x₁ (ek, k) (const α0)) a₂,
    (b', h₃) ← eval_add b₁ b₂,
    return (xadd' c a' x₁ n₂ b',
      c.cs_app ``horner_add_horner_gt [a₁, x₁.1, n₁.1, b₁, a₂, n₂.1, b₂, ek, a', b', h₁, h₂, h₃])
  else do
    (a', h₁) ← eval_add a₁ a₂,
    (b', h₂) ← eval_add b₁ b₂,
    (t, h₃) ← eval_horner a' x₁ n₁ b',
    return (t, c.cs_app ``horner_add_horner_eq
      [a₁, x₁.1, n₁.1, b₁, a₂, b₂, a', b', t, h₁, h₂, h₃])

theorem horner_neg {α} [comm_ring α] (a x n b a' b')
  (h₁ : -a = a') (h₂ : -b = b') :
  -@horner α _ a x n b = horner a' x n b' :=
by simp [h₂.symm, h₁.symm, horner]

meta def eval_neg : horner_expr → ring_m (horner_expr × expr)
| (const e) := do
  (e', p) ← lift $ mk_app ``has_neg.neg [e] >>= norm_num,
  return (const e', p)
| (xadd e a x n b) := do
  c ← get_cache,
  (a', h₁) ← eval_neg a,
  (b', h₂) ← eval_neg b,
  p ← ring_m.mk_app ``horner_neg ``comm_ring [a, x.1, n.1, b, a', b', h₁, h₂],
  return (xadd' c a' x n b', p)

theorem horner_const_mul {α} [comm_semiring α] (c a x n b a' b')
  (h₁ : c * a = a') (h₂ : c * b = b') :
  c * @horner α _ a x n b = horner a' x n b' :=
by simp [h₂.symm, h₁.symm, horner, mul_add, mul_assoc]

theorem horner_mul_const {α} [comm_semiring α] (a x n b c a' b')
  (h₁ : a * c = a') (h₂ : b * c = b') :
  @horner α _ a x n b * c = horner a' x n b' :=
by simp [h₂.symm, h₁.symm, horner, add_mul, mul_right_comm]

meta def eval_const_mul (k : expr) :
  horner_expr → ring_m (horner_expr × expr)
| (const e) := do
  (e', p) ← lift $ mk_app ``has_mul.mul [k, e] >>= norm_num,
  return (const e', p)
| (xadd e a x n b) := do
  c ← get_cache,
  (a', h₁) ← eval_const_mul a,
  (b', h₂) ← eval_const_mul b,
  return (xadd' c a' x n b',
    c.cs_app ``horner_const_mul [k, a, x.1, n.1, b, a', b', h₁, h₂])

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

meta def eval_mul : horner_expr → horner_expr → ring_m (horner_expr × expr)
| (const e₁) (const e₂) := do
  (e', p) ← lift $ mk_app ``has_mul.mul [e₁, e₂] >>= norm_num,
  return (const e', p)
| (const e₁) e₂ :=
  match e₁.to_nat with
  | (some 0) := do
    c ← get_cache,
    α0 ← lift $ expr.of_nat c.α 0,
    p ← lift $ mk_app ``zero_mul [e₂],
    return (const α0, p)
  | (some 1) := do
    p ← lift $ mk_app ``one_mul [e₂],
    return (e₂, p)
  | _ := eval_const_mul e₁ e₂
  end
| e₁ he₂@(const e₂) := do
  p₁ ← lift $ mk_app ``mul_comm [e₁, e₂],
  (e', p₂) ← eval_mul he₂ e₁,
  p ← lift $ mk_eq_trans p₁ p₂, return (e', p)
| he₁@(xadd e₁ a₁ x₁ n₁ b₁) he₂@(xadd e₂ a₂ x₂ n₂ b₂) := do
  c ← get_cache,
  if x₁.2 < x₂.2 then do
    (a', h₁) ← eval_mul a₁ he₂,
    (b', h₂) ← eval_mul b₁ he₂,
    return (xadd' c a' x₁ n₁ b',
      c.cs_app ``horner_mul_const [a₁, x₁.1, n₁.1, b₁, e₂, a', b', h₁, h₂])
  else if x₁.2 ≠ x₂.2 then do
    (a', h₁) ← eval_mul he₁ a₂,
    (b', h₂) ← eval_mul he₁ b₂,
    return (xadd' c a' x₂ n₂ b',
      c.cs_app ``horner_const_mul [e₁, a₂, x₂.1, n₂.1, b₂, a', b', h₁, h₂])
  else do
    (aa, h₁) ← eval_mul he₁ a₂,
    α0 ← lift $ expr.of_nat c.α 0,
    (haa, h₂) ← eval_horner aa x₁ n₂ (const α0),
    if b₂.e.to_nat = some 0 then
      return (haa, c.cs_app ``horner_mul_horner_zero
        [a₁, x₁.1, n₁.1, b₁, a₂, n₂.1, aa, haa, h₁, h₂])
    else do
      (ab, h₃) ← eval_mul a₁ b₂,
      (bb, h₄) ← eval_mul b₁ b₂,
      (t, H) ← eval_add haa (xadd' c ab x₁ n₁ bb),
      return (t, c.cs_app ``horner_mul_horner
        [a₁, x₁.1, n₁.1, b₁, a₂, n₂.1, b₂, aa, haa, ab, bb, t, h₁, h₂, h₃, h₄, H])

theorem horner_pow {α} [comm_semiring α] (a x n m n' a')
  (h₁ : n * m = n') (h₂ : a ^ m = a') :
  @horner α _ a x n 0 ^ m = horner a' x n' 0 :=
by simp [h₁.symm, h₂.symm, horner, mul_pow, pow_mul]

meta def eval_pow : horner_expr → expr × ℕ → ring_m (horner_expr × expr)
| e (_, 0) := do
  c ← get_cache,
  α1 ← lift $ expr.of_nat c.α 1,
  p ← lift $ mk_app ``pow_zero [e],
  return (const α1, p)
| e (_, 1) := do
  p ← lift $ mk_app ``pow_one [e],
  return (e, p)
| (const e) (e₂, m) := do
  (e', p) ← lift $ mk_app ``monoid.pow [e, e₂] >>= norm_num.derive,
  return (const e', p)
| he@(xadd e a x n b) m := do
  c ← get_cache,
  let N : expr := expr.const `nat [],
  match b.e.to_nat with
  | some 0 := do
    (n', h₁) ← lift $ mk_app ``has_mul.mul [n.1, m.1] >>= norm_num,
    (a', h₂) ← eval_pow a m,
    α0 ← lift $ expr.of_nat c.α 0,
    return (xadd' c a' x (n', n.2 * m.2) (const α0),
      c.cs_app ``horner_pow [a, x.1, n.1, m.1, n', a', h₁, h₂])
  | _ := do
    e₂ ← lift $ expr.of_nat N (m.2-1),
    l ← lift $ mk_app ``monoid.pow [e, e₂],
    (tl, hl) ← eval_pow he (e₂, m.2-1),
    (t, p₂) ← eval_mul tl he,
    hr ← lift $ mk_eq_refl e,
    p₂ ← ring_m.mk_app ``norm_num.subst_into_prod ``has_mul [l, e, tl, e, t, hl, hr, p₂],
    p₁ ← lift $ mk_app ``pow_succ' [e, e₂],
    p ← lift $ mk_eq_trans p₁ p₂,
    return (t, p)
  end

theorem horner_atom {α} [comm_semiring α] (x : α) : x = horner 1 x 1 0 :=
by simp [horner]

meta def eval_atom (e : expr) : ring_m (horner_expr × expr) :=
do c ← get_cache,
  i ← add_atom e,
  α0 ← lift $ expr.of_nat c.α 0,
  α1 ← lift $ expr.of_nat c.α 1,
  n1 ← lift $ expr.of_nat (expr.const `nat []) 1,
  return (xadd' c (const α1) (e, i) (n1, 1) (const α0),
    c.cs_app ``horner_atom [e])

lemma subst_into_pow {α} [monoid α] (l r tl tr t)
  (prl : (l : α) = tl) (prr : (r : ℕ) = tr) (prt : tl ^ tr = t) : l ^ r = t :=
by simp [prl, prr, prt]

lemma unfold_sub {α} [add_group α] (a b c : α)
  (h : a + -b = c) : a - b = c := h

lemma unfold_div {α} [division_ring α] (a b c : α)
  (h : a * b⁻¹ = c) : a / b = c := h

meta def eval : expr → ring_m (horner_expr × expr)
| `(%%e₁ + %%e₂) := do
  (e₁', p₁) ← eval e₁,
  (e₂', p₂) ← eval e₂,
  (e', p') ← eval_add e₁' e₂',
  p ← ring_m.mk_app ``norm_num.subst_into_sum ``has_add [e₁, e₂, e₁', e₂', e', p₁, p₂, p'],
  return (e', p)
| `(%%e₁ - %%e₂) := do
  c ← get_cache,
  e₂' ← lift $ mk_app ``has_neg.neg [e₂],
  e ← lift $ mk_app ``has_add.add [e₁, e₂'],
  (e', p) ← eval e,
  p' ← ring_m.mk_app ``unfold_sub ``add_group [e₁, e₂, e', p],
  return (e', p')
| `(- %%e) := do
  (e₁, p₁) ← eval e,
  (e₂, p₂) ← eval_neg e₁,
  p ← ring_m.mk_app ``norm_num.subst_into_neg ``has_neg [e, e₁, e₂, p₁, p₂],
  return (e₂, p)
| `(%%e₁ * %%e₂) := do
  (e₁', p₁) ← eval e₁,
  (e₂', p₂) ← eval e₂,
  (e', p') ← eval_mul e₁' e₂',
  p ← ring_m.mk_app ``norm_num.subst_into_prod ``has_mul [e₁, e₂, e₁', e₂', e', p₁, p₂, p'],
  return (e', p)
| e@`(has_inv.inv %%_) := (do
    (e', p) ← lift $ norm_num.derive e,
    lift $ e'.to_rat,
    return (const e', p)) <|> eval_atom e
| `(%%e₁ / %%e₂) := do
  e₂' ← lift $ mk_app ``has_inv.inv [e₂],
  e ← lift $ mk_app ``has_mul.mul [e₁, e₂'],
  (e', p) ← eval e,
  p' ← ring_m.mk_app ``unfold_div ``division_ring [e₁, e₂, e', p],
  return (e', p')
| e@`(@has_pow.pow _ _ %%P %%e₁ %%e₂) := do
  (e₂', p₂) ← eval e₂,
  match e₂'.e.to_nat, P with
  | some k, `(monoid.has_pow) := do
    (e₁', p₁) ← eval e₁,
    (e', p') ← eval_pow e₁' (e₂, k),
    p ← ring_m.mk_app ``subst_into_pow ``monoid [e₁, e₂, e₁', e₂', e', p₁, p₂, p'],
    return (e', p)
  | some k, `(nat.has_pow) := do
    (e₁', p₁) ← eval e₁,
    (e', p') ← eval_pow e₁' (e₂, k),
    p₃ ← ring_m.mk_app ``subst_into_pow ``monoid [e₁, e₂, e₁', e₂', e', p₁, p₂, p'],
    p₄ ← lift $ mk_app ``nat.pow_eq_pow [e₁, e₂] >>= mk_eq_symm,
    p ← lift $ mk_eq_trans p₄ p₃,
    return (e', p)
  | _, _ := eval_atom e
  end
| e := match e.to_nat with
  | some n := (const e).refl_conv
  | none := eval_atom e
  end

meta def eval' (red : transparency) (e : expr) : tactic (expr × expr) :=
ring_m.run red e $ do (e', p) ← eval e, return (e', p)

theorem horner_def' {α} [comm_semiring α] (a x n b) : @horner α _ a x n b = x ^ n * a + b :=
by simp [horner, mul_comm]

theorem mul_assoc_rev {α} [semigroup α] (a b c : α) : a * (b * c) = a * b * c :=
by simp [mul_assoc]

theorem pow_add_rev {α} [monoid α] (a : α) (m n : ℕ) : a ^ m * a ^ n = a ^ (m + n) :=
by simp [pow_add]

theorem pow_add_rev_right {α} [monoid α] (a b : α) (m n : ℕ) : b * a ^ m * a ^ n = b * a ^ (m + n) :=
by simp [pow_add, mul_assoc]

theorem add_neg_eq_sub {α} [add_group α] (a b : α) : a + -b = a - b := rfl

@[derive has_reflect]
inductive normalize_mode | raw | SOP | horner

meta def normalize (red : transparency) (mode := normalize_mode.horner) (e : expr) : tactic (expr × expr) := do
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
    (new_e, pr) ← match mode with
    | normalize_mode.raw := eval' red
    | normalize_mode.horner := trans_conv (eval' red) (simplify lemmas [])
    | normalize_mode.SOP :=
      trans_conv (eval' red) $
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

/-- Tactic for solving equations in the language of *commutative* (semi)rings.
  This version of `ring` fails if the target is not an equality
  that is provable by the axioms of commutative (semi)rings. -/
meta def ring1 (red : parse (tk "!")?) : tactic unit :=
let transp := if red.is_some then semireducible else reducible in
do `(%%e₁ = %%e₂) ← target,
  ((e₁', p₁), (e₂', p₂)) ← ring_m.run transp e₁ $
    prod.mk <$> eval e₁ <*> eval e₂,
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

/-- Tactic for solving equations in the language of *commutative* (semi)rings.
  Attempts to prove the goal outright if there is no `at`
  specifier and the target is an equality, but if this
  fails it falls back to rewriting all ring expressions
  into a normal form. When writing a normal form,
  `ring SOP` will use sum-of-products form instead of horner form.
  `ring!` will use a more aggressive reducibility setting to identify atoms. -/
meta def ring (red : parse (tk "!")?) (SOP : parse ring.mode) (loc : parse location) : tactic unit :=
match loc with
| interactive.loc.ns [none] := ring1 red
| _ := failed
end <|>
do ns ← loc.get_locals,
   let transp := if red.is_some then semireducible else reducible,
   tt ← tactic.replace_at (normalize transp SOP) ns loc.include_goal
      | fail "ring failed to simplify",
   when loc.include_goal $ try tactic.reflexivity

end interactive
end tactic

namespace conv.interactive
open conv interactive
open tactic tactic.interactive (ring.mode ring1)
open tactic.ring (normalize)

local postfix `?`:9001 := optional

meta def ring (red : parse (lean.parser.tk "!")?) (SOP : parse ring.mode) : conv unit :=
let transp := if red.is_some then semireducible else reducible in
discharge_eq_lhs (ring1 red)
<|> replace_lhs (normalize transp SOP)
<|> fail "ring failed to simplify"

end conv.interactive
