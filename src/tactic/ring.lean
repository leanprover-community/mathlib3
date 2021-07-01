/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import tactic.norm_num
import data.int.range

/-!
# `ring`

Evaluate expressions in the language of commutative (semi)rings.
Based on <http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf> .
-/

namespace tactic
namespace ring

/-- The normal form that `ring` uses is mediated by the function `horner a x n b := a * x ^ n + b`.
The reason we use a definition rather than the (more readable) expression on the right is because
this expression contains a number of typeclass arguments in different positions, while `horner`
contains only one `comm_semiring` instance at the top level. See also `horner_expr` for a
description of normal form. -/
def horner {α} [comm_semiring α] (a x : α) (n : ℕ) (b : α) := a * x ^ n + b

/-- This cache contains data required by the `ring` tactic during execution. -/
meta structure cache :=
(α : expr)
(univ : level)
(comm_semiring_inst : expr)
(red : transparency)
(ic : ref instance_cache)
(nc : ref instance_cache)
(atoms : ref (buffer expr))

/-- The monad that `ring` works in. This is a reader monad containing a mutable cache (using `ref`
for mutability), as well as the list of atoms-up-to-defeq encountered thus far, used for atom
sorting. -/
@[derive [monad, alternative]]
meta def ring_m (α : Type) : Type :=
reader_t cache tactic α

/-- Get the `ring` data from the monad. -/
meta def get_cache : ring_m cache := reader_t.read

/-- Get an already encountered atom by its index. -/
meta def get_atom (n : ℕ) : ring_m expr :=
⟨λ c, do es ← read_ref c.atoms, pure (es.read' n)⟩

/-- Get the index corresponding to an atomic expression, if it has already been encountered, or
put it in the list of atoms and return the new index, otherwise. -/
meta def add_atom (e : expr) : ring_m ℕ :=
⟨λ c, do
  let red := c.red,
  es ← read_ref c.atoms,
  es.iterate failed (λ n e' t, t <|> (is_def_eq e e' red $> n)) <|>
  (es.size <$ write_ref c.atoms (es.push_back e))⟩

/-- Lift a tactic into the `ring_m` monad. -/
@[inline] meta def lift {α} (m : tactic α) : ring_m α := reader_t.lift m

/-- Run a `ring_m` tactic in the tactic monad. This version of `ring_m.run` uses an external
atoms ref, so that subexpressions can be named across multiple `ring_m` calls. -/
meta def ring_m.run' (red : transparency) (atoms : ref (buffer expr))
  (e : expr) {α} (m : ring_m α) : tactic α :=
do α ← infer_type e,
   u ← mk_meta_univ,
   infer_type α >>= unify (expr.sort (level.succ u)),
   u ← get_univ_assignment u,
   ic ← mk_instance_cache α,
   (ic, c) ← ic.get ``comm_semiring,
   nc ← mk_instance_cache `(ℕ),
   using_new_ref ic $ λ r,
   using_new_ref nc $ λ nr,
   reader_t.run m ⟨α, u, c, red, r, nr, atoms⟩

/-- Run a `ring_m` tactic in the tactic monad. -/
meta def ring_m.run (red : transparency) (e : expr) {α} (m : ring_m α) : tactic α :=
using_new_ref mk_buffer $ λ atoms, ring_m.run' red atoms e m

/-- Lift an instance cache tactic (probably from `norm_num`) to the `ring_m` monad. This version
is abstract over the instance cache in question (either the ring `α`, or `ℕ` for exponents). -/
@[inline] meta def ic_lift' (icf : cache → ref instance_cache) {α}
  (f : instance_cache → tactic (instance_cache × α)) : ring_m α :=
⟨λ c, do
  let r := icf c,
  ic ← read_ref r,
  (ic', a) ← f ic,
  a <$ write_ref r ic'⟩

/-- Lift an instance cache tactic (probably from `norm_num`) to the `ring_m` monad. This uses
the instance cache corresponding to the ring `α`. -/
@[inline] meta def ic_lift {α} : (instance_cache → tactic (instance_cache × α)) → ring_m α :=
ic_lift' cache.ic

/-- Lift an instance cache tactic (probably from `norm_num`) to the `ring_m` monad. This uses
the instance cache corresponding to `ℕ`, which is used for computations in the exponent. -/
@[inline] meta def nc_lift {α} : (instance_cache → tactic (instance_cache × α)) → ring_m α :=
ic_lift' cache.nc

/-- Apply a theorem that expects a `comm_semiring` instance. This is a special case of
`ic_lift mk_app`, but it comes up often because `horner` and all its theorems have this assumption;
it also does not require the tactic monad which improves access speed a bit. -/
meta def cache.cs_app (c : cache) (n : name) : list expr → expr :=
(@expr.const tt n [c.univ] c.α c.comm_semiring_inst).mk_app

/-- Every expression in the language of commutative semirings can be viewed as a sum of monomials,
where each monomial is a product of powers of atoms. We fix a global order on atoms (up to
definitional equality), and then separate the terms according to their smallest atom. So the top
level expression is `a * x^n + b` where `x` is the smallest atom and `n > 0` is a numeral, and
`n` is maximal (so `a` contains at least one monomial not containing an `x`), and `b` contains no
monomials with an `x` (hence all atoms in `b` are larger than `x`).

If there is no `x` satisfying these constraints, then the expression must be a numeral. Even though
we are working over rings, we allow rational constants when these can be interpreted in the ring,
so we can solve problems like `x / 3 = 1 / 3 * x` even though these are not technically in the
language of rings.

These constraints ensure that there is a unique normal form for each ring expression, and so the
algorithm is simply to calculate the normal form of each side and compare for equality.

To allow us to efficiently pattern match on normal forms, we maintain this inductive type that
holds a normalized expression together with its structure. All the `expr`s in this type could be
removed without loss of information, and conversely the `horner_expr` structure and the `ℕ` and
`ℚ` values can be recovered from the top level `expr`, but we keep both in order to keep proof
 producing normalization functions efficient. -/
meta inductive horner_expr : Type
| const (e : expr) (coeff : ℚ) : horner_expr
| xadd (e : expr) (a : horner_expr) (x : expr × ℕ) (n : expr × ℕ) (b : horner_expr) : horner_expr

/-- Get the expression corresponding to a `horner_expr`. This can be calculated recursively from
the structure, but we cache the exprs in all subterms so that this function can be computed in
constant time. -/
meta def horner_expr.e : horner_expr → expr
| (horner_expr.const e _) := e
| (horner_expr.xadd e _ _ _ _) := e

/-- Is this expr the constant `0`? -/
meta def horner_expr.is_zero : horner_expr → bool
| (horner_expr.const _ c) := c = 0
| _ := ff

meta instance : has_coe horner_expr expr := ⟨horner_expr.e⟩
meta instance : has_coe_to_fun horner_expr := ⟨_, λ e, ((e : expr) : expr → expr)⟩

/-- Construct a `xadd` node, generating the cached expr using the input cache. -/
meta def horner_expr.xadd' (c : cache) (a : horner_expr)
  (x : expr × ℕ) (n : expr × ℕ) (b : horner_expr) : horner_expr :=
horner_expr.xadd (c.cs_app ``horner [a, x.1, n.1, b]) a x n b

open horner_expr

/-- Pretty printer for `horner_expr`. -/
meta def horner_expr.to_string : horner_expr → string
| (const e c) := to_string (e, c)
| (xadd e a x (_, n) b) :=
    "(" ++ a.to_string ++ ") * (" ++ to_string x.1 ++ ")^"
        ++ to_string n ++ " + " ++ b.to_string

/-- Pretty printer for `horner_expr`. -/
meta def horner_expr.pp : horner_expr → tactic format
| (const e c) := pp (e, c)
| (xadd e a x (_, n) b) := do
  pa ← a.pp, pb ← b.pp, px ← pp x.1,
  return $ "(" ++ pa ++ ") * (" ++ px ++ ")^" ++ to_string n ++ " + " ++ pb

meta instance : has_to_tactic_format horner_expr := ⟨horner_expr.pp⟩

/-- Reflexivity conversion for a `horner_expr`. -/
meta def horner_expr.refl_conv (e : horner_expr) : ring_m (horner_expr × expr) :=
do p ← lift $ mk_eq_refl e, return (e, p)

theorem zero_horner {α} [comm_semiring α] (x n b) :
  @horner α _ 0 x n b = b :=
by simp [horner]

theorem horner_horner {α} [comm_semiring α] (a₁ x n₁ n₂ b n')
  (h : n₁ + n₂ = n') :
  @horner α _ (horner a₁ x n₁ 0) x n₂ b = horner a₁ x n' b :=
by simp [h.symm, horner, pow_add, mul_assoc]

/-- Evaluate `horner a n x b` where `a` and `b` are already in normal form. -/
meta def eval_horner : horner_expr → expr × ℕ → expr × ℕ → horner_expr → ring_m (horner_expr × expr)
| ha@(const a coeff) x n b := do
  c ← get_cache,
  if coeff = 0 then
    return (b, c.cs_app ``zero_horner [x.1, n.1, b])
  else (xadd' c ha x n b).refl_conv
| ha@(xadd a a₁ x₁ n₁ b₁) x n b := do
  c ← get_cache,
  if x₁.2 = x.2 ∧ b₁.e.to_nat = some 0 then do
    (n', h) ← nc_lift $ λ nc, norm_num.prove_add_nat' nc n₁.1 n.1,
    return (xadd' c a₁ x (n', n₁.2 + n.2) b,
      c.cs_app ``horner_horner [a₁, x.1, n₁.1, n.1, b, n', h])
  else (xadd' c ha x n b).refl_conv

theorem const_add_horner {α} [comm_semiring α] (k a x n b b') (h : k + b = b') :
  k + @horner α _ a x n b = horner a x n b' :=
by simp [h.symm, horner]; cc

theorem horner_add_const {α} [comm_semiring α] (a x n b k b') (h : b + k = b') :
  @horner α _ a x n b + k = horner a x n b' :=
by simp [h.symm, horner, add_assoc]

theorem horner_add_horner_lt {α} [comm_semiring α] (a₁ x n₁ b₁ a₂ n₂ b₂ k a' b')
  (h₁ : n₁ + k = n₂) (h₂ : (a₁ + horner a₂ x k 0 : α) = a') (h₃ : b₁ + b₂ = b') :
  @horner α _ a₁ x n₁ b₁ + horner a₂ x n₂ b₂ = horner a' x n₁ b' :=
by simp [h₂.symm, h₃.symm, h₁.symm, horner, pow_add, mul_add, mul_comm, mul_left_comm]; cc

theorem horner_add_horner_gt {α} [comm_semiring α] (a₁ x n₁ b₁ a₂ n₂ b₂ k a' b')
  (h₁ : n₂ + k = n₁) (h₂ : (horner a₁ x k 0 + a₂ : α) = a') (h₃ : b₁ + b₂ = b') :
  @horner α _ a₁ x n₁ b₁ + horner a₂ x n₂ b₂ = horner a' x n₂ b' :=
by simp [h₂.symm, h₃.symm, h₁.symm, horner, pow_add, mul_add, mul_comm, mul_left_comm]; cc

theorem horner_add_horner_eq {α} [comm_semiring α] (a₁ x n b₁ a₂ b₂ a' b' t)
  (h₁ : a₁ + a₂ = a') (h₂ : b₁ + b₂ = b') (h₃ : horner a' x n b' = t) :
  @horner α _ a₁ x n b₁ + horner a₂ x n b₂ = t :=
by simp [h₃.symm, h₂.symm, h₁.symm, horner, add_mul, mul_comm (x ^ n)]; cc

/-- Evaluate `a + b` where `a` and `b` are already in normal form. -/
meta def eval_add : horner_expr → horner_expr → ring_m (horner_expr × expr)
| (const e₁ c₁) (const e₂ c₂) := ic_lift $ λ ic, do
  let n := c₁ + c₂,
  (ic, e) ← ic.of_rat n,
  (ic, p) ← norm_num.prove_add_rat ic e₁ e₂ e c₁ c₂ n,
  return (ic, const e n, p)
| he₁@(const e₁ c₁) he₂@(xadd e₂ a x n b) := do
  c ← get_cache,
  if c₁ = 0 then ic_lift $ λ ic, do
    (ic, p) ← ic.mk_app ``zero_add [e₂],
    return (ic, he₂, p)
  else do
    (b', h) ← eval_add he₁ b,
    return (xadd' c a x n b',
      c.cs_app ``const_add_horner [e₁, a, x.1, n.1, b, b', h])
| he₁@(xadd e₁ a x n b) he₂@(const e₂ c₂) := do
  c ← get_cache,
  if c₂ = 0 then ic_lift $ λ ic, do
    (ic, p) ← ic.mk_app ``add_zero [e₁],
    return (ic, he₁, p)
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
    (ek, h₁) ← nc_lift (λ nc, do
      (nc, ek) ← nc.of_nat k,
      (nc, h₁) ← norm_num.prove_add_nat nc n₁.1 ek n₂.1,
      return (nc, ek, h₁)),
    α0 ← ic_lift $ λ ic, ic.mk_app ``has_zero.zero [],
    (a', h₂) ← eval_add a₁ (xadd' c a₂ x₁ (ek, k) (const α0 0)),
    (b', h₃) ← eval_add b₁ b₂,
    return (xadd' c a' x₁ n₁ b',
      c.cs_app ``horner_add_horner_lt [a₁, x₁.1, n₁.1, b₁, a₂, n₂.1, b₂, ek, a', b', h₁, h₂, h₃])
  else if n₁.2 ≠ n₂.2 then do
    let k := n₁.2 - n₂.2,
    (ek, h₁) ← nc_lift (λ nc, do
      (nc, ek) ← nc.of_nat k,
      (nc, h₁) ← norm_num.prove_add_nat nc n₂.1 ek n₁.1,
      return (nc, ek, h₁)),
    α0 ← ic_lift $ λ ic, ic.mk_app ``has_zero.zero [],
    (a', h₂) ← eval_add (xadd' c a₁ x₁ (ek, k) (const α0 0)) a₂,
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
by simp [h₂.symm, h₁.symm, horner]; cc

/-- Evaluate `-a` where `a` is already in normal form. -/
meta def eval_neg : horner_expr → ring_m (horner_expr × expr)
| (const e coeff) := do
  (e', p) ← ic_lift $ λ ic, norm_num.prove_neg ic e,
  return (const e' (-coeff), p)
| (xadd e a x n b) := do
  c ← get_cache,
  (a', h₁) ← eval_neg a,
  (b', h₂) ← eval_neg b,
  p ← ic_lift $ λ ic, ic.mk_app ``horner_neg [a, x.1, n.1, b, a', b', h₁, h₂],
  return (xadd' c a' x n b', p)

theorem horner_const_mul {α} [comm_semiring α] (c a x n b a' b')
  (h₁ : c * a = a') (h₂ : c * b = b') :
  c * @horner α _ a x n b = horner a' x n b' :=
by simp [h₂.symm, h₁.symm, horner, mul_add, mul_assoc]

theorem horner_mul_const {α} [comm_semiring α] (a x n b c a' b')
  (h₁ : a * c = a') (h₂ : b * c = b') :
  @horner α _ a x n b * c = horner a' x n b' :=
by simp [h₂.symm, h₁.symm, horner, add_mul, mul_right_comm]

/-- Evaluate `k * a` where `k` is a rational numeral and `a` is in normal form. -/
meta def eval_const_mul (k : expr × ℚ) :
  horner_expr → ring_m (horner_expr × expr)
| (const e coeff) := do
  (e', p) ← ic_lift $ λ ic, norm_num.prove_mul_rat ic k.1 e k.2 coeff,
  return (const e' (k.2 * coeff), p)
| (xadd e a x n b) := do
  c ← get_cache,
  (a', h₁) ← eval_const_mul a,
  (b', h₂) ← eval_const_mul b,
  return (xadd' c a' x n b',
    c.cs_app ``horner_const_mul [k.1, a, x.1, n.1, b, a', b', h₁, h₂])

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

/-- Evaluate `a * b` where `a` and `b` are in normal form. -/
meta def eval_mul : horner_expr → horner_expr → ring_m (horner_expr × expr)
| (const e₁ c₁) (const e₂ c₂) := do
  (e', p) ← ic_lift $ λ ic, norm_num.prove_mul_rat ic e₁ e₂ c₁ c₂,
  return (const e' (c₁ * c₂), p)
| (const e₁ c₁) e₂ :=
  if c₁ = 0 then do
    c ← get_cache,
    α0 ← ic_lift $ λ ic, ic.mk_app ``has_zero.zero [],
    p ← ic_lift $ λ ic, ic.mk_app ``zero_mul [e₂],
    return (const α0 0, p)
  else if c₁ = 1 then do
    p ← ic_lift $ λ ic, ic.mk_app ``one_mul [e₂],
    return (e₂, p)
  else eval_const_mul (e₁, c₁) e₂
| e₁ he₂@(const e₂ c₂) := do
  p₁ ← ic_lift $ λ ic, ic.mk_app ``mul_comm [e₁, e₂],
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
    α0 ← ic_lift $ λ ic, ic.mk_app ``has_zero.zero [],
    (haa, h₂) ← eval_horner aa x₁ n₂ (const α0 0),
    if b₂.is_zero then
      return (haa, c.cs_app ``horner_mul_horner_zero
        [a₁, x₁.1, n₁.1, b₁, a₂, n₂.1, aa, haa, h₁, h₂])
    else do
      (ab, h₃) ← eval_mul a₁ b₂,
      (bb, h₄) ← eval_mul b₁ b₂,
      (t, H) ← eval_add haa (xadd' c ab x₁ n₁ bb),
      return (t, c.cs_app ``horner_mul_horner
        [a₁, x₁.1, n₁.1, b₁, a₂, n₂.1, b₂, aa, haa, ab, bb, t, h₁, h₂, h₃, h₄, H])

theorem horner_pow {α} [comm_semiring α] (a x n m n' a') (h₁ : n * m = n') (h₂ : a ^ m = a') :
  @horner α _ a x n 0 ^ m = horner a' x n' 0 :=
by simp [h₁.symm, h₂.symm, horner, mul_pow, pow_mul]

theorem pow_succ {α} [comm_semiring α] (a n b c)
  (h₁ : (a:α) ^ n = b) (h₂ : b * a = c) : a ^ (n + 1) = c :=
by rw [← h₂, ← h₁, pow_succ']

/-- Evaluate `a ^ n` where `a` is in normal form and `n` is a natural numeral. -/
meta def eval_pow : horner_expr → expr × ℕ → ring_m (horner_expr × expr)
| e (_, 0) := do
  c ← get_cache,
  α1 ← ic_lift $ λ ic, ic.mk_app ``has_one.one [],
  p ← ic_lift $ λ ic, ic.mk_app ``pow_zero [e],
  return (const α1 1, p)
| e (_, 1) := do
  p ← ic_lift $ λ ic, ic.mk_app ``pow_one [e],
  return (e, p)
| (const e coeff) (e₂, m) := ic_lift $ λ ic, do
  (ic, e', p) ← norm_num.prove_pow e coeff ic e₂,
  return (ic, const e' (coeff ^ m), p)
| he@(xadd e a x n b) m := do
  c ← get_cache,
  match b.e.to_nat with
  | some 0 := do
    (n', h₁) ← nc_lift $ λ nc, norm_num.prove_mul_rat nc n.1 m.1 n.2 m.2,
    (a', h₂) ← eval_pow a m,
    α0 ← ic_lift $ λ ic, ic.mk_app ``has_zero.zero [],
    return (xadd' c a' x (n', n.2 * m.2) (const α0 0),
      c.cs_app ``horner_pow [a, x.1, n.1, m.1, n', a', h₁, h₂])
  | _ := do
    e₂ ← nc_lift $ λ nc, nc.of_nat (m.2-1),
    (tl, hl) ← eval_pow he (e₂, m.2-1),
    (t, p₂) ← eval_mul tl he,
    return (t, c.cs_app ``pow_succ [e, e₂, tl, t, hl, p₂])
  end

theorem horner_atom {α} [comm_semiring α] (x : α) : x = horner 1 x 1 0 :=
by simp [horner]

/-- Evaluate `a` where `a` is an atom. -/
meta def eval_atom (e : expr) : ring_m (horner_expr × expr) :=
do c ← get_cache,
  i ← add_atom e,
  α0 ← ic_lift $ λ ic, ic.mk_app ``has_zero.zero [],
  α1 ← ic_lift $ λ ic, ic.mk_app ``has_one.one [],
  return (xadd' c (const α1 1) (e, i) (`(1), 1) (const α0 0),
    c.cs_app ``horner_atom [e])

lemma subst_into_pow {α} [monoid α] (l r tl tr t)
  (prl : (l : α) = tl) (prr : (r : ℕ) = tr) (prt : tl ^ tr = t) : l ^ r = t :=
by rw [prl, prr, prt]

lemma unfold_sub {α} [add_group α] (a b c : α)
  (h : a + -b = c) : a - b = c :=
by rw [sub_eq_add_neg, h]

lemma unfold_div {α} [division_ring α] (a b c : α)
  (h : a * b⁻¹ = c) : a / b = c :=
by rw [div_eq_mul_inv, h]

/-- Evaluate a ring expression `e` recursively to normal form, together with a proof of
equality. -/
meta def eval : expr → ring_m (horner_expr × expr)
| `(%%e₁ + %%e₂) := do
  (e₁', p₁) ← eval e₁,
  (e₂', p₂) ← eval e₂,
  (e', p') ← eval_add e₁' e₂',
  p ← ic_lift $ λ ic, ic.mk_app ``norm_num.subst_into_add [e₁, e₂, e₁', e₂', e', p₁, p₂, p'],
  return (e', p)
| e@`(@has_sub.sub %%α %%inst %%e₁ %%e₂) :=
  mcond (succeeds (lift $ mk_app ``comm_ring [α] >>= mk_instance))
    (do
      e₂' ← ic_lift $ λ ic, ic.mk_app ``has_neg.neg [e₂],
      e ← ic_lift $ λ ic, ic.mk_app ``has_add.add [e₁, e₂'],
      (e', p) ← eval e,
      p' ← ic_lift $ λ ic, ic.mk_app ``unfold_sub [e₁, e₂, e', p],
      return (e', p'))
    (eval_atom e)
| `(- %%e) := do
  (e₁, p₁) ← eval e,
  (e₂, p₂) ← eval_neg e₁,
  p ← ic_lift $ λ ic, ic.mk_app ``norm_num.subst_into_neg [e, e₁, e₂, p₁, p₂],
  return (e₂, p)
| `(%%e₁ * %%e₂) := do
  (e₁', p₁) ← eval e₁,
  (e₂', p₂) ← eval e₂,
  (e', p') ← eval_mul e₁' e₂',
  p ← ic_lift $ λ ic, ic.mk_app ``norm_num.subst_into_mul [e₁, e₂, e₁', e₂', e', p₁, p₂, p'],
  return (e', p)
| e@`(has_inv.inv %%_) := (do
    (e', p) ← lift $ norm_num.derive e <|> refl_conv e,
    n ← lift $ e'.to_rat,
    return (const e' n, p)) <|> eval_atom e
| e@`(@has_div.div _ %%inst %%e₁ %%e₂) := mcond
  (succeeds (do
    inst' ← ic_lift $ λ ic, ic.mk_app ``div_inv_monoid.to_has_div [],
    lift $ is_def_eq inst inst'))
  (do
    e₂' ← ic_lift $ λ ic, ic.mk_app ``has_inv.inv [e₂],
    e ← ic_lift $ λ ic, ic.mk_app ``has_mul.mul [e₁, e₂'],
    (e', p) ← eval e,
    p' ← ic_lift $ λ ic, ic.mk_app ``unfold_div [e₁, e₂, e', p],
    return (e', p'))
  (eval_atom e)
| e@`(@has_pow.pow _ _ %%P %%e₁ %%e₂) := do
  (e₂', p₂) ← lift $ norm_num.derive e₂ <|> refl_conv e₂,
  match e₂'.to_nat, P with
  | some k, `(monoid.has_pow) := do
    (e₁', p₁) ← eval e₁,
    (e', p') ← eval_pow e₁' (e₂, k),
    p ← ic_lift $ λ ic, ic.mk_app ``subst_into_pow [e₁, e₂, e₁', e₂', e', p₁, p₂, p'],
    return (e', p)
  | _, _ := eval_atom e
  end
| e := match e.to_nat with
  | some n := (const e (rat.of_int n)).refl_conv
  | none := eval_atom e
  end

/-- Evaluate a ring expression `e` recursively to normal form, together with a proof of
equality. -/
meta def eval' (red : transparency) (atoms : ref (buffer expr))
  (e : expr) : tactic (expr × expr) :=
ring_m.run' red atoms e $ do (e', p) ← eval e, return (e', p)

theorem horner_def' {α} [comm_semiring α] (a x n b) : @horner α _ a x n b = x ^ n * a + b :=
by simp [horner, mul_comm]

theorem mul_assoc_rev {α} [semigroup α] (a b c : α) : a * (b * c) = a * b * c :=
by simp [mul_assoc]

theorem pow_add_rev {α} [monoid α] (a : α) (m n : ℕ) : a ^ m * a ^ n = a ^ (m + n) :=
by simp [pow_add]

theorem pow_add_rev_right {α} [monoid α] (a b : α) (m n : ℕ) :
  b * a ^ m * a ^ n = b * a ^ (m + n) :=
by simp [pow_add, mul_assoc]

theorem add_neg_eq_sub {α} [add_group α] (a b : α) : a + -b = a - b := (sub_eq_add_neg a b).symm

/-- If `ring` fails to close the goal, it falls back on normalizing the expression to a "pretty"
form so that you can see why it failed. This setting adjusts the resulting form:

  * `raw` is the form that `ring` actually uses internally, with iterated applications of `horner`.
    Not very readable but useful if you don't want any postprocessing.
    This results in terms like `horner (horner (horner 3 y 1 0) x 2 1) x 1 (horner 1 y 1 0)`.
  * `horner` maintains the Horner form structure, but it unfolds the `horner` definition itself,
    and tries to otherwise minimize parentheses.
    This results in terms like `(3 * x ^ 2 * y + 1) * x + y`.
  * `SOP` means sum of products form, expanding everything to monomials.
    This results in terms like `3 * x ^ 3 * y + x + y`. -/
@[derive has_reflect]
inductive normalize_mode | raw | SOP | horner

instance : inhabited normalize_mode := ⟨normalize_mode.horner⟩

/-- A `ring`-based normalization simplifier that rewrites ring expressions into the specified mode.

  * `raw` is the form that `ring` actually uses internally, with iterated applications of `horner`.
    Not very readable but useful if you don't want any postprocessing.
    This results in terms like `horner (horner (horner 3 y 1 0) x 2 1) x 1 (horner 1 y 1 0)`.
  * `horner` maintains the Horner form structure, but it unfolds the `horner` definition itself,
    and tries to otherwise minimize parentheses.
    This results in terms like `(3 * x ^ 2 * y + 1) * x + y`.
  * `SOP` means sum of products form, expanding everything to monomials.
    This results in terms like `3 * x ^ 3 * y + x + y`. -/
meta def normalize (red : transparency) (mode := normalize_mode.horner) (e : expr) :
  tactic (expr × expr) :=
using_new_ref mk_buffer $ λ atoms, do
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
    | normalize_mode.raw := eval' red atoms
    | normalize_mode.horner := trans_conv (eval' red atoms)
                                 (λ e, do (e', prf, _) ← simplify lemmas [] e, return (e', prf))
    | normalize_mode.SOP :=
      trans_conv (eval' red atoms) $
      trans_conv (λ e, do (e', prf, _) ← simplify lemmas [] e, return (e', prf)) $
      simp_bottom_up' (λ e, norm_num.derive e <|> pow_lemma.rewrite e)
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

/-- Parser for `ring_nf`'s `mode` argument, which can only be the "keywords" `raw`, `horner` or
`SOP`. (Because these are not actually keywords we use a name parser and postprocess the result.)
-/
meta def ring.mode : lean.parser ring.normalize_mode :=
with_desc "(SOP|raw|horner)?" $
do mode ← ident?, match mode with
| none         := return ring.normalize_mode.horner
| some `horner := return ring.normalize_mode.horner
| some `SOP    := return ring.normalize_mode.SOP
| some `raw    := return ring.normalize_mode.raw
| _            := failed
end

/-- Simplification tactic for expressions in the language of commutative (semi)rings,
which rewrites all ring expressions into a normal form. When writing a normal form,
`ring_nf SOP` will use sum-of-products form instead of horner form.
`ring_nf!` will use a more aggressive reducibility setting to identify atoms.
-/
meta def ring_nf (red : parse (tk "!")?) (SOP : parse ring.mode) (loc : parse location) :
  tactic unit :=
do ns ← loc.get_locals,
   let transp := if red.is_some then semireducible else reducible,
   tt ← tactic.replace_at (normalize transp SOP) ns loc.include_goal
      | fail "ring_nf failed to simplify",
   when loc.include_goal $ try tactic.reflexivity

/-- Tactic for solving equations in the language of *commutative* (semi)rings.
`ring!` will use a more aggressive reducibility setting to identify atoms.

If the goal is not solvable, it falls back to rewriting all ring expressions
into a normal form, with a suggestion to use `ring_nf` instead, if this is the intent.
See also `ring1`, which is the same as `ring` but without the fallback behavior.

Based on [Proving Equalities in a Commutative Ring Done Right
in Coq](http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf) by Benjamin Grégoire
and Assia Mahboubi.
-/
meta def ring (red : parse (tk "!")?) : tactic unit :=
ring1 red <|>
(ring_nf red normalize_mode.horner (loc.ns [none]) >> trace "Try this: ring_nf")

add_hint_tactic "ring"

add_tactic_doc
{ name        := "ring",
  category    := doc_category.tactic,
  decl_names  := [``ring, ``ring_nf, ``ring1],
  inherit_description_from := ``ring,
  tags        := ["arithmetic", "simplification", "decision procedure"] }

end interactive
end tactic

namespace conv.interactive
open conv interactive
open tactic tactic.interactive (ring.mode ring1)
open tactic.ring (normalize normalize_mode.horner)

local postfix `?`:9001 := optional

/--
Normalises expressions in commutative (semi-)rings inside of a `conv` block using the tactic `ring`.
-/
meta def ring_nf (red : parse (lean.parser.tk "!")?) (SOP : parse ring.mode) : conv unit :=
let transp := if red.is_some then semireducible else reducible in
replace_lhs (normalize transp SOP)
<|> fail "ring_nf failed to simplify"

/--
Normalises expressions in commutative (semi-)rings inside of a `conv` block using the tactic `ring`.
-/
meta def ring (red : parse (lean.parser.tk "!")?) : conv unit :=
let transp := if red.is_some then semireducible else reducible in
discharge_eq_lhs (ring1 red)
<|> (replace_lhs (normalize transp normalize_mode.horner) >> trace "Try this: ring_nf")
<|> fail "ring failed to simplify"

end conv.interactive
