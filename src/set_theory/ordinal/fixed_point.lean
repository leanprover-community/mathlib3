/-
Copyright (c) 2018 Violeta Hernández Palacios, Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Mario Carneiro
-/

import set_theory.ordinal.arithmetic
import set_theory.ordinal.exponential

/-!
# Fixed points of normal functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We prove various statements about the fixed points of normal ordinal functions. We state them in
three forms: as statements about type-indexed families of normal functions, as statements about
ordinal-indexed families of normal functions, and as statements about a single normal function. For
the most part, the first case encompasses the others.

Moreover, we prove some lemmas about the fixed points of specific normal functions.

## Main definitions and results

* `nfp_family`, `nfp_bfamily`, `nfp`: the next fixed point of a (family of) normal function(s).
* `fp_family_unbounded`, `fp_bfamily_unbounded`, `fp_unbounded`: the (common) fixed points of a
  (family of) normal function(s) are unbounded in the ordinals.
* `deriv_add_eq_mul_omega_add`: a characterization of the derivative of addition.
* `deriv_mul_eq_opow_omega_mul`: a characterization of the derivative of multiplication.
-/

noncomputable theory

universes u v

open function order

namespace ordinal

/-! ### Fixed points of type-indexed families of ordinals -/

section
variables {ι : Type u} {f : ι → ordinal.{max u v} → ordinal.{max u v}}

/-- The next common fixed point, at least `a`, for a family of normal functions.

This is defined for any family of functions, as the supremum of all values reachable by applying
finitely many functions in the family to `a`.

`ordinal.nfp_family_fp` shows this is a fixed point, `ordinal.le_nfp_family` shows it's at
least `a`, and `ordinal.nfp_family_le_fp` shows this is the least ordinal with these properties. -/
def nfp_family (f : ι → ordinal → ordinal) (a) : ordinal :=
sup (list.foldr f a)

theorem nfp_family_eq_sup (f : ι → ordinal → ordinal) (a) :
  nfp_family f a = sup (list.foldr f a) :=
rfl

theorem foldr_le_nfp_family (f : ι → ordinal → ordinal) (a l) :
  list.foldr f a l ≤ nfp_family f a :=
le_sup _ _

theorem le_nfp_family (f : ι → ordinal → ordinal) (a) : a ≤ nfp_family f a :=
le_sup _ []

theorem lt_nfp_family {a b} : a < nfp_family f b ↔ ∃ l, a < list.foldr f b l :=
lt_sup

theorem nfp_family_le_iff {a b} : nfp_family f a ≤ b ↔ ∀ l, list.foldr f a l ≤ b :=
sup_le_iff

theorem nfp_family_le {a b} : (∀ l, list.foldr f a l ≤ b) → nfp_family f a ≤ b :=
sup_le

theorem nfp_family_monotone (hf : ∀ i, monotone (f i)) : monotone (nfp_family f) :=
λ a b h, sup_le $ λ l, (list.foldr_monotone hf l h).trans (le_sup _ l)

theorem apply_lt_nfp_family (H : ∀ i, is_normal (f i)) {a b} (hb : b < nfp_family f a) (i) :
  f i b < nfp_family f a :=
let ⟨l, hl⟩ := lt_nfp_family.1 hb in lt_sup.2 ⟨i :: l, (H i).strict_mono hl⟩

theorem apply_lt_nfp_family_iff [nonempty ι] (H : ∀ i, is_normal (f i)) {a b} :
  (∀ i, f i b < nfp_family f a) ↔ b < nfp_family f a :=
⟨λ h, lt_nfp_family.2 $ let ⟨l, hl⟩ := lt_sup.1 $ h $ classical.arbitrary ι in
  ⟨l, ((H _).self_le b).trans_lt hl⟩, apply_lt_nfp_family H⟩

theorem nfp_family_le_apply [nonempty ι] (H : ∀ i, is_normal (f i)) {a b} :
  (∃ i, nfp_family f a ≤ f i b) ↔ nfp_family f a ≤ b :=
by { rw ←not_iff_not, push_neg, exact apply_lt_nfp_family_iff H }

theorem nfp_family_le_fp (H : ∀ i, monotone (f i)) {a b} (ab : a ≤ b) (h : ∀ i, f i b ≤ b) :
  nfp_family f a ≤ b :=
sup_le $ λ l, begin
  by_cases hι : is_empty ι,
  { resetI, rwa unique.eq_default l },
  { haveI := not_is_empty_iff.1 hι,
    induction l with i l IH generalizing a, {exact ab},
    exact (H i (IH ab)).trans (h i) }
end

theorem nfp_family_fp {i} (H : is_normal (f i)) (a) : f i (nfp_family f a) = nfp_family f a :=
begin
  unfold nfp_family,
  rw @is_normal.sup _ H _ _ ⟨[]⟩,
  apply le_antisymm;
  refine ordinal.sup_le (λ l, _),
  { exact le_sup _ (i :: l) },
  { exact (H.self_le _).trans (le_sup _ _) }
end

theorem apply_le_nfp_family [hι : nonempty ι] {f : ι → ordinal → ordinal} (H : ∀ i, is_normal (f i))
  {a b} : (∀ i, f i b ≤ nfp_family f a) ↔ b ≤ nfp_family f a :=
begin
  refine ⟨λ h, _, λ h i, _⟩,
  { unfreezingI { cases hι with i },
    exact ((H i).self_le b).trans (h i) },
  rw ←nfp_family_fp (H i),
  exact (H i).monotone h
end

theorem nfp_family_eq_self {f : ι → ordinal → ordinal} {a} (h : ∀ i, f i a = a) :
  nfp_family f a = a :=
le_antisymm (sup_le $ λ l, by rw list.foldr_fixed' h l) $ le_nfp_family f a

/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
-- Todo: This is actually a special case of the fact the intersection of club sets is a club set.
theorem fp_family_unbounded (H : ∀ i, is_normal (f i)) :
  (⋂ i, function.fixed_points (f i)).unbounded (<) :=
λ a, ⟨_, λ s ⟨i, hi⟩, begin
  rw ←hi,
  exact nfp_family_fp (H i) a
end, (le_nfp_family f a).not_lt⟩

/-- The derivative of a family of normal functions is the sequence of their common fixed points.

This is defined for all functions such that `ordinal.deriv_family_zero`,
`ordinal.deriv_family_succ`, and `ordinal.deriv_family_limit` are satisfied. -/
def deriv_family (f : ι → ordinal → ordinal) (o : ordinal) : ordinal :=
limit_rec_on o (nfp_family f 0)
  (λ a IH, nfp_family f (succ IH))
  (λ a l, bsup.{(max u v) u} a)

@[simp] theorem deriv_family_zero (f : ι → ordinal → ordinal) :
  deriv_family f 0 = nfp_family f 0 :=
limit_rec_on_zero _ _ _

@[simp] theorem deriv_family_succ (f : ι → ordinal → ordinal) (o) :
  deriv_family f (succ o) = nfp_family f (succ (deriv_family f o)) :=
limit_rec_on_succ _ _ _ _

theorem deriv_family_limit (f : ι → ordinal → ordinal) {o} : is_limit o →
  deriv_family f o = bsup.{(max u v) u} o (λ a _, deriv_family f a) :=
limit_rec_on_limit _ _ _ _

theorem deriv_family_is_normal (f : ι → ordinal → ordinal) : is_normal (deriv_family f) :=
⟨λ o, by rw [deriv_family_succ, ← succ_le_iff]; apply le_nfp_family,
 λ o l a, by rw [deriv_family_limit _ l, bsup_le_iff]⟩

theorem deriv_family_fp {i} (H : is_normal (f i)) (o : ordinal.{max u v}) :
  f i (deriv_family f o) = deriv_family f o :=
begin
  refine limit_rec_on o _ (λ o IH, _) _,
  { rw [deriv_family_zero], exact nfp_family_fp H 0 },
  { rw [deriv_family_succ], exact nfp_family_fp H _ },
  { intros o l IH,
    rw [deriv_family_limit _ l,
      is_normal.bsup.{(max u v) u (max u v)} H (λ a _, deriv_family f a) l.1],
    refine eq_of_forall_ge_iff (λ c, _),
    simp only [bsup_le_iff, IH] {contextual:=tt} }
end

theorem le_iff_deriv_family (H : ∀ i, is_normal (f i)) {a} :
  (∀ i, f i a ≤ a) ↔ ∃ o, deriv_family f o = a :=
⟨λ ha, begin
  suffices : ∀ o (_ : a ≤ deriv_family f o), ∃ o, deriv_family f o = a,
  from this a ((deriv_family_is_normal _).self_le _),
  refine λ o, limit_rec_on o (λ h₁, ⟨0, le_antisymm _ h₁⟩) (λ o IH h₁, _) (λ o l IH h₁, _),
  { rw deriv_family_zero,
    exact nfp_family_le_fp (λ i, (H i).monotone) (ordinal.zero_le _) ha },
  { cases le_or_lt a (deriv_family f o), {exact IH h},
    refine ⟨succ o, le_antisymm _ h₁⟩,
    rw deriv_family_succ,
    exact nfp_family_le_fp (λ i, (H i).monotone) (succ_le_of_lt h) ha },
  { cases eq_or_lt_of_le h₁, {exact ⟨_, h.symm⟩},
    rw [deriv_family_limit _ l, ← not_le, bsup_le_iff, not_ball] at h,
    exact let ⟨o', h, hl⟩ := h in IH o' h (le_of_not_le hl) }
end, λ ⟨o, e⟩ i, e ▸ (deriv_family_fp (H i) _).le⟩

theorem fp_iff_deriv_family (H : ∀ i, is_normal (f i)) {a} :
  (∀ i, f i a = a) ↔ ∃ o, deriv_family f o = a :=
iff.trans ⟨λ h i, le_of_eq (h i), λ h i, (H i).le_iff_eq.1 (h i)⟩ (le_iff_deriv_family H)

/-- For a family of normal functions, `ordinal.deriv_family` enumerates the common fixed points. -/
theorem deriv_family_eq_enum_ord (H : ∀ i, is_normal (f i)) :
  deriv_family f = enum_ord (⋂ i, function.fixed_points (f i)) :=
begin
  rw ←eq_enum_ord _ (fp_family_unbounded H),
  use (deriv_family_is_normal f).strict_mono,
  rw set.range_eq_iff,
  refine ⟨_, λ a ha, _⟩,
  { rintros a S ⟨i, hi⟩,
    rw ←hi,
    exact deriv_family_fp (H i) a },
  rw set.mem_Inter at ha,
  rwa ←fp_iff_deriv_family H
end

end

/-! ### Fixed points of ordinal-indexed families of ordinals -/

section
variables {o : ordinal.{u}} {f : Π b < o, ordinal.{max u v} → ordinal.{max u v}}

/-- The next common fixed point, at least `a`, for a family of normal functions indexed by ordinals.

This is defined as `ordinal.nfp_family` of the type-indexed family associated to `f`.
-/
def nfp_bfamily (o : ordinal) (f : Π b < o, ordinal → ordinal) : ordinal → ordinal :=
nfp_family (family_of_bfamily o f)

theorem nfp_bfamily_eq_nfp_family {o : ordinal} (f : Π b < o, ordinal → ordinal) :
  nfp_bfamily o f = nfp_family (family_of_bfamily o f) :=
rfl

theorem foldr_le_nfp_bfamily {o : ordinal} (f : Π b < o, ordinal → ordinal) (a l) :
  list.foldr (family_of_bfamily o f) a l ≤ nfp_bfamily o f a :=
le_sup _ _

theorem le_nfp_bfamily {o : ordinal} (f : Π b < o, ordinal → ordinal) (a) :
  a ≤ nfp_bfamily o f a :=
le_sup _ []

theorem lt_nfp_bfamily {a b} :
  a < nfp_bfamily o f b ↔ ∃ l, a < list.foldr (family_of_bfamily o f) b l :=
lt_sup

theorem nfp_bfamily_le_iff {o : ordinal} {f : Π b < o, ordinal → ordinal} {a b} :
  nfp_bfamily o f a ≤ b ↔ ∀ l, list.foldr (family_of_bfamily o f) a l ≤ b :=
sup_le_iff

theorem nfp_bfamily_le {o : ordinal} {f : Π b < o, ordinal → ordinal} {a b} :
  (∀ l, list.foldr (family_of_bfamily o f) a l ≤ b) → nfp_bfamily o f a ≤ b :=
sup_le

theorem nfp_bfamily_monotone (hf : ∀ i hi, monotone (f i hi)) : monotone (nfp_bfamily o f) :=
nfp_family_monotone (λ i, hf _ _)

theorem apply_lt_nfp_bfamily (H : ∀ i hi, is_normal (f i hi)) {a b} (hb : b < nfp_bfamily o f a)
  (i hi) : f i hi b < nfp_bfamily o f a :=
begin
  rw ←family_of_bfamily_enum o f,
  apply apply_lt_nfp_family _ hb,
  exact λ _, H _ _
end

theorem apply_lt_nfp_bfamily_iff (ho : o ≠ 0) (H : ∀ i hi, is_normal (f i hi)) {a b} :
  (∀ i hi, f i hi b < nfp_bfamily o f a) ↔ b < nfp_bfamily o f a :=
⟨λ h, begin
  haveI := out_nonempty_iff_ne_zero.2 ho,
  refine (apply_lt_nfp_family_iff _).1 (λ _, h _ _),
  exact λ _, H _ _,
end, apply_lt_nfp_bfamily H⟩

theorem nfp_bfamily_le_apply (ho : o ≠ 0) (H : ∀ i hi, is_normal (f i hi)) {a b} :
  (∃ i hi, nfp_bfamily o f a ≤ f i hi b) ↔ nfp_bfamily o f a ≤ b :=
by { rw ←not_iff_not, push_neg, convert apply_lt_nfp_bfamily_iff ho H, simp only [not_le] }

theorem nfp_bfamily_le_fp (H : ∀ i hi, monotone (f i hi)) {a b} (ab : a ≤ b)
  (h : ∀ i hi, f i hi b ≤ b) : nfp_bfamily o f a ≤ b :=
nfp_family_le_fp (λ _, H _ _) ab (λ i, h _ _)

theorem nfp_bfamily_fp {i hi} (H : is_normal (f i hi)) (a) :
  f i hi (nfp_bfamily o f a) = nfp_bfamily o f a :=
by { rw ←family_of_bfamily_enum o f, apply nfp_family_fp, rw family_of_bfamily_enum, exact H }

theorem apply_le_nfp_bfamily (ho : o ≠ 0) (H : ∀ i hi, is_normal (f i hi)) {a b} :
  (∀ i hi, f i hi b ≤ nfp_bfamily o f a) ↔ b ≤ nfp_bfamily o f a :=
begin
  refine ⟨λ h, _, λ h i hi, _⟩,
  { have ho' : 0 < o := ordinal.pos_iff_ne_zero.2 ho,
    exact ((H 0 ho').self_le b).trans (h 0 ho') },
  { rw ←nfp_bfamily_fp (H i hi),
    exact (H i hi).monotone h }
end

theorem nfp_bfamily_eq_self {a} (h : ∀ i hi, f i hi a = a) : nfp_bfamily o f a = a :=
nfp_family_eq_self (λ _, h _ _)

/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
theorem fp_bfamily_unbounded (H : ∀ i hi, is_normal (f i hi)) :
  (⋂ i hi, function.fixed_points (f i hi)).unbounded (<) :=
λ a, ⟨_, by { rw set.mem_Inter₂, exact λ i hi, nfp_bfamily_fp (H i hi) _ },
  (le_nfp_bfamily f a).not_lt⟩

/-- The derivative of a family of normal functions is the sequence of their common fixed points.

This is defined as `ordinal.deriv_family` of the type-indexed family associated to `f`. -/
def deriv_bfamily (o : ordinal) (f : Π b < o, ordinal → ordinal) : ordinal → ordinal :=
deriv_family (family_of_bfamily o f)

theorem deriv_bfamily_eq_deriv_family {o : ordinal} (f : Π b < o, ordinal → ordinal) :
  deriv_bfamily o f = deriv_family (family_of_bfamily o f) :=
rfl

theorem deriv_bfamily_is_normal {o : ordinal} (f : Π b < o, ordinal → ordinal) :
  is_normal (deriv_bfamily o f) :=
deriv_family_is_normal _

theorem deriv_bfamily_fp {i hi} (H : is_normal (f i hi)) (a : ordinal) :
  f i hi (deriv_bfamily o f a) = deriv_bfamily o f a :=
by { rw ←family_of_bfamily_enum o f, apply deriv_family_fp, rw family_of_bfamily_enum, exact H }

theorem le_iff_deriv_bfamily (H : ∀ i hi, is_normal (f i hi)) {a} :
  (∀ i hi, f i hi a ≤ a) ↔ ∃ b, deriv_bfamily o f b = a :=
begin
  unfold deriv_bfamily,
  rw ←le_iff_deriv_family,
  { refine ⟨λ h i, h _ _, λ h i hi, _⟩,
    rw ←family_of_bfamily_enum o f,
    apply h },
  { exact λ _, H _ _ }
end

theorem fp_iff_deriv_bfamily (H : ∀ i hi, is_normal (f i hi)) {a} :
  (∀ i hi, f i hi a = a) ↔ ∃ b, deriv_bfamily o f b = a :=
begin
  rw ←le_iff_deriv_bfamily H,
  refine ⟨λ h i hi, le_of_eq (h i hi), λ h i hi, _⟩,
  rw ←(H i hi).le_iff_eq,
  exact h i hi
end

/-- For a family of normal functions, `ordinal.deriv_bfamily` enumerates the common fixed points. -/
theorem deriv_bfamily_eq_enum_ord (H : ∀ i hi, is_normal (f i hi)) :
  deriv_bfamily o f = enum_ord (⋂ i hi, function.fixed_points (f i hi)) :=
begin
  rw ←eq_enum_ord _ (fp_bfamily_unbounded H),
  use (deriv_bfamily_is_normal f).strict_mono,
  rw set.range_eq_iff,
  refine ⟨λ a, set.mem_Inter₂.2 (λ i hi, deriv_bfamily_fp (H i hi) a), λ a ha, _⟩,
  rw set.mem_Inter₂ at ha,
  rwa ←fp_iff_deriv_bfamily H
end

end

/-! ### Fixed points of a single function -/

section
variable {f : ordinal.{u} → ordinal.{u}}

/-- The next fixed point function, the least fixed point of the normal function `f`, at least `a`.

This is defined as `ordinal.nfp_family` applied to a family consisting only of `f`. -/
def nfp (f : ordinal → ordinal) : ordinal → ordinal :=
nfp_family (λ _ : unit, f)

theorem nfp_eq_nfp_family (f : ordinal → ordinal) : nfp f = nfp_family (λ _ : unit, f) :=
rfl

@[simp] theorem sup_iterate_eq_nfp (f : ordinal.{u} → ordinal.{u}) :
  (λ a, sup (λ n : ℕ, f^[n] a)) = nfp f :=
begin
  refine funext (λ a, le_antisymm _ (sup_le (λ l, _))),
  { rw sup_le_iff,
    intro n,
    rw [←list.length_replicate n unit.star, ←list.foldr_const f a],
    apply le_sup },
  { rw list.foldr_const f a l,
    exact le_sup _ _ },
end

theorem iterate_le_nfp (f a n) : f^[n] a ≤ nfp f a :=
by { rw ←sup_iterate_eq_nfp, exact le_sup _ n }

theorem le_nfp (f a) : a ≤ nfp f a :=
iterate_le_nfp f a 0

theorem lt_nfp {a b} : a < nfp f b ↔ ∃ n, a < (f^[n]) b :=
by { rw ←sup_iterate_eq_nfp, exact lt_sup }

theorem nfp_le_iff {a b} : nfp f a ≤ b ↔ ∀ n, (f^[n]) a ≤ b :=
by { rw ←sup_iterate_eq_nfp, exact sup_le_iff }

theorem nfp_le {a b} : (∀ n, (f^[n]) a ≤ b) → nfp f a ≤ b := nfp_le_iff.2

@[simp] theorem nfp_id : nfp id = id :=
funext (λ a, begin
  simp_rw [←sup_iterate_eq_nfp, iterate_id],
  exact sup_const a
end)

theorem nfp_monotone (hf : monotone f) : monotone (nfp f) :=
nfp_family_monotone (λ i, hf)

theorem is_normal.apply_lt_nfp {f} (H : is_normal f) {a b} :
  f b < nfp f a ↔ b < nfp f a :=
begin
  unfold nfp,
  rw ←@apply_lt_nfp_family_iff unit (λ _, f) _ (λ _, H) a b,
  exact ⟨λ h _, h, λ h, h unit.star⟩
end

theorem is_normal.nfp_le_apply {f} (H : is_normal f) {a b} : nfp f a ≤ f b ↔ nfp f a ≤ b :=
le_iff_le_iff_lt_iff_lt.2 H.apply_lt_nfp

theorem nfp_le_fp {f} (H : monotone f) {a b} (ab : a ≤ b) (h : f b ≤ b) : nfp f a ≤ b :=
nfp_family_le_fp (λ _, H) ab (λ _, h)

theorem is_normal.nfp_fp {f} (H : is_normal f) : ∀ a, f (nfp f a) = nfp f a :=
@nfp_family_fp unit (λ _, f) unit.star H

theorem is_normal.apply_le_nfp {f} (H : is_normal f) {a b} :
  f b ≤ nfp f a ↔ b ≤ nfp f a :=
⟨le_trans (H.self_le _), λ h, by simpa only [H.nfp_fp] using H.le_iff.2 h⟩

theorem nfp_eq_self {f : ordinal → ordinal} {a} (h : f a = a) : nfp f a = a :=
nfp_family_eq_self (λ _, h)

/-- The fixed point lemma for normal functions: any normal function has an unbounded set of
fixed points. -/
theorem fp_unbounded (H : is_normal f) : (function.fixed_points f).unbounded (<) :=
by { convert fp_family_unbounded (λ _ : unit, H), exact (set.Inter_const _).symm }

/-- The derivative of a normal function `f` is the sequence of fixed points of `f`.

This is defined as `ordinal.deriv_family` applied to a trivial family consisting only of `f`. -/
def deriv (f : ordinal → ordinal) : ordinal → ordinal :=
deriv_family (λ _ : unit, f)

theorem deriv_eq_deriv_family (f : ordinal → ordinal) : deriv f = deriv_family (λ _ : unit, f) :=
rfl

@[simp] theorem deriv_zero (f) : deriv f 0 = nfp f 0 :=
deriv_family_zero _

@[simp] theorem deriv_succ (f o) : deriv f (succ o) = nfp f (succ (deriv f o)) :=
deriv_family_succ _ _

theorem deriv_limit (f) {o} : is_limit o → deriv f o = bsup.{u 0} o (λ a _, deriv f a) :=
deriv_family_limit _

theorem deriv_is_normal (f) : is_normal (deriv f) :=
deriv_family_is_normal _

theorem deriv_id_of_nfp_id {f : ordinal → ordinal} (h : nfp f = id) : deriv f = id :=
((deriv_is_normal _).eq_iff_zero_and_succ is_normal.refl).2 (by simp [h])

theorem is_normal.deriv_fp {f} (H : is_normal f) : ∀ o, f (deriv f o) = deriv f o :=
@deriv_family_fp unit (λ _, f) unit.star H

theorem is_normal.le_iff_deriv {f} (H : is_normal f) {a} : f a ≤ a ↔ ∃ o, deriv f o = a :=
begin
  unfold deriv,
  rw ←le_iff_deriv_family (λ _ : unit, H),
  exact ⟨λ h _, h, λ h, h unit.star⟩
end

theorem is_normal.fp_iff_deriv {f} (H : is_normal f) {a} : f a = a ↔ ∃ o, deriv f o = a :=
by rw [←H.le_iff_eq, H.le_iff_deriv]

/-- `ordinal.deriv` enumerates the fixed points of a normal function. -/
theorem deriv_eq_enum_ord (H : is_normal f) : deriv f = enum_ord (function.fixed_points f) :=
by { convert deriv_family_eq_enum_ord (λ _ : unit, H), exact (set.Inter_const _).symm }

theorem deriv_eq_id_of_nfp_eq_id {f : ordinal → ordinal} (h : nfp f = id) : deriv f = id :=
(is_normal.eq_iff_zero_and_succ (deriv_is_normal _) is_normal.refl).2 $ by simp [h]

end

/-! ### Fixed points of addition -/

@[simp] theorem nfp_add_zero (a) : nfp ((+) a) 0 = a * omega :=
begin
  simp_rw [←sup_iterate_eq_nfp, ←sup_mul_nat],
  congr, funext,
  induction n with n hn,
  { rw [nat.cast_zero, mul_zero, iterate_zero_apply] },
  { nth_rewrite 1 nat.succ_eq_one_add,
    rw [nat.cast_add, nat.cast_one, mul_one_add, iterate_succ_apply', hn] }
end

theorem nfp_add_eq_mul_omega {a b} (hba : b ≤ a * omega) :
  nfp ((+) a) b = a * omega :=
begin
  apply le_antisymm (nfp_le_fp (add_is_normal a).monotone hba _),
  { rw ←nfp_add_zero,
    exact nfp_monotone (add_is_normal a).monotone (ordinal.zero_le b) },
  { rw [←mul_one_add, one_add_omega] }
end

theorem add_eq_right_iff_mul_omega_le {a b : ordinal} : a + b = b ↔ a * omega ≤ b :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw [←nfp_add_zero a, ←deriv_zero],
    cases (add_is_normal a).fp_iff_deriv.1 h with c hc,
    rw ←hc,
    exact (deriv_is_normal _).monotone (ordinal.zero_le _) },
  { have := ordinal.add_sub_cancel_of_le h,
    nth_rewrite 0 ←this,
    rwa [←add_assoc, ←mul_one_add, one_add_omega] }
end

theorem add_le_right_iff_mul_omega_le {a b : ordinal} : a + b ≤ b ↔ a * omega ≤ b :=
by { rw ←add_eq_right_iff_mul_omega_le, exact (add_is_normal a).le_iff_eq }

theorem deriv_add_eq_mul_omega_add (a b : ordinal.{u}) : deriv ((+) a) b = a * omega + b :=
begin
  revert b,
  rw [←funext_iff, is_normal.eq_iff_zero_and_succ (deriv_is_normal _) (add_is_normal _)],
  refine ⟨_, λ a h, _⟩,
  { rw [deriv_zero, add_zero],
    exact nfp_add_zero a },
  { rw [deriv_succ, h, add_succ],
    exact nfp_eq_self (add_eq_right_iff_mul_omega_le.2 ((le_add_right _ _).trans (le_succ _))) }
end

/-! ### Fixed points of multiplication -/

local infixr (name := ordinal.pow) ^ := @pow ordinal ordinal ordinal.has_pow
@[simp] theorem nfp_mul_one {a : ordinal} (ha : 0 < a) : nfp ((*) a) 1 = a ^ omega :=
begin
  rw [←sup_iterate_eq_nfp, ←sup_opow_nat],
  { dsimp, congr, funext,
    induction n with n hn,
    { rw [nat.cast_zero, opow_zero, iterate_zero_apply] },
    nth_rewrite 1 nat.succ_eq_one_add,
    rw [nat.cast_add, nat.cast_one, opow_add, opow_one, iterate_succ_apply', hn] },
  { exact ha }
end

@[simp] theorem nfp_mul_zero (a : ordinal) : nfp ((*) a) 0 = 0 :=
begin
  rw [←ordinal.le_zero, nfp_le_iff],
  intro n,
  induction n with n hn, { refl },
  rwa [iterate_succ_apply, mul_zero]
end

@[simp] theorem nfp_zero_mul : nfp ((*) 0) = id :=
begin
  rw ←sup_iterate_eq_nfp,
  refine funext (λ a, (sup_le (λ n, _)).antisymm (le_sup (λ n, ((*) 0)^[n] a) 0)),
  induction n with n hn, { refl },
  rw function.iterate_succ',
  change 0 * _ ≤ a,
  rw zero_mul,
  exact ordinal.zero_le a
end

@[simp] theorem deriv_mul_zero : deriv ((*) 0) = id :=
deriv_eq_id_of_nfp_eq_id nfp_zero_mul

theorem nfp_mul_eq_opow_omega {a b : ordinal} (hb : 0 < b) (hba : b ≤ a ^ omega) :
  nfp ((*) a) b = a ^ omega.{u} :=
begin
  cases eq_zero_or_pos a with ha ha,
  { rw [ha, zero_opow omega_ne_zero] at *,
    rw [ordinal.le_zero.1 hba, nfp_zero_mul],
    refl },
  apply le_antisymm,
  { apply nfp_le_fp (mul_is_normal ha).monotone hba,
    rw [←opow_one_add, one_add_omega] },
  rw ←nfp_mul_one ha,
  exact nfp_monotone (mul_is_normal ha).monotone (one_le_iff_pos.2 hb)
end

theorem eq_zero_or_opow_omega_le_of_mul_eq_right {a b : ordinal} (hab : a * b = b) :
  b = 0 ∨ a ^ omega.{u} ≤ b :=
begin
  cases eq_zero_or_pos a with ha ha,
  { rw [ha, zero_opow omega_ne_zero],
    exact or.inr (ordinal.zero_le b) },
  rw or_iff_not_imp_left,
  intro hb,
  change b ≠ 0 at hb,
  rw ←nfp_mul_one ha,
  rw ←one_le_iff_ne_zero at hb,
  exact nfp_le_fp (mul_is_normal ha).monotone hb (le_of_eq hab)
end

theorem mul_eq_right_iff_opow_omega_dvd {a b : ordinal} : a * b = b ↔ a ^ omega ∣ b :=
begin
  cases eq_zero_or_pos a with ha ha,
  { rw [ha, zero_mul, zero_opow omega_ne_zero, zero_dvd_iff],
    exact eq_comm },
  refine ⟨λ hab, _, λ h, _⟩,
  { rw dvd_iff_mod_eq_zero,
    rw [←div_add_mod b (a ^ omega), mul_add, ←mul_assoc, ←opow_one_add, one_add_omega,
      add_left_cancel] at hab,
    cases eq_zero_or_opow_omega_le_of_mul_eq_right hab with hab hab,
    { exact hab },
    refine (not_lt_of_le hab (mod_lt b (opow_ne_zero omega _))).elim,
    rwa ←ordinal.pos_iff_ne_zero },
  cases h with c hc,
  rw [hc, ←mul_assoc, ←opow_one_add, one_add_omega]
end

theorem mul_le_right_iff_opow_omega_dvd {a b : ordinal} (ha : 0 < a) : a * b ≤ b ↔ a ^ omega ∣ b :=
by { rw ←mul_eq_right_iff_opow_omega_dvd, exact (mul_is_normal ha).le_iff_eq }

theorem nfp_mul_opow_omega_add {a c : ordinal} (b) (ha : 0 < a) (hc : 0 < c) (hca : c ≤ a ^ omega) :
  nfp ((*) a) (a ^ omega * b + c) = a ^ omega.{u} * (succ b) :=
begin
  apply le_antisymm,
  { apply nfp_le_fp (mul_is_normal ha).monotone,
    { rw mul_succ,
      apply add_le_add_left hca },
    { rw [←mul_assoc, ←opow_one_add, one_add_omega] } },
  { cases mul_eq_right_iff_opow_omega_dvd.1 ((mul_is_normal ha).nfp_fp (a ^ omega * b + c))
      with d hd,
    rw hd,
    apply mul_le_mul_left',
    have := le_nfp (has_mul.mul a) (a ^ omega * b + c),
    rw hd at this,
    have := (add_lt_add_left hc (a ^ omega * b)).trans_le this,
    rw [add_zero, mul_lt_mul_iff_left (opow_pos omega ha)] at this,
    rwa succ_le_iff }
end

theorem deriv_mul_eq_opow_omega_mul {a : ordinal.{u}} (ha : 0 < a) (b) :
  deriv ((*) a) b = a ^ omega * b :=
begin
  revert b,
  rw [←funext_iff,
    is_normal.eq_iff_zero_and_succ (deriv_is_normal _) (mul_is_normal (opow_pos omega ha))],
  refine ⟨_, λ c h, _⟩,
  { rw [deriv_zero, nfp_mul_zero, mul_zero] },
  { rw [deriv_succ, h],
    exact nfp_mul_opow_omega_add c ha zero_lt_one (one_le_iff_pos.2 (opow_pos _ ha)) },
end

end ordinal
