/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import set_theory.ordinal_arithmetic

/-!
# Fixed points of normal functions

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
-/

noncomputable theory

universes u v

open function

namespace ordinal

/-! ### Fixed points of type-indexed families of ordinals -/

section
variables {ι : Type u} {f : ι → ordinal.{max u v} → ordinal.{max u v}}

/-- The next common fixed point, at least `a`, for a family of normal functions.

`ordinal.nfp_family_fp` shows this is a fixed point, `ordinal.self_le_nfp_family` shows it's at
least `a`, and `ordinal.nfp_family_le_fp` shows this is the least ordinal with these properties. -/
def nfp_family (f : ι → ordinal → ordinal) (a) : ordinal :=
sup (list.foldr f a)

theorem nfp_family_eq_sup (f : ι → ordinal → ordinal) (a) :
  nfp_family f a = sup (list.foldr f a) :=
rfl

theorem foldr_le_nfp_family (f : ι → ordinal → ordinal) (a l) :
  list.foldr f a l ≤ nfp_family f a :=
le_sup _ _

theorem self_le_nfp_family (f : ι → ordinal → ordinal) (a) : a ≤ nfp_family f a :=
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
⟨λ h, lt_nfp_family.2 $ let ⟨l, hl⟩ := lt_sup.1 (h (classical.arbitrary ι)) in
  ⟨l, ((H _).self_le b).trans_lt hl⟩, apply_lt_nfp_family H⟩

theorem nfp_family_le_apply [nonempty ι] (H : ∀ i, is_normal (f i)) {a b} :
  (∃ i, nfp_family f a ≤ f i b) ↔ nfp_family f a ≤ b :=
by { rw ←not_iff_not, push_neg, exact apply_lt_nfp_family_iff H }

theorem nfp_family_le_fp (H : ∀ i, monotone (f i)) {a b} (ab : a ≤ b) (h : ∀ i, f i b ≤ b) :
  nfp_family f a ≤ b :=
sup_le $ λ l, begin
  by_cases hι : is_empty ι,
  { rwa @unique.eq_default _ (@list.unique_of_is_empty ι hι) l },
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
le_antisymm (sup_le (λ l, (by rw list.foldr_fixed' h l))) (self_le_nfp_family f a)

/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
theorem fp_family_unbounded (H : ∀ i, is_normal (f i)) :
  (⋂ i, function.fixed_points (f i)).unbounded (<) :=
λ a, ⟨_, λ s ⟨i, hi⟩, begin
  rw ←hi,
  exact nfp_family_fp (H i) a
end, (self_le_nfp_family f a).not_lt⟩

/-- The derivative of a family of normal functions is the sequence of their common fixed points. -/
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
⟨λ o, by rw [deriv_family_succ, ← succ_le]; apply self_le_nfp_family,
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
    exact nfp_family_le_fp (λ i, (H i).monotone) (succ_le.2 h) ha },
  { cases eq_or_lt_of_le h₁, {exact ⟨_, h.symm⟩},
    rw [deriv_family_limit _ l, ← not_le, bsup_le_iff, not_ball] at h,
    exact let ⟨o', h, hl⟩ := h in IH o' h (le_of_not_le hl) }
end, λ ⟨o, e⟩ i, e ▸ le_of_eq (deriv_family_fp (H i) _)⟩

theorem fp_iff_deriv_family (H : ∀ i, is_normal (f i)) {a} :
  (∀ i, f i a = a) ↔ ∃ o, deriv_family f o = a :=
iff.trans ⟨λ h i, le_of_eq (h i), λ h i, (H i).le_iff_eq.1 (h i)⟩ (le_iff_deriv_family H)

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
-/
def nfp_bfamily (o : ordinal) (f : Π b < o, ordinal → ordinal) : ordinal → ordinal :=
nfp_family (family_of_bfamily o f)

theorem nfp_bfamily_eq_nfp_family {o : ordinal} (f : Π b < o, ordinal → ordinal) :
  nfp_bfamily o f = nfp_family (family_of_bfamily o f) :=
rfl

theorem foldr_le_nfp_bfamily {o : ordinal} (f : Π b < o, ordinal → ordinal) (a l) :
  list.foldr (family_of_bfamily o f) a l ≤ nfp_bfamily o f a :=
le_sup _ _

theorem self_le_nfp_bfamily {o : ordinal} (f : Π b < o, ordinal → ordinal) (a) :
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

theorem apply_lt_nfp_bfamily (ho : o ≠ 0) (H : ∀ i hi, is_normal (f i hi)) {a b} :
  (∀ i hi, f i hi b < nfp_bfamily o f a) ↔ b < nfp_bfamily o f a :=
begin
  unfold nfp_bfamily,
  rw ←@apply_lt_nfp_family_iff _ (family_of_bfamily o f) (out_nonempty_iff_ne_zero.2 ho)
    (λ i, H _ _),
  refine ⟨λ h i, h _ (typein_lt_self i), λ h i hio, _⟩,
  rw ←family_of_bfamily_enum o f,
  apply h
end

theorem nfp_bfamily_le_apply (ho : o ≠ 0) (H : ∀ i hi, is_normal (f i hi)) {a b} :
  (∃ i hi, nfp_bfamily o f a ≤ f i hi b) ↔ nfp_bfamily o f a ≤ b :=
by { rw ←not_iff_not, push_neg, convert apply_lt_nfp_bfamily ho H, simp only [not_le] }

theorem nfp_bfamily_le_fp (H : ∀ i hi, monotone (f i hi)) {a b} (ab : a ≤ b)
  (h : ∀ i hi, f i hi b ≤ b) : nfp_bfamily o f a ≤ b :=
nfp_family_le_fp (λ _, H _ _) ab (λ i, h _ _)

theorem nfp_bfamily_fp {i hi} (H : is_normal (f i hi)) (a) :
  f i hi (nfp_bfamily o f a) = nfp_bfamily o f a :=
by { rw ←family_of_bfamily_enum o f, apply nfp_family_fp, rw family_of_bfamily_enum, exact H }

theorem le_nfp_bfamily (ho : o ≠ 0) (H : ∀ i hi, is_normal (f i hi)) {a b} :
  (∀ i hi, f i hi b ≤ nfp_bfamily o f a) ↔ b ≤ nfp_bfamily o f a :=
begin
  refine ⟨λ h, _, λ h i hi, _⟩,
  { have ho' : 0 < o := ordinal.pos_iff_ne_zero.2 ho,
    exact ((H 0 ho').self_le b).trans (h 0 ho') },
  rw ←nfp_bfamily_fp (H i hi),
  exact (H i hi).monotone h
end

theorem nfp_bfamily_eq_self {a} (h : ∀ i hi, f i hi a = a) : nfp_bfamily o f a = a :=
nfp_family_eq_self (λ _, h _ _)

/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
theorem fp_bfamily_unbounded (H : ∀ i hi, is_normal (f i hi)) :
  (⋂ i hi, function.fixed_points (f i hi)).unbounded (<) :=
λ a, ⟨_, by { rw set.mem_Inter₂, exact λ i hi, nfp_bfamily_fp (H i hi) _ },
  (self_le_nfp_bfamily f a).not_lt⟩

/-- The derivative of a family of normal functions is the sequence of their common fixed points. -/
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
  exact λ _, H _ _
end

theorem fp_iff_deriv_bfamily (H : ∀ i hi, is_normal (f i hi)) {a} :
  (∀ i hi, f i hi a = a) ↔ ∃ b, deriv_bfamily o f b = a :=
begin
  rw ←le_iff_deriv_bfamily H,
  refine ⟨λ h i hi, le_of_eq (h i hi), λ h i hi, _⟩,
  rw ←(H i hi).le_iff_eq,
  exact h i hi
end

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
end ordinal
