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

universes u v w

open function

namespace ordinal

/-! ### Fixed points of type-indexed families of ordinals -/

section
variables {ι : Type u} {ι' : Type w} {f : ι → ordinal.{max u v} → ordinal.{max u v}}

/-- Applies the functions specified by the indices of a list, in order, to a specified value. -/
def nfp_family_iterate (f : ι → ordinal → ordinal) (a : ordinal) : list ι → ordinal
| []       := a
| (i :: l) := f i (nfp_family_iterate l)

@[simp] theorem nfp_family_iterate_nil (f : ι → ordinal → ordinal) (a) :
  nfp_family_iterate f a [] = a :=
rfl

@[simp] theorem nfp_family_iterate_cons (f : ι → ordinal → ordinal) (i l a) :
  nfp_family_iterate f a (i :: l) = f i (nfp_family_iterate f a l) :=
rfl

theorem nfp_family_iterate_empty [is_empty ι] (f : ι → ordinal → ordinal) (a) :
  Π l : list ι, nfp_family_iterate f a l = a
| []       := rfl
| (i :: l) := is_empty_elim i

theorem nfp_family_iterate_fixed {a} (ha : ∀ i, f i a = a) :
  Π l : list ι, nfp_family_iterate f a l = a
| []       := rfl
| (i :: l) := by { convert ha i, exact congr_arg (f i) (nfp_family_iterate_fixed l) }

theorem nfp_family_iterate_eq_iterate (f : ordinal → ordinal) (a) :
  Π l, nfp_family_iterate (λ _ : ι, f) a l = (f^[l.length]) a
| []       := rfl
| (i :: l) := begin
  convert congr_arg f (nfp_family_iterate_eq_iterate l),
  exact function.iterate_succ_apply' f _ a
end

theorem nfp_family_iterate_monotone {f : ι → ordinal → ordinal} (H : ∀ i, monotone (f i))
  (l : list ι) : monotone (λ a, nfp_family_iterate f a l) :=
λ a b h, list.rec_on l h (λ i l hl, H i hl)

theorem nfp_family_iterate_range_subset_of_range_subset {ι'} {f : ι → ordinal → ordinal}
  {g : ι' → ordinal → ordinal} (hfg : set.range f ⊆ set.range g) (a) :
  set.range (nfp_family_iterate f a) ⊆ set.range (nfp_family_iterate g a) :=
begin
  rintros x ⟨l, rfl⟩,
  induction l with i l hl,
  { exact ⟨[], rfl⟩ },
  { cases hfg ⟨i, rfl⟩ with i' hi',
    cases hl with l' hl',
    rw [nfp_family_iterate_cons, ←hi', ←hl'],
    exact ⟨i' :: l', rfl⟩ }
end

theorem nfp_family_iterate_range_eq_of_range_eq {ι'} {f : ι → ordinal → ordinal}
  {g : ι' → ordinal → ordinal} (hfg : set.range f = set.range g) (a) :
  set.range (nfp_family_iterate f a) = set.range (nfp_family_iterate g a) :=
(nfp_family_iterate_range_subset_of_range_subset hfg.le a).antisymm
(nfp_family_iterate_range_subset_of_range_subset hfg.ge a)

/-- The next common fixed point, at least `a`, for a family of normal functions. -/
def nfp_family (f : ι → ordinal → ordinal) (a) : ordinal :=
sup (nfp_family_iterate f a)

theorem nfp_family_eq_sup (f : ι → ordinal → ordinal) :
  nfp_family f = (λ a, sup (nfp_family_iterate f a)) :=
rfl

theorem iterate_le_nfp_family (f : ι → ordinal → ordinal) (a l) :
  nfp_family_iterate f a l ≤ nfp_family f a :=
le_sup _ _

theorem self_le_nfp_family (f : ι → ordinal → ordinal) (a) : a ≤ nfp_family f a :=
le_sup _ []

theorem lt_nfp_family {a b} : a < nfp_family f b ↔ ∃ l, a < nfp_family_iterate f b l :=
lt_sup

theorem nfp_family_le {a b} : nfp_family f a ≤ b ↔ ∀ l, nfp_family_iterate f a l ≤ b :=
sup_le

theorem nfp_family_empty [is_empty ι] (f : ι → ordinal → ordinal) : nfp_family f = id :=
funext (λ a, le_antisymm begin
  rw nfp_family_le,
  rintro (_ | i),
  { refl },
  { exact is_empty_elim i }
end (self_le_nfp_family f a))

theorem nfp_family_monotone (hf : ∀ i, monotone (f i)) : monotone (nfp_family f) :=
λ a b h, sup_le.2 $ λ l, (nfp_family_iterate_monotone hf l h).trans (le_sup _ l)

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

theorem nfp_family_le_of_range_subset {ι : Type u} {ι' : Type v} {f : ι → ordinal → ordinal}
  {g : ι' → ordinal → ordinal} (hfg : set.range f ⊆ set.range g) (a) :
  nfp_family.{u (max v w)} f a ≤ nfp_family.{v (max u w)} g a :=
sup_le_of_range_subset (nfp_family_iterate_range_subset_of_range_subset hfg a)

theorem nfp_family_eq_of_range_eq {ι : Type u} {ι' : Type v} {f : ι → ordinal → ordinal}
  {g : ι' → ordinal → ordinal} (hfg : set.range f = set.range g) :
  nfp_family.{u (max v w)} f = nfp_family.{v (max u w)} g :=
funext (λ a, sup_eq_of_range_eq (nfp_family_iterate_range_eq_of_range_eq hfg a))

theorem nfp_family_le_fp (H : ∀ i, is_normal (f i)) {a b} (ab : a ≤ b) (h : ∀ i, f i b ≤ b) :
  nfp_family f a ≤ b :=
sup_le.2 $ λ i, begin
  by_cases hι : is_empty ι,
  { rwa @nfp_family_iterate_empty ι hι },
  { haveI := not_is_empty_iff.1 hι,
    induction i with i l IH generalizing a, {exact ab},
    exact ((H i).strict_mono.monotone (IH ab)).trans (h i) }
end

theorem nfp_family_fp (H : ∀ i, is_normal (f i)) (i a) : f i (nfp_family f a) = nfp_family f a :=
begin
  unfold nfp_family,
  rw (H i).sup ⟨[]⟩,
  apply le_antisymm;
  refine ordinal.sup_le.2 (λ l, _),
  { exact le_sup _ (i :: l) },
  { exact ((H i).self_le _).trans (le_sup _ _) }
end

theorem apply_le_nfp_family [hι : nonempty ι] {f : ι → ordinal → ordinal} (H : ∀ i, is_normal (f i))
  {a b} : (∀ i, f i b ≤ nfp_family f a) ↔ b ≤ nfp_family f a :=
begin
  refine ⟨λ h, _, λ h i, _⟩,
  { unfreezingI { cases hι with i },
    exact ((H i).self_le b).trans (h i) },
  rw ←nfp_family_fp H i,
  exact (H i).strict_mono.monotone h
end

theorem nfp_family_eq_self {f : ι → ordinal → ordinal} {a} (h : ∀ i, f i a = a) :
  nfp_family f a = a :=
le_antisymm (sup_le.2 (λ l, (by rw nfp_family_iterate_fixed h))) (self_le_nfp_family f a)

/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
has an unbounded set of common fixed points. -/
theorem fp_family_unbounded (H : ∀ i, is_normal (f i)) :
  (⋂ i, function.fixed_points (f i)).unbounded (<) :=
λ a, ⟨_, λ s ⟨i, hi⟩, begin
  rw ←hi,
  exact nfp_family_fp H i a
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
 λ o l a, by rw [deriv_family_limit _ l, bsup_le]⟩

theorem deriv_family_fp (H : ∀ i, is_normal (f i)) (o : ordinal.{max u v}) (i) :
  f i (deriv_family f o) = deriv_family f o :=
begin
  refine limit_rec_on o _ (λ o IH, _) _,
  { rw [deriv_family_zero], exact nfp_family_fp H i 0 },
  { rw [deriv_family_succ], exact nfp_family_fp H i _ },
  { intros o l IH,
    rw [deriv_family_limit _ l,
      is_normal.bsup.{(max u v) u (max u v)} (H i) (λ a _, deriv_family f a) l.1],
    refine eq_of_forall_ge_iff (λ c, _),
    simp only [bsup_le, IH] {contextual:=tt} }
end

theorem le_iff_deriv_family (H : ∀ i, is_normal (f i)) {a} :
  (∀ i, f i a ≤ a) ↔ ∃ o, deriv_family f o = a :=
⟨λ ha, begin
  suffices : ∀ o (_ : a ≤ deriv_family f o), ∃ o, deriv_family f o = a,
  from this a ((deriv_family_is_normal _).self_le _),
  refine λ o, limit_rec_on o (λ h₁, ⟨0, le_antisymm _ h₁⟩) (λ o IH h₁, _) (λ o l IH h₁, _),
  { rw deriv_family_zero,
    exact nfp_family_le_fp H (ordinal.zero_le _) ha },
  { cases le_or_lt a (deriv_family f o), {exact IH h},
    refine ⟨succ o, le_antisymm _ h₁⟩,
    rw deriv_family_succ,
    exact nfp_family_le_fp H (succ_le.2 h) ha },
  { cases eq_or_lt_of_le h₁, {exact ⟨_, h.symm⟩},
    rw [deriv_family_limit _ l, ← not_le, bsup_le, not_ball] at h,
    exact let ⟨o', h, hl⟩ := h in IH o' h (le_of_not_le hl) }
end, λ ⟨o, e⟩ i, e ▸ le_of_eq (deriv_family_fp H _ i)⟩

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
    exact deriv_family_fp H a i },
  rw set.mem_Inter at ha,
  rwa ←fp_iff_deriv_family H
end

theorem deriv_family_le_of_range_subset {f : ι → ordinal → ordinal}
  {g : ι' → ordinal → ordinal.{max u v w}} (hf : ∀ i, monotone (f i))
  (hfg : set.range f ⊆ set.range g) (a) : deriv_family f a ≤ deriv_family.{w (max u v w)} g a :=
begin
  apply limit_rec_on a,
  { simp only [deriv_family_zero],
    exact nfp_family_le_of_range_subset.{u w v} hfg 0 },
  { simp only [deriv_family_succ],
    exact λ b H, (nfp_family_monotone hf (succ_le_succ.2 H)).trans
      (nfp_family_le_of_range_subset.{u w v} hfg _) },
  { intros b hb H,
    rw [deriv_family_limit f hb, deriv_family_limit.{w (max u v w)} g hb, bsup_le],
    exact λ c hc, (H c hc).trans (le_bsup _ c hc) }
end

theorem deriv_family_eq_of_range_eq {f : ι → ordinal → ordinal}
  {g : ι' → ordinal → ordinal.{max u v w}} (hfg : set.range f = set.range g) :
  deriv_family f = deriv_family.{w max u v w} g :=
funext (λ a, begin
  apply limit_rec_on a,
  { simp only [deriv_family_zero],
    rw nfp_family_eq_of_range_eq.{u w v} hfg,
    refl },
  { simp only [deriv_family_succ],
    intros b H,
    rw [H, nfp_family_eq_of_range_eq.{u w v} hfg],
    refl },
  { intros b hb H,
    rw [deriv_family_limit f hb, deriv_family_limit.{w (max u v w)} g hb],
    apply bsup_eq_of_brange_eq.{(max u v w) (max u v w) (max u v w)},
    congr,
    ext c hc,
    exact H c hc }
end)

-- another PR
theorem deriv_family_le_of_fp_subset {f : ι → ordinal → ordinal}
  {g : ι' → ordinal → ordinal} (hf : ∀ i, is_normal (f i)) (hg : ∀ i', is_normal (g i'))
  (H : ∀ o, (∀ i, f i o = o) → (∀ i', g i' o = o)) (a) :
  deriv_family.{w max u v w} g a ≤ deriv_family.{u max u v w} f a :=
begin
  rw [deriv_family_eq_enum_ord.{u max u v w} hf, deriv_family_eq_enum_ord hg],
  apply enum_ord_le_of_subset (fp_family_unbounded.{u max u v w} hf),
  intros a ha,
  rw set.mem_Inter at *,
  exact H a ha
end

-- another PR
theorem deriv_family_eq_of_fp_eq {f : ι → ordinal → ordinal}
  {g : ι' → ordinal → ordinal} (hf : ∀ i, is_normal (f i)) (hg : ∀ i', is_normal (g i'))
  (H : ∀ o, (∀ i, f i o = o) ↔ (∀ i', g i' o = o)) :
  deriv_family.{u max u v w} f = deriv_family.{w max u v w} g :=
funext (λ a, le_antisymm
  (deriv_family_le_of_fp_subset.{w v u} hg hf (λ o, (H o).2) a)
  (deriv_family_le_of_fp_subset.{u v w} hf hg (λ o, (H o).1) a))

end

/-! ### Fixed points of ordinal-indexed families of ordinals -/

section
variables {o : ordinal.{u}} {o' : ordinal.{w}} {f : Π b < o, ordinal.{max u v} → ordinal.{max u v}}

/-- The next common fixed point, at least `a`, for a family of normal functions indexed by ordinals.
-/
def nfp_bfamily (o : ordinal) (f : Π b < o, ordinal → ordinal) : ordinal → ordinal :=
nfp_family (family_of_bfamily o f)

theorem nfp_bfamily_eq_nfp_family (o : ordinal) (f : Π b < o, ordinal → ordinal) :
  nfp_bfamily o f = nfp_family (family_of_bfamily o f) :=
rfl

theorem nfp_family_eq_nfp_bfamily {ι : Type u} (f : ι → ordinal → ordinal) :
  nfp_family.{u v} f = nfp_bfamily _ (bfamily_of_family f) :=
nfp_family_eq_of_range_eq.{u u v} (by simp)

theorem iterate_le_nfp_bfamily {o : ordinal} (f : Π b < o, ordinal → ordinal) (a l) :
  nfp_family_iterate (family_of_bfamily o f) a l ≤ nfp_bfamily o f a :=
le_sup _ _

theorem self_le_nfp_bfamily {o : ordinal} (f : Π b < o, ordinal → ordinal) (a) :
  a ≤ nfp_bfamily o f a :=
le_sup _ []

theorem lt_nfp_bfamily {a b} :
  a < nfp_bfamily o f b ↔ ∃ l, a < nfp_family_iterate (family_of_bfamily o f) b l :=
lt_sup

theorem nfp_bfamily_le {o : ordinal} {f : Π b < o, ordinal → ordinal} {a b} :
  nfp_bfamily o f a ≤ b ↔ ∀ l, nfp_family_iterate (family_of_bfamily o f) a l ≤ b :=
sup_le

theorem nfp_bfamily_zero {o : ordinal} (ho : o = 0) (f : Π b < o, ordinal → ordinal) :
  nfp_bfamily o f = id :=
@nfp_family_empty _ (out_empty_iff_eq_zero.2 ho) _

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

theorem nfp_bfamily_le_fp (H : ∀ i hi, is_normal (f i hi)) {a b} (ab : a ≤ b)
  (h : ∀ i hi, f i hi b ≤ b) : nfp_bfamily o f a ≤ b :=
nfp_family_le_fp (λ _, H _ _) ab (λ i, h _ _)

theorem nfp_bfamily_fp (H : ∀ i hi, is_normal (f i hi)) (i hi a) :
  f i hi (nfp_bfamily o f a) = nfp_bfamily o f a :=
by { rw ←family_of_bfamily_enum o f, exact nfp_family_fp (λ i, H _ _) _ _ }

theorem le_nfp_bfamily (ho : o ≠ 0) (H : ∀ i hi, is_normal (f i hi)) {a b} :
  (∀ i hi, f i hi b ≤ nfp_bfamily o f a) ↔ b ≤ nfp_bfamily o f a :=
begin
  refine ⟨λ h, _, λ h i hi, _⟩,
  { have ho' : 0 < o := ordinal.pos_iff_ne_zero.2 ho,
    exact ((H 0 ho').self_le b).trans (h 0 ho') },
  rw ←nfp_bfamily_fp H i,
  exact (H i hi).strict_mono.monotone h
end

theorem nfp_bfamily_eq_self {a} (h : ∀ i hi, f i hi a = a) : nfp_bfamily o f a = a :=
nfp_family_eq_self (λ _, h _ _)

/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
has an unbounded set of common fixed points. -/
theorem fp_bfamily_unbounded (H : ∀ i hi, is_normal (f i hi)) :
  (⋂ i hi, function.fixed_points (f i hi)).unbounded (<) :=
λ a, ⟨_, by { rw set.mem_Inter₂, exact λ _ _, nfp_bfamily_fp H _ _ _ },
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

theorem deriv_bfamily_fp (H : ∀ i hi, is_normal (f i hi)) (a : ordinal) (i hi) :
  f i hi (deriv_bfamily o f a) = deriv_bfamily o f a :=
by { rw ←family_of_bfamily_enum o f, exact deriv_family_fp (λ _, H _ _) _ _ }

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
  refine ⟨λ a, set.mem_Inter₂.2 (deriv_bfamily_fp H a), λ a ha, _⟩,
  rw set.mem_Inter₂ at ha,
  rwa ←fp_iff_deriv_bfamily H
end

theorem deriv_bfamily_le_of_range_subset {f : Π b < o, ordinal → ordinal}
  {g : Π b < o', ordinal → ordinal.{max u v w}} (hf : ∀ i hi, monotone (f i hi))
  (hfg : brange o f ⊆ brange o' g) (a) :
  deriv_bfamily o f a ≤ deriv_bfamily.{w (max u v w)} o' g a :=
begin
  apply deriv_family_le_of_range_subset,
  { exact (λ i, hf _ _) },
  { simpa [range_family_of_bfamily] using hfg }
end

theorem deriv_bfamily_eq_of_range_eq {f : Π b < o, ordinal → ordinal}
  {g : Π b < o', ordinal → ordinal.{max u v w}} (hf : ∀ i hi, monotone (f i hi))
  (hfg : brange o f = brange o' g) : deriv_bfamily o f = deriv_bfamily.{w (max u v w)} o' g :=
funext (λ a, begin
  unfold deriv_bfamily,
  rw deriv_family_eq_of_range_eq,
  simpa [range_family_of_bfamily] using hfg
end)

-- another PR
theorem deriv_bfamily_le_of_fp_subset {f : Π a < o, ordinal → ordinal}
  {g : Π a < o', ordinal → ordinal} (hf : ∀ i hi, is_normal (f i hi))
  (hg : ∀ i' hi', is_normal (g i' hi'))
  (H : ∀ o, (∀ i hi, f i hi o = o) → (∀ i' hi', g i' hi' o = o)) (a) :
  deriv_bfamily.{w max u v w} o' g a ≤ deriv_bfamily.{u max u v w} o f a :=
begin
  refine deriv_family_le_of_fp_subset (λ i, hf _ _) (λ i, hg _ _) (λ a h i', H _ (λ i hi, _) _ _) a,
  rw ←type_out o at hi,
  have := h (enum o.out.r i hi),
  rwa family_of_bfamily_enum at this
end

-- another PR
theorem deriv_bfamily_eq_of_fp_eq {f : Π a < o, ordinal → ordinal}
  {g : Π a < o', ordinal → ordinal} (hf : ∀ i hi, is_normal (f i hi))
  (hg : ∀ i' hi', is_normal (g i' hi'))
  (H : ∀ o, (∀ i hi, f i hi o = o) ↔ (∀ i' hi', g i' hi' o = o)) :
  deriv_bfamily.{u max u v w} o f = deriv_bfamily.{w max u v w} o' g :=
funext (λ a, le_antisymm
  (deriv_bfamily_le_of_fp_subset.{w v u} hg hf (λ o, (H o).2) a)
  (deriv_bfamily_le_of_fp_subset.{u v w} hf hg (λ o, (H o).1) a))

end

/-! ### Fixed points of a single function -/

section
variable {f : ordinal.{u} → ordinal.{u}}

/-- The next fixed point function, the least fixed point of the normal function `f`, at least `a`.
-/
def nfp (f : ordinal → ordinal) : ordinal → ordinal :=
nfp_family (λ _ : unit, f)

theorem nfp_eq_nfp_family (f : ordinal → ordinal) : nfp f = nfp_family (λ _ : unit, f) :=
rfl

theorem nfp_eq_nfp_family' (ι) [nonempty ι] (f : ordinal → ordinal) :
  nfp f = nfp_family (λ _ : ι, f) :=
nfp_family_eq_of_range_eq (by simp only [set.range_const])

@[simp] theorem sup_iterate_eq_nfp (f : ordinal.{u} → ordinal.{u}) :
  (λ a, sup (λ n : ℕ, f^[n] a)) = nfp f :=
begin
  refine funext (λ a, le_antisymm _ (sup_le.2 (λ l, _))),
  { rw sup_le,
    intro n,
    rw [←list.length_repeat unit.star n, ←nfp_family_iterate_eq_iterate.{0 u} f a],
    exact le_sup _ _ },
  { rw nfp_family_iterate_eq_iterate.{0 u} f a l,
    exact le_sup _ _ },
end

theorem iterate_le_nfp (f a n) : f^[n] a ≤ nfp f a :=
by { rw ←sup_iterate_eq_nfp, exact le_sup _ n }

theorem self_le_nfp (f a) : a ≤ nfp f a :=
iterate_le_nfp f a 0

theorem lt_nfp {a b} : a < nfp f b ↔ ∃ n, a < (f^[n]) b :=
by { rw ←sup_iterate_eq_nfp, exact lt_sup }

theorem nfp_le {a b} : nfp f a ≤ b ↔ ∀ n, (f^[n]) a ≤ b :=
by { rw ←sup_iterate_eq_nfp, exact sup_le }

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

theorem is_normal.nfp_le_fp {f} (H : is_normal f) {a b} (ab : a ≤ b) (h : f b ≤ b) : nfp f a ≤ b :=
nfp_family_le_fp (λ _, H) ab (λ _, h)

theorem is_normal.nfp_fp {f} (H : is_normal f) : ∀ a, f (nfp f a) = nfp f a :=
nfp_family_fp (λ _, H) unit.star

theorem is_normal.le_nfp {f} (H : is_normal f) {a b} :
  f b ≤ nfp f a ↔ b ≤ nfp f a :=
⟨le_trans (H.self_le _), λ h, by simpa only [H.nfp_fp] using H.le_iff.2 h⟩

theorem nfp_eq_self {f : ordinal → ordinal} {a} (h : f a = a) : nfp f a = a :=
nfp_family_eq_self (λ _, h)

/-- The fixed point lemma for normal functions: any normal function has an unbounded set of
fixed points. -/
theorem fp_unbounded (H : is_normal f) : (function.fixed_points f).unbounded (<) :=
by { convert fp_family_unbounded (λ _ : unit, H), exact (set.Inter_const _).symm }

/-- The derivative of a normal function `f` is the sequence of fixed points of `f`. -/
def deriv (f : ordinal → ordinal) : ordinal → ordinal :=
deriv_family (λ _ : unit, f)

theorem deriv_eq_deriv_family (f : ordinal → ordinal) : deriv f = deriv_family (λ _ : unit, f) :=
rfl

theorem deriv_eq_deriv_family' (ι : Type u) [nonempty ι] (f : ordinal → ordinal) :
  deriv f = deriv_family.{u (max u v)} (λ _ : ι, f) :=
deriv_family_eq_of_range_eq.{0 v u} (by simp)

theorem deriv_eq_deriv_bfamily (f : ordinal → ordinal) : deriv f = deriv_bfamily 1 (λ a _, f) :=
@deriv_eq_deriv_family' _ (out_nonempty_iff_ne_zero.2 ordinal.one_ne_zero) f

theorem deriv_eq_deriv_bfamily' {o : ordinal} (ho : o ≠ 0) (f : ordinal → ordinal) :
  deriv f = deriv_bfamily.{u (max u v)} o (λ a _, f) :=
deriv_family_eq_of_range_eq.{0 v} $ by rwa [set.range_const, range_family_of_bfamily, brange_const]

@[simp] theorem deriv_zero (f) : deriv f 0 = nfp f 0 :=
deriv_family_zero _

@[simp] theorem deriv_succ (f o) : deriv f (succ o) = nfp f (succ (deriv f o)) :=
deriv_family_succ _ _

theorem deriv_limit (f) {o} : is_limit o → deriv f o = bsup.{u 0} o (λ a _, deriv f a) :=
deriv_family_limit _

theorem deriv_is_normal (f) : is_normal (deriv f) :=
deriv_family_is_normal _

theorem is_normal.deriv_fp {f} (H : is_normal f) (o) : f (deriv f o) = deriv f o :=
deriv_family_fp (λ _, H) _ unit.star

theorem is_normal.le_iff_deriv {f} (H : is_normal f) {a} : f a ≤ a ↔ ∃ o, deriv f o = a :=
begin
  unfold deriv,
  rw ←le_iff_deriv_family (λ _ : unit, H),
  exact ⟨λ h _, h, λ h, h unit.star⟩
end

theorem is_normal.fp_iff_deriv {f} (H : is_normal f) {a} : f a = a ↔ ∃ o, deriv f o = a :=
by rw [←H.le_iff_eq, H.le_iff_deriv]

theorem deriv_eq_enum_ord (H : is_normal f) : deriv f = enum_ord (function.fixed_points f) :=
by { convert deriv_family_eq_enum_ord (λ _ : unit, H), exact (set.Inter_const _).symm }

@[simp] theorem deriv_id : deriv id = id :=
begin
  rw [deriv_eq_enum_ord is_normal.refl, fixed_points_id],
  exact enum_ord_univ
end

theorem self_le_deriv {f : ordinal → ordinal} (hf : is_normal f) (o) : f o ≤ deriv f o :=
begin
  rw deriv_eq_enum_ord hf,
  nth_rewrite 0 ←enum_ord_range hf.strict_mono,
  exact enum_ord_le_of_subset (fp_unbounded hf) fixed_points_subset_range _
end

-- another PR
theorem deriv_le_of_fp_subset {f g : ordinal → ordinal} (hf : is_normal f) (hg : is_normal g)
  (H : ∀ o, f o = o → g o = o) (a) : deriv g a ≤ deriv f a :=
deriv_family_le_of_fp_subset (λ _, hf) (λ _, hg) (λ o hf' _, H o (hf' unit.star)) a

-- another PR
theorem deriv_eq_of_fp_eq {f g : ordinal → ordinal} (hf : is_normal f) (hg : is_normal g)
  (H : ∀ o, f o = o ↔ g o = o) : deriv f = deriv g :=
funext (λ a, le_antisymm
  (deriv_le_of_fp_subset hg hf (λ o, (H o).2) a)
  (deriv_le_of_fp_subset hf hg (λ o, (H o).1) a))

/-! ### Fixed points of addition -/

@[simp] theorem nfp_add_zero (a) : nfp ((+) a) 0 = a * omega :=
begin
  rw [←sup_iterate_eq_nfp, ←sup_mul_nat],
  dsimp, congr, funext,
  induction n with n hn,
  { rw [nat.cast_zero, mul_zero, iterate_zero_apply] },
  { nth_rewrite 1 nat.succ_eq_one_add,
    rw [nat.cast_add, nat.cast_one, mul_one_add, iterate_succ_apply', hn] }
end

theorem nfp_add_eq_mul_omega {a b} (hba : b ≤ a * omega) :
  nfp ((+) a) b = a * omega :=
begin
  apply le_antisymm ((add_is_normal a).nfp_le_fp hba _),
  { rw ←nfp_add_zero,
    exact nfp_monotone (add_is_normal a).strict_mono.monotone (ordinal.zero_le b) },
  { rw [←mul_one_add, one_add_omega] }
end

theorem add_eq_right_iff_mul_omega_le {a b : ordinal} : a + b = b ↔ a * omega ≤ b :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw [←nfp_add_zero a, ←deriv_zero],
    cases (add_is_normal a).fp_iff_deriv.1 h with c hc,
    rw ←hc,
    exact (deriv_is_normal _).strict_mono.monotone (ordinal.zero_le _) },
  { have := ordinal.add_sub_cancel_of_le h,
    nth_rewrite 0 ←this,
    rwa [←add_assoc, ←mul_one_add, one_add_omega] }
end

theorem add_le_right_iff_mul_omega_le {a b : ordinal} : a + b ≤ b ↔ a * omega ≤ b :=
by { rw ←add_eq_right_iff_mul_omega_le, exact (add_is_normal a).le_iff_eq }

theorem deriv_add_eq_mul_omega_add (a b : ordinal.{u}) : deriv ((+) a) b = a * omega + b :=
begin
  refine b.limit_rec_on _ (λ o h, _) (λ o ho h, _),
  { rw [deriv_zero, add_zero],
    exact nfp_add_zero a },
  { rw [deriv_succ, h, add_succ],
    exact nfp_eq_self (add_eq_right_iff_mul_omega_le.2 ((le_add_right _ _).trans
      (lt_succ_self _).le)) },
  { rw [←is_normal.bsup_eq.{u u} (add_is_normal _) ho,
      ←is_normal.bsup_eq.{u u} (deriv_is_normal _) ho],
    congr,
    ext a hao,
    exact h a hao }
end

end
end ordinal
