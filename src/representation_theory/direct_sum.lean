/-
Copyright (c) 2021 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import representation_theory.repre_hom_basic
import algebra.direct_sum
import linear_algebra.direct_sum_module

open_locale direct_sum

namespace direct_sum_repre

/- Need to specify k because Lean cannot otherwise infer it. -/
def smul
  {ι : Type*} (k : Type*) {G : Type*} {M : ι → Type*}
  [semiring k] [monoid G]
  [Π i : ι, add_comm_monoid (M i)] [Π i : ι, module k (M i)]
  [Π i : ι, repre k G (M i)] : G → (⨁ i : ι, M i) →ₗ[k] ⨁ i : ι, M i :=
λ g, dfinsupp.map_range.linear_map (λ i : ι, (linear_map_of_smul k G (M i) g : M i →ₗ[k] M i))

instance has_scalar
  {ι : Type*} (k : Type*) {G : Type*} {M : ι → Type*}
  [semiring k] [monoid G]
  [Π i : ι, add_comm_monoid (M i)] [Π i : ι, module k (M i)]
  [Π i : ι, repre k G (M i)] : has_scalar G (Π₀ i : ι, M i) := ⟨λ g x, smul k g x⟩

lemma smul_apply
  {ι : Type*} {k : Type*} {G : Type*} {M : ι → Type*}
  [semiring k] [monoid G]
  [Π i : ι, add_comm_monoid (M i)] [Π i : ι, module k (M i)]
  [Π i : ι, repre k G (M i)] (i : ι) :
  ∀ (g : G) (x : Π₀ i : ι, M i), (g • x) i = g • (x i) := by {intros, simp}

end direct_sum_repre

/--
A collection of representations has a natural representation structure from the G-action on individual `module k (M i)`.
-/
instance direct_sum_repre
  {ι : Type*} {k : Type*} {G : Type*} {M : ι → Type*}
  [semiring k] [monoid G]
  [Π i : ι, add_comm_monoid (M i)] [Π i : ι, module k (M i)]
  [Π i : ι, repre k G (M i)] : repre k G (Π₀ i : ι, M i) :=
{ to_distrib_mul_action :=
  { to_mul_action :=
    { to_has_scalar := direct_sum_repre.has_scalar k,
      one_smul := by {intro, ext, simp},
      mul_smul := by {intros, ext, simp} },
    smul_add := by {intros, ext, simp},
    smul_zero := by {intros, ext, simp} },
  smul_smul := by {intros, ext, simp} }

/-
Copy from dfinsupp, linear_algebra.dfinsupp, and/or linear_algebra.direct_sum_module
-/

namespace direct_sum_repre

/--
Inclusion map of the i-th component of a direct_sum as a repre_hom.
-/
def lof
  {ι : Type*} (k : Type*) {G : Type*} (M : ι → Type*)
  [decidable_eq ι] [semiring k] [monoid G]
  [Π i : ι, add_comm_monoid (M i)] [Π i : ι, module k (M i)]
  [Π i : ι, repre k G (M i)] (i : ι) : M i →ᵣ[k;G] Π₀ i : ι, M i :=
repre_hom.of_linear_map (direct_sum.lof k ι M i)
begin
  intros,
  ext j,
  unfold direct_sum.lof,
  simp,
  by_cases i = j,
  { rw ←h,
    simp },
  { simp [h] }
end

lemma smul_single
  {ι : Type*} {k : Type*} {G : Type*} {M : ι → Type*}
  [decidable_eq ι] [semiring k] [monoid G]
  [Π i : ι, add_comm_monoid (M i)] [Π i : ι, module k (M i)]
  [Π i : ι, repre k G (M i)]
  (g : G) (i : ι) (x : M i) : g • dfinsupp.single i x = dfinsupp.single i (g • x) :=
begin
  ext j,
  simp,
  by_cases i = j,
  { rw ←h,
    rw dif_pos rfl,
    rw dif_pos rfl },
  { rw dif_neg h,
    rw dif_neg h,
    simp }
end

/-- Given a collection of repre_hom from individual factors, construct a repre_hom from the direct sum representation. -/
def to_repre
  (k : Type*) (G : Type*) (ι : Type*) {M : ι → Type*} (N : Type*)
  [decidable_eq ι] [semiring k] [monoid G]
  [Π i : ι, add_comm_monoid (M i)] [Π i : ι, module k (M i)]
  [Π i : ι, repre k G (M i)]
  [add_comm_monoid N] [module k N] [repre k G N]
  (φ : Π i, M i →ᵣ[k;G] N) : (Π₀ i, M i) →ᵣ[k;G] N :=
begin
  apply repre_hom.of_linear_map,
  show (⨁ (i : ι), M i) →ₗ[k] N,
  { apply direct_sum.to_module,
    intro i,
    exact φ i },
  { intros,
    simp,
    apply dfinsupp.induction x,
    { simp },
    { intros i xi y h1 h2 h3,
      simp,
      rw h3,
      congr,
      rw smul_single,
      rw direct_sum.single_eq_lof k,
      rw direct_sum.single_eq_lof k,
      rw direct_sum.to_module_lof,
      rw direct_sum.to_module_lof,
      apply (φ i).map_smul2 } }
end

/-- The `direct_sum_repre` formed by a collection of `subrepre`s of `M` is said to be internal if the canonical map `(⨁ i, A i) →ᵣ[k;G] M` is bijective. -/
def subrepre_is_internal
  {ι : Type*} {k : Type*} {G : Type*} {M : Type*}
  [decidable_eq ι] [semiring k] [monoid G]
  [add_comm_monoid M] [module k M] [repre k G M]
  (p : ι → subrepre k G M) : Prop :=
function.bijective (to_repre k G ι M (λ i, (p i).subtype))

structure decomposition
  (k : Type*) (G : Type*) (M : Type*)
  [semiring k] [monoid G] [nontrivial M]
  [add_comm_monoid M] [module k M] [repre k G M] :=
(ι : Type*)
[dec_ι : decidable_eq ι]
[nontriv_ι : nontrivial ι]
(subrepre : ι → subrepre k G M)
[nontriv : Π i : ι, nontrivial (subrepre i)]
(internal : subrepre_is_internal subrepre)

attribute [instance] decomposition.dec_ι
attribute [instance] decomposition.nontriv_ι
attribute [instance] decomposition.nontriv

/-- A nontrivial representation is decomposable if it is the internal direct sum of more than 1 nontrivial subrepresentations. (Is this def actually correct?) -/
def is_decomposable
  (k : Type*) (G : Type*) (M : Type*)
  [semiring k] [monoid G] [nontrivial M]
  [add_comm_monoid M] [module k M] [repre k G M] :=
nonempty (decomposition k G M)

/- TODO: simplify the following proof -/

/-- The existence of a (nontrivial) decomposition implies that the representation is reducible. -/
theorem is_internal_not_irreducible
  {k : Type*} [semiring k]
  {G : Type*} [monoid G]
  {M : Type*} [nontrivial M]
  [add_comm_monoid M] [module k M] [repre k G M] :
  is_decomposable k G M → ¬is_irreducible k G M :=
begin
  intros h irr,
  cases h with decomp h,
  have htop : ∀ i : decomp.ι, decomp.subrepre i = ⊤,
  { intro,
    unfold is_irreducible at irr,
    have := irr (decomp.subrepre i),
    cases this,
    rw this,
    { have : nontrivial (⊥ : subrepre k G M),
      { split,
        cases exists_ne (0 : decomp.subrepre i) with x hx,
        rw ←this,
        existsi x,
        existsi (0 : decomp.subrepre i),
        exact hx },
      cases @exists_ne _ this (0 : (⊥ : subrepre k G M)) with x hx,
      have : x = (0 : (⊥ : subrepre k G M)),
      { simp },
      exact absurd this hx },
    exact this },
  cases exists_pair_ne decomp.ι with i hi,
  cases hi with j hij,
  have : nontrivial (⊤ : subrepre k G M),
  { split,
    rw ←htop i,
    exact exists_pair_ne (decomp.subrepre i) },
  cases @exists_ne _ this (0 : (⊤ : subrepre k G M)) with a ha,
  let x := dfinsupp.single i a,
  let y := dfinsupp.single j a,

  have hneq : x ≠ y,
  { apply mt (dfinsupp.single_eq_single_iff i j a a).mp,
    push_neg,
    split,
    { intro h,
      exact absurd h hij },
    { intro h,
      exact absurd h ha } },

  have h_eq : to_repre k G decomp.ι M (λ i, (⊤ : subrepre k G M).subtype) x = to_repre k G decomp.ι M (λ i, (⊤ : subrepre k G M).subtype) y,
  { unfold to_repre repre_hom.of_linear_map direct_sum.to_module,
    simp },
  have hinj := decomp.internal.injective,
  have hinjtop : function.injective ⇑(to_repre k G decomp.ι M (λ (i : decomp.ι), (⊤ : subrepre k G M).subtype)),
  { convert hinj,
    any_goals { ext ii, congr, exact (htop ii).symm },
    any_goals { ext ii, refl, simp, intro ii, rw htop ii } },
  unfold function.injective at hinjtop,
  have := hinjtop h_eq,
  exact absurd this hneq
end

end direct_sum_repre