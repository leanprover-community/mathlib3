/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
import data.finsupp.to_dfinsupp
import linear_algebra.basis

/-!
# Properties of the module `Π₀ i, M i`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given an indexed collection of `R`-modules `M i`, the `R`-module structure on `Π₀ i, M i`
is defined in `data.dfinsupp`.

In this file we define `linear_map` versions of various maps:

* `dfinsupp.lsingle a : M →ₗ[R] Π₀ i, M i`: `dfinsupp.single a` as a linear map;

* `dfinsupp.lmk s : (Π i : (↑s : set ι), M i) →ₗ[R] Π₀ i, M i`: `dfinsupp.single a` as a linear map;

* `dfinsupp.lapply i : (Π₀ i, M i) →ₗ[R] M`: the map `λ f, f i` as a linear map;

* `dfinsupp.lsum`: `dfinsupp.sum` or `dfinsupp.lift_add_hom` as a `linear_map`;

## Implementation notes

This file should try to mirror `linear_algebra.finsupp` where possible. The API of `finsupp` is
much more developed, but many lemmas in that file should be eligible to copy over.

## Tags

function with finite support, module, linear algebra
-/

variables {ι : Type*} {R : Type*} {S : Type*} {M : ι → Type*} {N : Type*}

variables [dec_ι : decidable_eq ι]

namespace dfinsupp
variables [semiring R] [Π i, add_comm_monoid (M i)] [Π i, module R (M i)]
variables [add_comm_monoid N] [module R N]

include dec_ι

/-- `dfinsupp.mk` as a `linear_map`. -/
def lmk (s : finset ι) : (Π i : (↑s : set ι), M i) →ₗ[R] Π₀ i, M i :=
{ to_fun := mk s, map_add' := λ _ _, mk_add, map_smul' := λ c x, mk_smul c x}

/-- `dfinsupp.single` as a `linear_map` -/
def lsingle (i) : M i →ₗ[R] Π₀ i, M i :=
{ to_fun := single i, map_smul' := single_smul, .. dfinsupp.single_add_hom _ _ }

/-- Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree everywhere. -/
lemma lhom_ext ⦃φ ψ : (Π₀ i, M i) →ₗ[R] N⦄
  (h : ∀ i x, φ (single i x) = ψ (single i x)) :
  φ = ψ :=
linear_map.to_add_monoid_hom_injective $ add_hom_ext h

/-- Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree everywhere.

See note [partially-applied ext lemmas].
After apply this lemma, if `M = R` then it suffices to verify `φ (single a 1) = ψ (single a 1)`. -/
@[ext] lemma lhom_ext' ⦃φ ψ : (Π₀ i, M i) →ₗ[R] N⦄
  (h : ∀ i, φ.comp (lsingle i) = ψ.comp (lsingle i)) :
  φ = ψ :=
lhom_ext $ λ i, linear_map.congr_fun (h i)

omit dec_ι

/-- Interpret `λ (f : Π₀ i, M i), f i` as a linear map. -/
def lapply (i : ι) : (Π₀ i, M i) →ₗ[R] M i :=
{ to_fun := λ f, f i,
  map_add' := λ f g, add_apply f g i,
  map_smul' := λ c f, smul_apply c f i}

include dec_ι

@[simp] lemma lmk_apply (s : finset ι) (x) : (lmk s : _ →ₗ[R] Π₀ i, M i) x = mk s x := rfl

@[simp] lemma lsingle_apply (i : ι) (x : M i) : (lsingle i : _ →ₗ[R] _) x = single i x := rfl

omit dec_ι

@[simp] lemma lapply_apply (i : ι) (f : Π₀ i, M i) : (lapply i : _ →ₗ[R] _) f = f i := rfl

section lsum

/-- Typeclass inference can't find `dfinsupp.add_comm_monoid` without help for this case.
This instance allows it to be found where it is needed on the LHS of the colon in
`dfinsupp.module_of_linear_map`. -/
instance add_comm_monoid_of_linear_map : add_comm_monoid (Π₀ (i : ι), M i →ₗ[R] N) :=
@dfinsupp.add_comm_monoid _ (λ i, M i →ₗ[R] N) _

/-- Typeclass inference can't find `dfinsupp.module` without help for this case.
This is needed to define `dfinsupp.lsum` below.

The cause seems to be an inability to unify the `Π i, add_comm_monoid (M i →ₗ[R] N)` instance that
we have with the `Π i, has_zero (M i →ₗ[R] N)` instance which appears as a parameter to the
`dfinsupp` type. -/
instance module_of_linear_map [semiring S] [module S N] [smul_comm_class R S N] :
  module S (Π₀ (i : ι), M i →ₗ[R] N) :=
@dfinsupp.module _ _ (λ i, M i →ₗ[R] N) _ _ _

variables (S)

include dec_ι

/-- The `dfinsupp` version of `finsupp.lsum`.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used. -/
@[simps]
def lsum [semiring S] [module S N] [smul_comm_class R S N] :
  (Π i, M i →ₗ[R] N) ≃ₗ[S] ((Π₀ i, M i) →ₗ[R] N) :=
{ to_fun := λ F,
  { to_fun := sum_add_hom (λ i, (F i).to_add_monoid_hom),
    map_add' := (lift_add_hom (λ i, (F i).to_add_monoid_hom)).map_add,
    map_smul' := λ c f, by
    { dsimp,
      apply dfinsupp.induction f,
      { rw [smul_zero, add_monoid_hom.map_zero, smul_zero] },
      { intros a b f ha hb hf,
        rw [smul_add, add_monoid_hom.map_add, add_monoid_hom.map_add, smul_add, hf, ←single_smul,
          sum_add_hom_single, sum_add_hom_single, linear_map.to_add_monoid_hom_coe,
          linear_map.map_smul], } } },
  inv_fun := λ F i, F.comp (lsingle i),
  left_inv := λ F, by { ext x y, simp },
  right_inv := λ F, by { ext x y, simp },
  map_add' := λ F G, by { ext x y, simp },
  map_smul' := λ c F, by { ext, simp } }

/-- While `simp` can prove this, it is often convenient to avoid unfolding `lsum` into `sum_add_hom`
with `dfinsupp.lsum_apply_apply`. -/
lemma lsum_single [semiring S] [module S N] [smul_comm_class R S N]
  (F : Π i, M i →ₗ[R] N) (i) (x : M i) :
  lsum S F (single i x) = F i x :=
sum_add_hom_single _ _ _

end lsum

/-! ### Bundled versions of `dfinsupp.map_range`

The names should match the equivalent bundled `finsupp.map_range` definitions.
-/

section map_range

variables {β β₁ β₂: ι → Type*}
variables [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (β₁ i)] [Π i, add_comm_monoid (β₂ i)]
variables [Π i, module R (β i)] [Π i, module R (β₁ i)] [Π i, module R (β₂ i)]

lemma map_range_smul (f : Π i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0)
  (r : R) (hf' : ∀ i x, f i (r • x) = r • f i x) (g : Π₀ i, β₁ i):
  map_range f hf (r • g) = r • map_range f hf g :=
begin
  ext,
  simp only [map_range_apply f, coe_smul, pi.smul_apply, hf']
end

/-- `dfinsupp.map_range` as an `linear_map`. -/
@[simps apply]
def map_range.linear_map (f : Π i, β₁ i →ₗ[R] β₂ i) : (Π₀ i, β₁ i) →ₗ[R] (Π₀ i, β₂ i) :=
{ to_fun := map_range (λ i x, f i x) (λ i, (f i).map_zero),
  map_smul' := λ r, map_range_smul _ _ _ (λ i, (f i).map_smul r),
  .. map_range.add_monoid_hom (λ i, (f i).to_add_monoid_hom) }

@[simp]
lemma map_range.linear_map_id :
  map_range.linear_map (λ i, (linear_map.id : (β₂ i) →ₗ[R] _)) = linear_map.id :=
linear_map.ext map_range_id

lemma map_range.linear_map_comp (f : Π i, β₁ i →ₗ[R] β₂ i) (f₂ : Π i, β i →ₗ[R] β₁ i):
  map_range.linear_map (λ i, (f i).comp (f₂ i)) =
    (map_range.linear_map f).comp (map_range.linear_map f₂) :=
linear_map.ext $ map_range_comp (λ i x, f i x) (λ i x, f₂ i x) _ _ _

include dec_ι
lemma sum_map_range_index.linear_map
  [Π (i : ι) (x : β₁ i), decidable (x ≠ 0)] [Π (i : ι) (x : β₂ i), decidable (x ≠ 0)]
  {f : Π i, β₁ i →ₗ[R] β₂ i} {h : Π i, β₂ i →ₗ[R] N} {l : Π₀ i, β₁ i} :
  dfinsupp.lsum ℕ h (map_range.linear_map f l) = dfinsupp.lsum ℕ (λ i, (h i).comp (f i)) l :=
by simpa [dfinsupp.sum_add_hom_apply] using
  @sum_map_range_index ι N _ _ _ _ _ _ _ _ (λ i, f i) (λ i, by simp) l (λ i, h i) (λ i, by simp)
omit dec_ι

/-- `dfinsupp.map_range.linear_map` as an `linear_equiv`. -/
@[simps apply]
def map_range.linear_equiv (e : Π i, β₁ i ≃ₗ[R] β₂ i) : (Π₀ i, β₁ i) ≃ₗ[R] (Π₀ i, β₂ i) :=
{ to_fun := map_range (λ i x, e i x) (λ i, (e i).map_zero),
  inv_fun := map_range (λ i x, (e i).symm x) (λ i, (e i).symm.map_zero),
  .. map_range.add_equiv (λ i, (e i).to_add_equiv),
  .. map_range.linear_map (λ i, (e i).to_linear_map) }

@[simp]
lemma map_range.linear_equiv_refl :
  (map_range.linear_equiv $ λ i, linear_equiv.refl R (β₁ i)) = linear_equiv.refl _ _ :=
linear_equiv.ext map_range_id

lemma map_range.linear_equiv_trans (f : Π i, β i ≃ₗ[R] β₁ i) (f₂ : Π i, β₁ i ≃ₗ[R] β₂ i):
  map_range.linear_equiv (λ i, (f i).trans (f₂ i)) =
    (map_range.linear_equiv f).trans (map_range.linear_equiv f₂) :=
linear_equiv.ext $ map_range_comp (λ i x, f₂ i x) (λ i x, f i x) _ _ _

@[simp]
lemma map_range.linear_equiv_symm (e : Π i, β₁ i ≃ₗ[R] β₂ i) :
  (map_range.linear_equiv e).symm = map_range.linear_equiv (λ i, (e i).symm) := rfl

end map_range

section coprod_map

variables [decidable_eq ι] [Π (x : N), decidable (x ≠ 0)]

/-- Given a family of linear maps `f i : M i  →ₗ[R] N`, we can form a linear map
`(Π₀ i, M i) →ₗ[R] N` which sends `x : Π₀ i, M i` to the sum over `i` of `f i` applied to `x i`.
This is the map coming from the universal property of `Π₀ i, M i` as the coproduct of the `M i`.
See also `linear_map.coprod` for the binary product version. -/
noncomputable def coprod_map (f : Π (i : ι), M i  →ₗ[R] N) : (Π₀ i, M i) →ₗ[R] N :=
finsupp.lsum ℕ (λ i : ι, linear_map.id) ∘ₗ
(@finsupp_lequiv_dfinsupp ι R N _ _ _ _ _).symm.to_linear_map ∘ₗ
(dfinsupp.map_range.linear_map f)

lemma coprod_map_apply (f : Π (i : ι), M i  →ₗ[R] N) (x : Π₀ i, M i) :
  coprod_map f x =
  finsupp.sum (map_range (λ i, f i) (λ i, linear_map.map_zero _) x).to_finsupp (λ i, id) := rfl

end coprod_map

section basis

/-- The direct sum of free modules is free.

Note that while this is stated for `dfinsupp` not `direct_sum`, the types are defeq. -/
noncomputable def basis {η : ι → Type*} (b : Π i, basis (η i) R (M i)) :
  basis (Σ i, η i) R (Π₀ i, M i) :=
basis.of_repr ((map_range.linear_equiv (λ i, (b i).repr)).trans
  (sigma_finsupp_lequiv_dfinsupp R).symm)

end basis

end dfinsupp

include dec_ι

namespace submodule
variables [semiring R] [add_comm_monoid N] [module R N]
open dfinsupp

lemma dfinsupp_sum_mem {β : ι → Type*} [Π i, has_zero (β i)]
  [Π i (x : β i), decidable (x ≠ 0)] (S : submodule R N)
  (f : Π₀ i, β i) (g : Π i, β i → N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) : f.sum g ∈ S :=
dfinsupp_sum_mem S f g h

lemma dfinsupp_sum_add_hom_mem {β : ι → Type*} [Π i, add_zero_class (β i)]
  (S : submodule R N) (f : Π₀ i, β i) (g : Π i, β i →+ N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) :
  dfinsupp.sum_add_hom g f ∈ S :=
dfinsupp_sum_add_hom_mem S f g h

/-- The supremum of a family of submodules is equal to the range of `dfinsupp.lsum`; that is
every element in the `supr` can be produced from taking a finite number of non-zero elements
of `p i`, coercing them to `N`, and summing them. -/
lemma supr_eq_range_dfinsupp_lsum (p : ι → submodule R N) :
  supr p = (dfinsupp.lsum ℕ (λ i, (p i).subtype)).range :=
begin
  apply le_antisymm,
  { apply supr_le _,
    intros i y hy,
    exact ⟨dfinsupp.single i ⟨y, hy⟩, dfinsupp.sum_add_hom_single _ _ _⟩, },
  { rintros x ⟨v, rfl⟩,
    exact dfinsupp_sum_add_hom_mem _ v _ (λ i _, (le_supr p i : p i ≤ _) (v i).prop) }
end

/-- The bounded supremum of a family of commutative additive submonoids is equal to the range of
`dfinsupp.sum_add_hom` composed with `dfinsupp.filter_add_monoid_hom`; that is, every element in the
bounded `supr` can be produced from taking a finite number of non-zero elements from the `S i` that
satisfy `p i`, coercing them to `γ`, and summing them. -/
lemma bsupr_eq_range_dfinsupp_lsum (p : ι → Prop)
  [decidable_pred p] (S : ι → submodule R N) :
  (⨆ i (h : p i), S i) =
    ((dfinsupp.lsum ℕ (λ i, (S i).subtype)).comp (dfinsupp.filter_linear_map R _ p)).range :=
begin
  apply le_antisymm,
  { refine supr₂_le (λ i hi y hy, ⟨dfinsupp.single i ⟨y, hy⟩, _⟩),
    rw [linear_map.comp_apply, filter_linear_map_apply, filter_single_pos _ _ hi],
    exact dfinsupp.sum_add_hom_single _ _ _, },
  { rintros x ⟨v, rfl⟩,
    refine dfinsupp_sum_add_hom_mem _ _ _ (λ i hi, _),
    refine mem_supr_of_mem i _,
    by_cases hp : p i,
    { simp [hp], },
    { simp [hp] }, }
end

lemma mem_supr_iff_exists_dfinsupp (p : ι → submodule R N) (x : N) :
  x ∈ supr p ↔ ∃ f : Π₀ i, p i, dfinsupp.lsum ℕ (λ i, (p i).subtype) f = x :=
set_like.ext_iff.mp (supr_eq_range_dfinsupp_lsum p) x

/-- A variant of `submodule.mem_supr_iff_exists_dfinsupp` with the RHS fully unfolded. -/
lemma mem_supr_iff_exists_dfinsupp' (p : ι → submodule R N) [Π i (x : p i), decidable (x ≠ 0)]
  (x : N) :
  x ∈ supr p ↔ ∃ f : Π₀ i, p i, f.sum (λ i xi, ↑xi) = x :=
begin
  rw mem_supr_iff_exists_dfinsupp,
  simp_rw [dfinsupp.lsum_apply_apply, dfinsupp.sum_add_hom_apply],
  congr',
end

lemma mem_bsupr_iff_exists_dfinsupp (p : ι → Prop) [decidable_pred p] (S : ι → submodule R N)
  (x : N) :
  x ∈ (⨆ i (h : p i), S i) ↔
    ∃ f : Π₀ i, S i, dfinsupp.lsum ℕ (λ i, (S i).subtype) (f.filter p) = x :=
set_like.ext_iff.mp (bsupr_eq_range_dfinsupp_lsum p S) x

open_locale big_operators
omit dec_ι
lemma mem_supr_finset_iff_exists_sum {s : finset ι} (p : ι → submodule R N) (a : N) :
  a ∈ (⨆ i ∈ s, p i) ↔ ∃ μ : Π i, p i, ∑ i in s, (μ i : N) = a :=
begin
  classical,
  rw submodule.mem_supr_iff_exists_dfinsupp',
  split; rintro ⟨μ, hμ⟩,
  { use λ i, ⟨μ i, (supr_const_le : _ ≤ p i) (coe_mem $ μ i)⟩,
    rw ← hμ, symmetry, apply finset.sum_subset,
    { intro x, contrapose, intro hx,
      rw [mem_support_iff, not_ne_iff],
      ext, rw [coe_zero, ← mem_bot R], convert coe_mem (μ x),
      symmetry, exact supr_neg hx },
    { intros x _ hx, rw [mem_support_iff, not_ne_iff] at hx, rw hx, refl } },
  { refine ⟨dfinsupp.mk s _, _⟩,
    { rintro ⟨i, hi⟩, refine ⟨μ i, _⟩,
      rw supr_pos, { exact coe_mem _ }, { exact hi } },
    simp only [dfinsupp.sum],
    rw [finset.sum_subset support_mk_subset, ← hμ],
    exact finset.sum_congr rfl (λ x hx, congr_arg coe $ mk_of_mem hx),
    { intros x _ hx, rw [mem_support_iff, not_ne_iff] at hx, rw hx, refl } }
end

end submodule

namespace complete_lattice

open dfinsupp

section semiring
variables [semiring R] [add_comm_monoid N] [module R N]

/-- Independence of a family of submodules can be expressed as a quantifier over `dfinsupp`s.

This is an intermediate result used to prove
`complete_lattice.independent_of_dfinsupp_lsum_injective` and
`complete_lattice.independent.dfinsupp_lsum_injective`. -/
lemma independent_iff_forall_dfinsupp (p : ι → submodule R N) :
  independent p ↔
    ∀ i (x : p i) (v : Π₀ (i : ι), ↥(p i)), lsum ℕ (λ i, (p i).subtype) (erase i v) = x → x = 0 :=
begin
  simp_rw [complete_lattice.independent_def, submodule.disjoint_def,
    submodule.mem_bsupr_iff_exists_dfinsupp, exists_imp_distrib, filter_ne_eq_erase],
  apply forall_congr (λ i, _),
  refine subtype.forall'.trans _,
  simp_rw submodule.coe_eq_zero,
  refl,
end

/- If `dfinsupp.lsum` applied with `submodule.subtype` is injective then the submodules are
independent. -/
lemma independent_of_dfinsupp_lsum_injective (p : ι → submodule R N)
  (h : function.injective (lsum ℕ (λ i, (p i).subtype))) :
  independent p :=
begin
  rw independent_iff_forall_dfinsupp,
  intros i x v hv,
  replace hv : lsum ℕ (λ i, (p i).subtype) (erase i v) = lsum ℕ (λ i, (p i).subtype) (single i x),
  { simpa only [lsum_single] using hv, },
  have := dfinsupp.ext_iff.mp (h hv) i,
  simpa [eq_comm] using this,
end

/- If `dfinsupp.sum_add_hom` applied with `add_submonoid.subtype` is injective then the additive
submonoids are independent. -/
lemma independent_of_dfinsupp_sum_add_hom_injective (p : ι → add_submonoid N)
  (h : function.injective (sum_add_hom (λ i, (p i).subtype))) :
  independent p :=
begin
  rw ←independent_map_order_iso_iff (add_submonoid.to_nat_submodule : add_submonoid N ≃o _),
  exact independent_of_dfinsupp_lsum_injective _ h,
end

/-- Combining `dfinsupp.lsum` with `linear_map.to_span_singleton` is the same as `finsupp.total` -/
lemma lsum_comp_map_range_to_span_singleton
  [Π (m : R), decidable (m ≠ 0)]
  (p : ι → submodule R N) {v : ι → N} (hv : ∀ (i : ι), v i ∈ p i) :
  ((lsum ℕ) (λ i, (p i).subtype) : _ →ₗ[R] _).comp
    ((map_range.linear_map
      (λ i, linear_map.to_span_singleton R ↥(p i) ⟨v i, hv i⟩) : _ →ₗ[R] _).comp
      (finsupp_lequiv_dfinsupp R : (ι →₀ R) ≃ₗ[R] _).to_linear_map) =
  finsupp.total ι N R v :=
by { ext, simp }

end semiring

section ring
variables [ring R] [add_comm_group N] [module R N]


/- If `dfinsupp.sum_add_hom` applied with `add_submonoid.subtype` is injective then the additive
subgroups are independent. -/
lemma independent_of_dfinsupp_sum_add_hom_injective' (p : ι → add_subgroup N)
  (h : function.injective (sum_add_hom (λ i, (p i).subtype))) :
  independent p :=
begin
  rw ←independent_map_order_iso_iff (add_subgroup.to_int_submodule : add_subgroup N ≃o _),
  exact independent_of_dfinsupp_lsum_injective _ h,
end

/-- The canonical map out of a direct sum of a family of submodules is injective when the submodules
are `complete_lattice.independent`.

Note that this is not generally true for `[semiring R]`, for instance when `A` is the
`ℕ`-submodules of the positive and negative integers.

See `counterexamples/direct_sum_is_internal.lean` for a proof of this fact. -/
lemma independent.dfinsupp_lsum_injective {p : ι → submodule R N}
  (h : independent p) : function.injective (lsum ℕ (λ i, (p i).subtype)) :=
begin
  -- simplify everything down to binders over equalities in `N`
  rw independent_iff_forall_dfinsupp at h,
  suffices : (lsum ℕ (λ i, (p i).subtype)).ker = ⊥,
  { -- Lean can't find this without our help
    letI : add_comm_group (Π₀ i, p i) := @dfinsupp.add_comm_group _ (λ i, p i) _,
    rw linear_map.ker_eq_bot at this, exact this },
  rw linear_map.ker_eq_bot',
  intros m hm,
  ext i : 1,
  -- split `m` into the piece at `i` and the pieces elsewhere, to match `h`
  rw [dfinsupp.zero_apply, ←neg_eq_zero],
  refine h i (-m i) m _,
  rwa [←erase_add_single i m, linear_map.map_add, lsum_single, submodule.subtype_apply,
    add_eq_zero_iff_eq_neg, ←submodule.coe_neg] at hm,
end

/-- The canonical map out of a direct sum of a family of additive subgroups is injective when the
additive subgroups are `complete_lattice.independent`. -/
lemma independent.dfinsupp_sum_add_hom_injective {p : ι → add_subgroup N}
  (h : independent p) : function.injective (sum_add_hom (λ i, (p i).subtype)) :=
begin
  rw ←independent_map_order_iso_iff (add_subgroup.to_int_submodule : add_subgroup N ≃o _) at h,
  exact h.dfinsupp_lsum_injective,
end

/-- A family of submodules over an additive group are independent if and only iff `dfinsupp.lsum`
applied with `submodule.subtype` is injective.

Note that this is not generally true for `[semiring R]`; see
`complete_lattice.independent.dfinsupp_lsum_injective` for details. -/
lemma independent_iff_dfinsupp_lsum_injective (p : ι → submodule R N) :
  independent p ↔ function.injective (lsum ℕ (λ i, (p i).subtype)) :=
⟨independent.dfinsupp_lsum_injective, independent_of_dfinsupp_lsum_injective p⟩

/-- A family of additive subgroups over an additive group are independent if and only if
`dfinsupp.sum_add_hom` applied with `add_subgroup.subtype` is injective. -/
lemma independent_iff_dfinsupp_sum_add_hom_injective (p : ι → add_subgroup N) :
  independent p ↔ function.injective (sum_add_hom (λ i, (p i).subtype)) :=
⟨independent.dfinsupp_sum_add_hom_injective, independent_of_dfinsupp_sum_add_hom_injective' p⟩

omit dec_ι

/-- If a family of submodules is `independent`, then a choice of nonzero vector from each submodule
forms a linearly independent family.

See also `complete_lattice.independent.linear_independent'`. -/
lemma independent.linear_independent [no_zero_smul_divisors R N] (p : ι → submodule R N)
  (hp : independent p) {v : ι → N} (hv : ∀ i, v i ∈ p i) (hv' : ∀ i, v i ≠ 0) :
  linear_independent R v :=
begin
  classical,
  rw linear_independent_iff,
  intros l hl,
  let a := dfinsupp.map_range.linear_map
    (λ i, linear_map.to_span_singleton R (p i) (⟨v i, hv i⟩)) l.to_dfinsupp,
  have ha : a = 0,
  { apply hp.dfinsupp_lsum_injective,
    rwa ←lsum_comp_map_range_to_span_singleton _ hv at hl },
  ext i,
  apply smul_left_injective R (hv' i),
  have : l i • v i = a i := rfl,
  simp [this, ha],
end

lemma independent_iff_linear_independent_of_ne_zero [no_zero_smul_divisors R N] {v : ι → N}
  (h_ne_zero : ∀ i, v i ≠ 0) :
  independent (λ i, R ∙ v i) ↔ linear_independent R v :=
⟨λ hv, hv.linear_independent _ (λ i, submodule.mem_span_singleton_self $ v i) h_ne_zero,
 λ hv, hv.independent_span_singleton⟩

end ring

end complete_lattice
