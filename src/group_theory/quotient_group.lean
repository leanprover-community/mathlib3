/-
Copyright (c) 2018 Kevin Buzzard, Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Patrick Massot

This file is to a certain extent based on `quotient_module.lean` by Johannes Hölzl.
-/
import group_theory.coset

/-!
# Quotients of groups by normal subgroups

This files develops the basic theory of quotients of groups by normal subgroups. In particular it
proves Noether's first and second isomorphism theorems.

## Main definitions

* `mk'`: the canonical group homomorphism `G →* G/N` given a normal subgroup `N` of `G`.
* `lift φ`: the group homomorphism `G/N →* H` given a group homomorphism `φ : G →* H` such that
  `N ⊆ ker φ`.
* `map f`: the group homomorphism `G/N →* H/M` given a group homomorphism `f : G →* H` such that
  `N ⊆ f⁻¹(M)`.

## Main statements

* `quotient_ker_equiv_range`: Noether's first isomorphism theorem, an explicit isomorphism
  `G/ker φ → range φ` for every group homomorphism `φ : G →* H`.
* `quotient_inf_equiv_prod_normal_quotient`: Noether's second isomorphism theorem, an explicit
  isomorphism between `H/(H ∩ N)` and `(HN)/N` given a subgroup `H` and a normal subgroup `N` of a
  group `G`.
* `quotient_group.quotient_quotient_equiv_quotient`: Noether's third isomorphism theorem,
  the canonical isomorphism between `(G / M) / (M / N)` and `G / N`, where `N ≤ M`.

## Tags

isomorphism theorems, quotient groups
-/

universes u v

namespace quotient_group

variables {G : Type u} [group G] (N : subgroup G) [nN : N.normal] {H : Type v} [group H]
include nN

-- Define the `div_inv_monoid` before the `group` structure,
-- to make sure we have `inv` fully defined before we show `mul_left_inv`.
-- TODO: is there a non-invasive way of defining this in one declaration?
@[to_additive quotient_add_group.div_inv_monoid]
instance : div_inv_monoid (quotient N) :=
{ one := (1 : G),
  mul := quotient.map₂' (*)
  (λ a₁ b₁ hab₁ a₂ b₂ hab₂,
    ((N.mul_mem_cancel_right (N.inv_mem hab₂)).1
        (by rw [mul_inv_rev, mul_inv_rev, ← mul_assoc (a₂⁻¹ * a₁⁻¹),
          mul_assoc _ b₂, ← mul_assoc b₂, mul_inv_self, one_mul, mul_assoc (a₂⁻¹)];
          exact nN.conj_mem _ hab₁ _))),
  mul_assoc := λ a b c, quotient.induction_on₃' a b c
    (λ a b c, congr_arg mk (mul_assoc a b c)),
  one_mul := λ a, quotient.induction_on' a
    (λ a, congr_arg mk (one_mul a)),
  mul_one := λ a, quotient.induction_on' a
    (λ a, congr_arg mk (mul_one a)),
  inv := λ a, quotient.lift_on' a (λ a, ((a⁻¹ : G) : quotient N))
    (λ a b hab, quotient.sound' begin
      show a⁻¹⁻¹ * b⁻¹ ∈ N,
      rw ← mul_inv_rev,
      exact N.inv_mem (nN.mem_comm hab)
    end) }

@[to_additive quotient_add_group.add_group]
instance : group (quotient N) :=
{ mul_left_inv := λ a, quotient.induction_on' a
    (λ a, congr_arg mk (mul_left_inv a)),
 .. quotient.div_inv_monoid _ }

/-- The group homomorphism from `G` to `G/N`. -/
@[to_additive quotient_add_group.mk' "The additive group homomorphism from `G` to `G/N`."]
def mk' : G →* quotient N := monoid_hom.mk' (quotient_group.mk) (λ _ _, rfl)

@[to_additive, simp]
lemma coe_mk' : (mk' N : G → quotient N) = coe := rfl

@[to_additive, simp]
lemma mk'_apply (x : G) : mk' N x = x := rfl

@[simp, to_additive quotient_add_group.eq_zero_iff]
lemma eq_one_iff {N : subgroup G} [nN : N.normal] (x : G) : (x : quotient N) = 1 ↔ x ∈ N :=
begin
  refine quotient_group.eq.trans _,
  rw [mul_one, subgroup.inv_mem_iff],
end

@[simp, to_additive quotient_add_group.ker_mk]
lemma ker_mk :
  monoid_hom.ker (quotient_group.mk' N : G →* quotient_group.quotient N) = N :=
subgroup.ext eq_one_iff

@[to_additive quotient_add_group.eq_iff_sub_mem]
lemma eq_iff_div_mem {N : subgroup G} [nN : N.normal] {x y : G} :
  (x : quotient N) = y ↔ x / y ∈ N :=
begin
  refine eq_comm.trans (quotient_group.eq.trans _),
  rw [nN.mem_comm_iff, div_eq_mul_inv]
end

-- for commutative groups we don't need normality assumption
omit nN

@[to_additive quotient_add_group.add_comm_group]
instance {G : Type*} [comm_group G] (N : subgroup G) : comm_group (quotient N) :=
{ mul_comm := λ a b, quotient.induction_on₂' a b
    (λ a b, congr_arg mk (mul_comm a b)),
  .. @quotient_group.quotient.group _ _ N N.normal_of_comm }

include nN

local notation ` Q ` := quotient N

@[simp, to_additive quotient_add_group.coe_zero]
lemma coe_one : ((1 : G) : Q) = 1 := rfl

@[simp, to_additive quotient_add_group.coe_add]
lemma coe_mul (a b : G) : ((a * b : G) : Q) = a * b := rfl

@[simp, to_additive quotient_add_group.coe_neg]
lemma coe_inv (a : G) : ((a⁻¹ : G) : Q) = a⁻¹ := rfl

@[simp] lemma coe_pow (a : G) (n : ℕ) : ((a ^ n : G) : Q) = a ^ n :=
(mk' N).map_pow a n

@[simp] lemma coe_gpow (a : G) (n : ℤ) : ((a ^ n : G) : Q) = a ^ n :=
(mk' N).map_gpow a n

/-- A group homomorphism `φ : G →* H` with `N ⊆ ker(φ)` descends (i.e. `lift`s) to a
group homomorphism `G/N →* H`. -/
@[to_additive quotient_add_group.lift "An `add_group` homomorphism `φ : G →+ H` with `N ⊆ ker(φ)`
descends (i.e. `lift`s) to a group homomorphism `G/N →* H`."]
def lift (φ : G →* H) (HN : ∀x∈N, φ x = 1) : Q →* H :=
monoid_hom.mk'
  (λ q : Q, q.lift_on' φ $ assume a b (hab : a⁻¹ * b ∈ N),
  (calc φ a = φ a * 1           : (mul_one _).symm
  ...       = φ a * φ (a⁻¹ * b) : HN (a⁻¹ * b) hab ▸ rfl
  ...       = φ (a * (a⁻¹ * b)) : (is_mul_hom.map_mul φ a (a⁻¹ * b)).symm
  ...       = φ b               : by rw mul_inv_cancel_left))
  (λ q r, quotient.induction_on₂' q r $ is_mul_hom.map_mul φ)

@[simp, to_additive quotient_add_group.lift_mk]
lemma lift_mk {φ : G →* H} (HN : ∀x∈N, φ x = 1) (g : G) :
  lift N φ HN (g : Q) = φ g := rfl

@[simp, to_additive quotient_add_group.lift_mk']
lemma lift_mk' {φ : G →* H} (HN : ∀x∈N, φ x = 1) (g : G) :
  lift N φ HN (mk g : Q) = φ g := rfl

@[simp, to_additive quotient_add_group.lift_quot_mk]
lemma lift_quot_mk {φ : G →* H} (HN : ∀x∈N, φ x = 1) (g : G) :
  lift N φ HN (quot.mk _ g : Q) = φ g := rfl

/-- A group homomorphism `f : G →* H` induces a map `G/N →* H/M` if `N ⊆ f⁻¹(M)`. -/
@[to_additive quotient_add_group.map "An `add_group` homomorphism `f : G →+ H` induces a map
`G/N →+ H/M` if `N ⊆ f⁻¹(M)`."]
def map (M : subgroup H) [M.normal] (f : G →* H) (h : N ≤ M.comap f) :
  quotient N →* quotient M :=
begin
  refine quotient_group.lift N ((mk' M).comp f) _,
  assume x hx,
  refine quotient_group.eq.2 _,
  rw [mul_one, subgroup.inv_mem_iff],
  exact h hx,
end

@[simp, to_additive quotient_add_group.map_coe] lemma map_coe
  (M : subgroup H) [M.normal] (f : G →* H) (h : N ≤ M.comap f) (x : G) :
  map N M f h ↑x = ↑(f x) :=
lift_mk' _ _ x

@[to_additive quotient_add_group.map_mk'] lemma map_mk'
  (M : subgroup H) [M.normal] (f : G →* H) (h : N ≤ M.comap f) (x : G) :
  map N M f h (mk' _ x) = ↑(f x) :=
quotient_group.lift_mk' _ _ x

omit nN
variables (φ : G →* H)

open function monoid_hom

/-- The induced map from the quotient by the kernel to the codomain. -/
@[to_additive quotient_add_group.ker_lift "The induced map from the quotient by the kernel to the
codomain."]
def ker_lift : quotient (ker φ) →* H :=
lift _ φ $ λ g, φ.mem_ker.mp

@[simp, to_additive quotient_add_group.ker_lift_mk]
lemma ker_lift_mk (g : G) : (ker_lift φ) g = φ g :=
lift_mk _ _ _

@[simp, to_additive quotient_add_group.ker_lift_mk']
lemma ker_lift_mk' (g : G) : (ker_lift φ) (mk g) = φ g :=
lift_mk' _ _ _

@[to_additive quotient_add_group.injective_ker_lift]
lemma ker_lift_injective : injective (ker_lift φ) :=
assume a b, quotient.induction_on₂' a b $
  assume a b (h : φ a = φ b), quotient.sound' $
show a⁻¹ * b ∈ ker φ, by rw [mem_ker,
  is_mul_hom.map_mul φ, ← h, is_group_hom.map_inv φ, inv_mul_self]

-- Note that `ker φ` isn't definitionally `ker (φ.range_restrict)`
-- so there is a bit of annoying code duplication here

/-- The induced map from the quotient by the kernel to the range. -/
@[to_additive quotient_add_group.range_ker_lift "The induced map from the quotient by the kernel to
the range."]
def range_ker_lift : quotient (ker φ) →* φ.range :=
lift _ φ.range_restrict $ λ g hg, (mem_ker _).mp $ by rwa range_restrict_ker

@[to_additive quotient_add_group.range_ker_lift_injective]
lemma range_ker_lift_injective : injective (range_ker_lift φ) :=
assume a b, quotient.induction_on₂' a b $
  assume a b (h : φ.range_restrict a = φ.range_restrict b), quotient.sound' $
show a⁻¹ * b ∈ ker φ, by rw [←range_restrict_ker, mem_ker,
  φ.range_restrict.map_mul, ← h, φ.range_restrict.map_inv, inv_mul_self]

@[to_additive quotient_add_group.range_ker_lift_surjective]
lemma range_ker_lift_surjective : surjective (range_ker_lift φ) :=
begin
  rintro ⟨_, g, rfl⟩,
  use mk g,
  refl,
end

/-- **Noether's first isomorphism theorem** (a definition): the canonical isomorphism between
`G/(ker φ)` to `range φ`. -/
@[to_additive quotient_add_group.quotient_ker_equiv_range "The first isomorphism theorem
(a definition): the canonical isomorphism between `G/(ker φ)` to `range φ`."]
noncomputable def quotient_ker_equiv_range : (quotient (ker φ)) ≃* range φ :=
mul_equiv.of_bijective (range_ker_lift φ) ⟨range_ker_lift_injective φ, range_ker_lift_surjective φ⟩

/-- The canonical isomorphism `G/(ker φ) ≃* H` induced by a homomorphism `φ : G →* H`
with a right inverse `ψ : H → G`. -/
@[to_additive quotient_add_group.quotient_ker_equiv_of_right_inverse "The canonical isomorphism
`G/(ker φ) ≃+ H` induced by a homomorphism `φ : G →+ H` with a right inverse `ψ : H → G`.",
  simps]
def quotient_ker_equiv_of_right_inverse (ψ : H → G) (hφ : function.right_inverse ψ φ) :
  quotient (ker φ) ≃* H :=
{ to_fun := ker_lift φ,
  inv_fun := mk ∘ ψ,
  left_inv := λ x, ker_lift_injective φ (by rw [function.comp_app, ker_lift_mk', hφ]),
  right_inv := hφ,
  .. ker_lift φ }

/-- The canonical isomorphism `G/(ker φ) ≃* H` induced by a surjection `φ : G →* H`.

For a `computable` version, see `quotient_group.quotient_ker_equiv_of_right_inverse`.
-/
@[to_additive quotient_add_group.quotient_ker_equiv_of_surjective "The canonical isomorphism
`G/(ker φ) ≃+ H` induced by a surjection `φ : G →+ H`.

For a `computable` version, see `quotient_add_group.quotient_ker_equiv_of_right_inverse`."]
noncomputable def quotient_ker_equiv_of_surjective (hφ : function.surjective φ) :
  quotient (ker φ) ≃* H :=
quotient_ker_equiv_of_right_inverse φ _ hφ.has_right_inverse.some_spec

/-- If two normal subgroups `M` and `N` of `G` are the same, their quotient groups are
isomorphic. -/
@[to_additive "If two normal subgroups `M` and `N` of `G` are the same, their quotient groups are
isomorphic."]
def equiv_quotient_of_eq {M N : subgroup G} [M.normal] [N.normal] (h : M = N) :
  quotient M ≃* quotient N :=
{ to_fun := (lift M (mk' N) (λ m hm, quotient_group.eq.mpr (by simpa [← h] using M.inv_mem hm))),
  inv_fun := (lift N (mk' M) (λ n hn, quotient_group.eq.mpr (by simpa [← h] using N.inv_mem hn))),
  left_inv := λ x, x.induction_on' $ by { intro, refl },
  right_inv := λ x, x.induction_on' $ by { intro, refl },
  map_mul' := λ x y, by rw map_mul }

/-- Let `A', A, B', B` be subgroups of `G`. If `A' ≤ B'` and `A ≤ B`,
then there is a map `A / (A' ⊓ A) →* B / (B' ⊓ B)` induced by the inclusions. -/
@[to_additive "Let `A', A, B', B` be subgroups of `G`. If `A' ≤ B'` and `A ≤ B`,
then there is a map `A / (A' ⊓ A) →+ B / (B' ⊓ B)` induced by the inclusions."]
def quotient_map_subgroup_of_of_le {A' A B' B : subgroup G}
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal]
  (h' : A' ≤ B') (h : A ≤ B) :
  quotient (A'.subgroup_of A) →* quotient (B'.subgroup_of B) :=
map _ _ (subgroup.inclusion h) $
  by simp [subgroup.subgroup_of, subgroup.comap_comap]; exact subgroup.comap_mono h'

/-- Let `A', A, B', B` be subgroups of `G`.
If `A' = B'` and `A = B`, then the quotients `A / (A' ⊓ A)` and `B / (B' ⊓ B)` are isomorphic.

Applying this equiv is nicer than rewriting along the equalities, since the type of
`(A'.subgroup_of A : subgroup A)` depends on on `A`.
-/
@[to_additive "Let `A', A, B', B` be subgroups of `G`.
If `A' = B'` and `A = B`, then the quotients `A / (A' ⊓ A)` and `B / (B' ⊓ B)` are isomorphic.

Applying this equiv is nicer than rewriting along the equalities, since the type of
`(A'.add_subgroup_of A : add_subgroup A)` depends on on `A`.
"]
def equiv_quotient_subgroup_of_of_eq {A' A B' B : subgroup G}
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal]
  (h' : A' = B') (h : A = B) :
  quotient (A'.subgroup_of A) ≃* quotient (B'.subgroup_of B) :=
by apply monoid_hom.to_mul_equiv
    (quotient_map_subgroup_of_of_le h'.le h.le) (quotient_map_subgroup_of_of_le h'.ge h.ge);
  { ext ⟨x⟩, simp [quotient_map_subgroup_of_of_le, map, lift, mk', subgroup.inclusion], refl }

section snd_isomorphism_thm

open subgroup

/-- **Noether's second isomorphism theorem**: given two subgroups `H` and `N` of a group `G`, where
`N` is normal, defines an isomorphism between `H/(H ∩ N)` and `(HN)/N`. -/
@[to_additive "The second isomorphism theorem: given two subgroups `H` and `N` of a group `G`,
where `N` is normal, defines an isomorphism between `H/(H ∩ N)` and `(H + N)/N`"]
noncomputable def quotient_inf_equiv_prod_normal_quotient (H N : subgroup G) [N.normal] :
  quotient ((H ⊓ N).comap H.subtype) ≃* quotient (N.comap (H ⊔ N).subtype) :=
/- φ is the natural homomorphism H →* (HN)/N. -/
let φ : H →* quotient (N.comap (H ⊔ N).subtype) :=
  (mk' $ N.comap (H ⊔ N).subtype).comp (inclusion le_sup_left) in
have φ_surjective : function.surjective φ := λ x, x.induction_on' $
  begin
    rintro ⟨y, (hy : y ∈ ↑(H ⊔ N))⟩, rw mul_normal H N at hy,
    rcases hy with ⟨h, n, hh, hn, rfl⟩,
    use [h, hh], apply quotient.eq.mpr, change h⁻¹ * (h * n) ∈ N,
    rwa [←mul_assoc, inv_mul_self, one_mul],
  end,
(equiv_quotient_of_eq (by simp [comap_comap, ←comap_ker])).trans
  (quotient_ker_equiv_of_surjective φ φ_surjective)

end snd_isomorphism_thm

section third_iso_thm

variables (M : subgroup G) [nM : M.normal]

include nM nN

@[to_additive quotient_add_group.map_normal]
instance map_normal : (M.map (quotient_group.mk' N)).normal :=
{ conj_mem := begin
    rintro _ ⟨x, hx, rfl⟩ y,
    refine induction_on' y (λ y, ⟨y * x * y⁻¹, subgroup.normal.conj_mem nM x hx y, _⟩),
    simp only [mk'_apply, coe_mul, coe_inv]
  end }

variables (h : N ≤ M)

/-- The map from the third isomorphism theorem for groups: `(G / N) / (M / N) → G / M`. -/
@[to_additive quotient_add_group.quotient_quotient_equiv_quotient_aux
"The map from the third isomorphism theorem for additive groups: `(A / N) / (M / N) → A / M`."]
def quotient_quotient_equiv_quotient_aux :
  quotient (M.map (mk' N)) →* quotient M :=
lift (M.map (mk' N))
  (map N M (monoid_hom.id G) h)
  (by { rintro _ ⟨x, hx, rfl⟩, rw map_mk' N M _ _ x,
        exact (quotient_group.eq_one_iff _).mpr hx })

@[simp, to_additive quotient_add_group.quotient_quotient_equiv_quotient_aux_coe]
lemma quotient_quotient_equiv_quotient_aux_coe (x : quotient_group.quotient N) :
  quotient_quotient_equiv_quotient_aux N M h x = quotient_group.map N M (monoid_hom.id G) h x :=
quotient_group.lift_mk' _ _ x

@[to_additive quotient_add_group.quotient_quotient_equiv_quotient_aux_coe_coe]
lemma quotient_quotient_equiv_quotient_aux_coe_coe (x : G) :
  quotient_quotient_equiv_quotient_aux N M h (x : quotient_group.quotient N) =
    x :=
quotient_group.lift_mk' _ _ x

/-- **Noether's third isomorphism theorem** for groups: `(G / N) / (M / N) ≃ G / M`. -/
@[to_additive quotient_add_group.quotient_quotient_equiv_quotient
"**Noether's third isomorphism theorem** for additive groups: `(A / N) / (M / N) ≃ A / M`."]
def quotient_quotient_equiv_quotient :
  quotient_group.quotient (M.map (quotient_group.mk' N)) ≃* quotient_group.quotient M :=
{ to_fun := quotient_quotient_equiv_quotient_aux N M h,
  inv_fun := quotient_group.map _ _ (quotient_group.mk' N) (subgroup.le_comap_map _ _),
  left_inv := λ x, quotient_group.induction_on' x $ λ x, quotient_group.induction_on' x $
    λ x, by simp,
  right_inv := λ x, quotient_group.induction_on' x $ λ x, by simp,
  map_mul' := monoid_hom.map_mul _ }

end third_iso_thm

section Zassenhaus
open subgroup

@[to_additive] lemma normal_subgroup_mul
  {A B C : subgroup G} (hA : A ≤ C) [hN : (A.subgroup_of C).normal] (hB : B ≤ C) :
  ((A ⊔ B : subgroup G) : set G) = A * B :=
begin
  suffices h : ((A ⊔ B).subgroup_of C : set C) = A.subgroup_of C * B.subgroup_of C,
  have key : (C.subtype) ⁻¹' (↑A * ↑B) = (C.subtype) ⁻¹' ↑A * (C.subtype) ⁻¹' ↑B,
  { refine set.preimage_mul_of_injective C.subtype ↑A ↑B subtype.coe_injective _ _;
    simp only [← monoid_hom.coe_range, subtype_range]; assumption, },
  have hsub : (A : set G) * B ⊆ C,
  { rintro _ ⟨p, q, hp, hq, rfl⟩,
    exact mul_mem _ (hA hp) (hB hq) },
  apply_fun set.image (C.subtype) at h,
  simp only [subgroup_of, coe_comap, ← key] at h,
  simp only [subtype.image_preimage_coe ↑C _, subgroup.coe_subtype,
    set.inter_eq_self_of_subset_left hsub, inf_of_le_left (sup_le hA hB),
    set.inter_eq_self_of_subset_left (set_like.coe_subset_coe.mpr (sup_le hA hB))] at h,
  exact h,
  simp [subgroup_of_sup A B C hA hB, normal_mul],
end

@[to_additive] lemma Zassenhaus_subgroup {A' A B' B : subgroup G} (hA : A' ≤ A) (hB : B' ≤ B) :
  ((A' ⊓ B) ⊔ (A ⊓ B') ≤ A ⊓ B) :=
sup_le (inf_le_inf hA (le_refl _)) (inf_le_inf (le_refl _) hB)

instance Zassenhaus
  {A' A B' B : subgroup G} [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal] :
  (((A' ⊓ B) ⊔ (A ⊓ B')).subgroup_of (A ⊓ B)).normal :=
begin
  haveI h₁ : ((A' ⊓ B).subgroup_of (A ⊓ B)).normal :=
  by { have := inf_subgroup_of_inf_normal_of_right B A' A hA.out,
    rw inf_comm, rwa @inf_comm _ _ A' B },
  haveI h₂ : ((A ⊓ B').subgroup_of (A ⊓ B)).normal :=
  by { have := inf_subgroup_of_inf_normal_of_right A B' B hB.out,
    rw inf_comm, rwa @inf_comm _ _ B A },
  rw subgroup_of_sup,
  { exact subgroup.sup_normal ((A' ⊓ B).subgroup_of (A ⊓ B)) ((A ⊓ B').subgroup_of (A ⊓ B)) },
  { exact inf_le_inf hA.out (le_refl _) },
  { exact inf_le_inf (le_refl _) hB.out },
end

/-- bruh  -/
@[derive inhabited] def Zassenhaus_quot (A' A B' B : subgroup G) :=
quotient_group.quotient $ ((A' ⊓ B) ⊔ (A ⊓ B')).subgroup_of (A ⊓ B)

instance Zassenhaus_group
  {A' A B' B : subgroup G} [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal] :
  group (Zassenhaus_quot A' A B' B) :=
begin
  dsimp [Zassenhaus_quot],
  haveI := @quotient_group.Zassenhaus _ _ A' A B' B hA hB,
  apply_instance,
end

lemma Zassenhaus_aux
  {A' A : subgroup G} (B : subgroup G) (hA : A' ≤ A) [hAN : (A'.subgroup_of A).normal] :
  ↑(A' ⊔ A ⊓ B) = (A' : set G) * (A ⊓ B : subgroup G) :=
normal_subgroup_mul hA (inf_le_of_left_le (le_refl A))

lemma Zassenhaus_quot_aux {A' A B' B : subgroup G} (hA : A' ≤ A) (hB : B' ≤ B)
  [hAN : (A'.subgroup_of A).normal] :
  ↑((A' ⊓ B) ⊔ (A ⊓ B')) = (A : set G) ⊓ B ⊓ (A' * B') :=
begin
  have : ↑((A' ⊓ B) ⊔ (A ⊓ B')) = ((A' : set G) ⊓ B) * (A ⊓ B'),
  { haveI : ((A' ⊓ B).subgroup_of (A ⊓ B)).normal :=
    by { have := inf_subgroup_of_inf_normal_of_right B A' A hA,
      rw inf_comm, rwa @inf_comm _ _ A' B },
    refine normal_subgroup_mul (inf_le_inf hA (le_refl B)) (inf_le_inf (le_refl A) hB), },
  rw this,
  clear this,
  have := mul_inf_assoc (A' ⊓ B) B' A _,
  rw @inf_comm _ _ _ A at this,
  rw @inf_comm _ _ (↑(A' ⊓ B) * ↑B') _ at this,
  have bleh : ↑(A' ⊓ B) * ↑B' = (B : set G) ⊓ (A' * B'),
  { have yes := inf_mul_assoc B A' B' hB, rwa inf_comm at yes },
  rw bleh at this,
  rw ← inf_assoc at this,
  convert this,
  exact inf_le_of_left_le hA,
end

lemma inv_mul_eq_mul_inv {u v a b : G} (h : u * v = a * b) : a⁻¹ * u = b * v⁻¹ :=
  inv_mul_eq_of_eq_mul (mul_assoc a b v⁻¹ ▸ eq_mul_inv_of_mul_eq h)


/-- bruh -/
noncomputable def Zassenhaus_fun_aux {A' A : subgroup G} (B' B : subgroup G) (hA : A' ≤ A)
  [hAN : (A'.subgroup_of A).normal] (x : A' ⊔ A ⊓ B) : Zassenhaus_quot A' A B' B :=
quotient.mk' ⟨_, ((mem_sup_iff (Zassenhaus_aux B hA)).mp x.2).some_spec.some_spec.2.1⟩

theorem Zassenhaus_fun_aux_app {A' A B' B : subgroup G} (hA : A' ≤ A)
  [hAN : (A'.subgroup_of A).normal] (a : A') (x : A ⊓ B) (h) :
  Zassenhaus_fun_aux B' B hA ⟨a * x, h⟩ = quotient.mk' x :=
begin
  apply quotient.sound',
  have H := (mem_sup_iff (Zassenhaus_aux B hA)).mp h,
  let u := H.some, let v := H.some_spec.some,
  cases a with a ha, cases x with x hx,
  obtain ⟨hu : u ∈ A', hv : v ∈ A ⊓ B, huv : u * v = a * x⟩ := H.some_spec.some_spec,
  refine mem_subgroup_of.2 (mem_of_le le_sup_left (_ : v⁻¹ * x ∈ A' ⊓ B)),
  have := mul_mem A' (inv_mem A' ha) hu,
  rw inv_mul_eq_mul_inv huv at this,
  haveI := inf_subgroup_of_inf_normal_of_left B hA,
  refine subgroup_normal.mem_comm (inf_le_inf hA (le_refl B)) (inv_mem (A ⊓ B) hv) _,
  refine mem_inf.mpr ⟨this, mul_mem _ (mem_inf.mp hx).2 (inv_mem _ (mem_inf.mp hv).2)⟩,
end

theorem Zassenhaus_fun_aux_app' {A' A B' B : subgroup G} (hA : A' ≤ A)
  [hAN : (A'.subgroup_of A).normal] (a : A') (x : A ⊓ B) (b : A' ⊔ A ⊓ B)
  (e : (a * x : G) = b.1) :
  Zassenhaus_fun_aux B' B hA b = quotient.mk' x :=
begin
  have h : (a * x : G) ∈ A' ⊔ A ⊓ B, { rw e, exact b.2 },
  convert ← Zassenhaus_fun_aux_app hA _ _ h, ext, exact e,
end

/-- bruh -/
noncomputable def Zassenhaus_fun (A' A B' B : subgroup G) [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal] :
  ↥(A' ⊔ A ⊓ B) →* Zassenhaus_quot A' A B' B :=
{ to_fun := Zassenhaus_fun_aux B' B hA.out,
  map_one' := Zassenhaus_fun_aux_app' _ 1 _ _ (by simp; refl),
  map_mul' := λ ⟨a, ha⟩ ⟨b, hb⟩,
  begin
    clear_,
    obtain ⟨a₁, a₂, rfl⟩ := (mem_sup_iff' (Zassenhaus_aux B hA.out)).1 ha,
    obtain ⟨b₁, b₂, rfl⟩ := (mem_sup_iff' (Zassenhaus_aux B hA.out)).1 hb,
    simp only [Zassenhaus_fun_aux_app],
    refine Zassenhaus_fun_aux_app' hA.out ⟨a₁ * (a₂ * b₁ * a₂⁻¹), _⟩ _ _ _,
    { rw normal_subgroup_of_iff hA.out at hAN,
      exact mul_mem A' a₁.2 (hAN ↑b₁ ↑a₂ b₁.2 (mem_inf.mp a₂.2).1) },
    simp [mul_assoc],
  end }

lemma Zassenhaus_fun_ker {A' A B' B : subgroup G} [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal] :
  (Zassenhaus_fun A' A B' B).ker = (A' ⊔ A ⊓ B').subgroup_of (A' ⊔ A ⊓ B) :=
begin
  ext ⟨x, hx⟩,
  obtain ⟨a, b, rfl⟩ := (mem_sup_iff' (Zassenhaus_aux B hA.out)).1 hx,
  change (Zassenhaus_fun A' A B' B) ⟨↑a * ↑b, hx⟩ = quotient.mk' 1 ↔ _,
  simp only [Zassenhaus_fun, monoid_hom.coe_mk, Zassenhaus_fun_aux_app' hA.out _ _ ⟨_, hx⟩ rfl,
    quotient.eq'],
  change b⁻¹ * 1 ∈ ((A' ⊓ B ⊔ A ⊓ B').subgroup_of (A ⊓ B)) ↔ _,
  simp only [mem_subgroup_of, subgroup.coe_mk, mem_inf, subgroup.coe_subtype,
    mul_one, coe_inv, inv_mem_iff],
  refine ⟨λ h, _, λ hx', _⟩,
  { letI := inf_subgroup_of_inf_normal_of_left B hA.out,
    have p := normal_subgroup_mul (inf_le_inf hA.out (le_refl B)) (inf_le_inf (le_refl A) hB.out),
    obtain ⟨x, y, hmm⟩ := (mem_sup_iff' p).mp h, rw ← hmm,
    refine (mem_sup_iff' (Zassenhaus_aux B' hA.out)).mpr ⟨a * ⟨x, _⟩, y, _⟩,
    exact mem_of_le (inf_le_left) x.2,
    simp [mul_assoc] },
  obtain ⟨x, y, h⟩ := (mem_sup_iff' (Zassenhaus_aux B' hA.out)).1 hx',
  have : (b : G) * y⁻¹ ∈ A' ⊓ B ⊔ A ⊓ B',
  { refine mem_of_le le_sup_left _,
    have := mul_mem A' (inv_mem A' a.2) x.2,
    simp only [inv_mul_eq_mul_inv h, subtype.val_eq_coe] at this,
    have bval := (mem_inf.mp y.2).2, rw subtype.val_eq_coe at bval,
    refine mem_inf.mpr ⟨this, mul_mem _ (mem_inf.mp b.2).2 (mem_of_le hB.out (inv_mem _ bval))⟩ },
  have done : (b : G) * y⁻¹ * y ∈ A' ⊓ B ⊔ A ⊓ B' := mul_mem _ this (mem_of_le le_sup_right y.2),
  rwa [inv_mul_cancel_right] at done,
end

@[instance] lemma Zassenhaus_normal
  {A' A B' B : subgroup G} [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal] :
  ((A' ⊔ A ⊓ B').subgroup_of (A' ⊔ A ⊓ B)).normal :=
by { rw ← Zassenhaus_fun_ker, exact monoid_hom.normal_ker _, }

lemma Zassenhaus_fun_surjective {A' A B' B : subgroup G} [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal] :
  function.surjective (Zassenhaus_fun A' A B' B) := λ x, x.induction_on' $
begin
  rintro ⟨y, (hy : y ∈ ↑(A ⊓ B))⟩,
  have hy' := (mem_sup_iff' (Zassenhaus_aux B hA.out)).mpr ⟨1, ⟨y, hy⟩, one_mul _⟩,
  use ⟨y, hy'⟩,
  rw [subtype.coe_mk, ← one_mul y, ← subtype.coe_mk y hy] at hy',
  conv_lhs { find y { rw ← one_mul y, rw ← subtype.coe_mk y hy, } },
  simp only [Zassenhaus_fun, monoid_hom.coe_mk],
  exact Zassenhaus_fun_aux_app hA.out 1 ⟨y, hy⟩ hy',
end

/-- bruh -/
def Zassenhaus' {A' A B' B : subgroup G} [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal] :
  Zassenhaus_quot A' A B' B ≃* Zassenhaus_quot B' B A' A :=
equiv_quotient_subgroup_of_of_eq (by { rwa [inf_comm, @inf_comm _ _ A B', sup_comm] } ) (inf_comm)

/-- bruh  -/
noncomputable def Zassenhaus''
  {A' A B' B : subgroup G} [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal] :
  quotient ((A' ⊔ A ⊓ B').subgroup_of (A' ⊔ A ⊓ B)) ≃*
    quotient ((B' ⊔ B ⊓ A').subgroup_of (B' ⊔ B ⊓ A)) :=
(((equiv_quotient_of_eq Zassenhaus_fun_ker).symm.trans
  (quotient_ker_equiv_of_surjective (Zassenhaus_fun A' A B' B)
  Zassenhaus_fun_surjective)).trans Zassenhaus').trans
  ((equiv_quotient_of_eq Zassenhaus_fun_ker).symm.trans
  (quotient_ker_equiv_of_surjective (Zassenhaus_fun B' B A' A)
  (Zassenhaus_fun_surjective))).symm

end Zassenhaus

end quotient_group
