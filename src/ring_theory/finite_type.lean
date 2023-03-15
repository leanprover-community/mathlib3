/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import group_theory.finiteness
import ring_theory.adjoin.tower
import ring_theory.finiteness
import ring_theory.noetherian

/-!
# Finiteness conditions in commutative algebra

In this file we define a notion of finiteness that is common in commutative algebra.

## Main declarations

- `algebra.finite_type`, `ring_hom.finite_type`, `alg_hom.finite_type`
  all of these express that some object is finitely generated *as algebra* over some base ring.

-/

open function (surjective)
open_locale big_operators polynomial

section module_and_algebra

variables (R A B M N : Type*)

/-- An algebra over a commutative semiring is of `finite_type` if it is finitely generated
over the base ring as algebra. -/
class algebra.finite_type [comm_semiring R] [semiring A] [algebra R A] : Prop :=
(out : (⊤ : subalgebra R A).fg)

namespace module

variables [semiring R] [add_comm_monoid M] [module R M] [add_comm_monoid N] [module R N]

namespace finite
open _root_.submodule set

variables {R M N}

section algebra

@[priority 100] -- see Note [lower instance priority]
instance finite_type {R : Type*} (A : Type*) [comm_semiring R] [semiring A]
  [algebra R A] [hRA : finite R A] : algebra.finite_type R A :=
⟨subalgebra.fg_of_submodule_fg hRA.1⟩

end algebra

end finite

end module

namespace algebra

variables [comm_ring R] [comm_ring A] [algebra R A] [comm_ring B] [algebra R B]
variables [add_comm_group M] [module R M]
variables [add_comm_group N] [module R N]

namespace finite_type

lemma self : finite_type R R := ⟨⟨{1}, subsingleton.elim _ _⟩⟩

protected lemma polynomial : finite_type R R[X] :=
⟨⟨{polynomial.X}, by { rw finset.coe_singleton, exact polynomial.adjoin_X }⟩⟩

open_locale classical

protected lemma mv_polynomial (ι : Type*) [finite ι] : finite_type R (mv_polynomial ι R) :=
by casesI nonempty_fintype ι; exact ⟨⟨finset.univ.image mv_polynomial.X,
  by {rw [finset.coe_image, finset.coe_univ, set.image_univ], exact mv_polynomial.adjoin_range_X}⟩⟩

lemma of_restrict_scalars_finite_type [algebra A B] [is_scalar_tower R A B] [hB : finite_type R B] :
  finite_type A B :=
begin
  obtain ⟨S, hS⟩ := hB.out,
  refine ⟨⟨S, eq_top_iff.2 (λ b, _)⟩⟩,
  have le : adjoin R (S : set B) ≤ subalgebra.restrict_scalars R (adjoin A S),
  { apply (algebra.adjoin_le _ : _ ≤ (subalgebra.restrict_scalars R (adjoin A ↑S))),
    simp only [subalgebra.coe_restrict_scalars],
    exact algebra.subset_adjoin, },
  exact le (eq_top_iff.1 hS b),
end

variables {R A B}

lemma of_surjective (hRA : finite_type R A) (f : A →ₐ[R] B) (hf : surjective f) :
  finite_type R B :=
⟨begin
  convert hRA.1.map f,
  simpa only [map_top f, @eq_comm _ ⊤, eq_top_iff, alg_hom.mem_range] using hf
end⟩

lemma equiv (hRA : finite_type R A) (e : A ≃ₐ[R] B) : finite_type R B :=
hRA.of_surjective e e.surjective

lemma trans [algebra A B] [is_scalar_tower R A B] (hRA : finite_type R A) (hAB : finite_type A B) :
  finite_type R B :=
⟨fg_trans' hRA.1 hAB.1⟩

/-- An algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a finset. -/
lemma iff_quotient_mv_polynomial : (finite_type R A) ↔ ∃ (s : finset A)
  (f : (mv_polynomial {x // x ∈ s} R) →ₐ[R] A), (surjective f) :=
begin
  split,
  { rintro ⟨s, hs⟩,
    use [s, mv_polynomial.aeval coe],
    intro x,
    have hrw : (↑s : set A) = (λ (x : A), x ∈ s.val) := rfl,
    rw [← set.mem_range, ← alg_hom.coe_range, ← adjoin_eq_range, ← hrw, hs],
    exact set.mem_univ x },
  { rintro ⟨s, ⟨f, hsur⟩⟩,
    exact finite_type.of_surjective (finite_type.mv_polynomial R {x // x ∈ s}) f hsur }
end

/-- An algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a fintype. -/
lemma iff_quotient_mv_polynomial' : (finite_type R A) ↔ ∃ (ι : Type u_2) (_ : fintype ι)
  (f : (mv_polynomial ι R) →ₐ[R] A), (surjective f) :=
begin
  split,
  { rw iff_quotient_mv_polynomial,
    rintro ⟨s, ⟨f, hsur⟩⟩,
    use [{x // x ∈ s}, by apply_instance, f, hsur] },
  { rintro ⟨ι, ⟨hfintype, ⟨f, hsur⟩⟩⟩,
    letI : fintype ι := hfintype,
    exact finite_type.of_surjective (finite_type.mv_polynomial R ι) f hsur }
end

/-- An algebra is finitely generated if and only if it is a quotient of a polynomial ring in `n`
variables. -/
lemma iff_quotient_mv_polynomial'' : (finite_type R A) ↔ ∃ (n : ℕ)
  (f : (mv_polynomial (fin n) R) →ₐ[R] A), (surjective f) :=
begin
  split,
  { rw iff_quotient_mv_polynomial',
    rintro ⟨ι, hfintype, ⟨f, hsur⟩⟩,
    resetI,
    have equiv := mv_polynomial.rename_equiv R (fintype.equiv_fin ι),
    exact ⟨fintype.card ι, alg_hom.comp f equiv.symm, function.surjective.comp hsur
      (alg_equiv.symm equiv).surjective⟩ },
  { rintro ⟨n, ⟨f, hsur⟩⟩,
    exact finite_type.of_surjective (finite_type.mv_polynomial R (fin n)) f hsur }
end

instance prod [hA : finite_type R A] [hB : finite_type R B] : finite_type R (A × B) :=
⟨begin
  rw ← subalgebra.prod_top,
  exact hA.1.prod hB.1
end⟩

lemma is_noetherian_ring (R S : Type*) [comm_ring R] [comm_ring S] [algebra R S]
  [h : algebra.finite_type R S] [is_noetherian_ring R] : is_noetherian_ring S :=
begin
  obtain ⟨s, hs⟩ := h.1,
  apply is_noetherian_ring_of_surjective
    (mv_polynomial s R) S (mv_polynomial.aeval coe : mv_polynomial s R →ₐ[R] S),
  rw [← set.range_iff_surjective, alg_hom.coe_to_ring_hom, ← alg_hom.coe_range,
    ← algebra.adjoin_range_eq_range_aeval, subtype.range_coe_subtype, finset.set_of_mem, hs],
  refl
end

lemma _root_.subalgebra.fg_iff_finite_type {R A : Type*} [comm_semiring R] [semiring A]
  [algebra R A] (S : subalgebra R A) : S.fg ↔ algebra.finite_type R S :=
S.fg_top.symm.trans ⟨λ h, ⟨h⟩, λ h, h.out⟩

end finite_type

end algebra

end module_and_algebra

namespace ring_hom
variables {A B C : Type*} [comm_ring A] [comm_ring B] [comm_ring C]

/-- A ring morphism `A →+* B` is of `finite_type` if `B` is finitely generated as `A`-algebra. -/
def finite_type (f : A →+* B) : Prop := @algebra.finite_type A B _ _ f.to_algebra

namespace finite

variables {A}

lemma finite_type {f : A →+* B} (hf : f.finite) : finite_type f :=
@module.finite.finite_type _ _ _ _ f.to_algebra hf

end finite

namespace finite_type

variables (A)

lemma id : finite_type (ring_hom.id A) := algebra.finite_type.self A

variables {A}

lemma comp_surjective {f : A →+* B} {g : B →+* C} (hf : f.finite_type) (hg : surjective g) :
  (g.comp f).finite_type :=
@algebra.finite_type.of_surjective A B C _ _ f.to_algebra _ (g.comp f).to_algebra hf
{ to_fun := g, commutes' := λ a, rfl, .. g } hg

lemma of_surjective (f : A →+* B) (hf : surjective f) : f.finite_type :=
by { rw ← f.comp_id, exact (id A).comp_surjective hf }

lemma comp {g : B →+* C} {f : A →+* B} (hg : g.finite_type) (hf : f.finite_type) :
  (g.comp f).finite_type :=
@algebra.finite_type.trans A B C _ _ f.to_algebra _ (g.comp f).to_algebra g.to_algebra
begin
  fconstructor,
  intros a b c,
  simp only [algebra.smul_def, ring_hom.map_mul, mul_assoc],
  refl
end
hf hg

lemma of_finite {f : A →+* B} (hf : f.finite) : f.finite_type :=
@module.finite.finite_type _ _ _ _ f.to_algebra hf

alias of_finite ← _root_.ring_hom.finite.to_finite_type

lemma of_comp_finite_type {f : A →+* B} {g : B →+* C} (h : (g.comp f).finite_type) :
  g.finite_type :=
begin
  letI := f.to_algebra,
  letI := g.to_algebra,
  letI := (g.comp f).to_algebra,
  letI : is_scalar_tower A B C := restrict_scalars.is_scalar_tower A B C,
  letI : algebra.finite_type A C := h,
  exact algebra.finite_type.of_restrict_scalars_finite_type A B C
end

end finite_type

end ring_hom

namespace alg_hom

variables {R A B C : Type*} [comm_ring R]
variables [comm_ring A] [comm_ring B] [comm_ring C]
variables [algebra R A] [algebra R B] [algebra R C]

/-- An algebra morphism `A →ₐ[R] B` is of `finite_type` if it is of finite type as ring morphism.
In other words, if `B` is finitely generated as `A`-algebra. -/
def finite_type (f : A →ₐ[R] B) : Prop := f.to_ring_hom.finite_type

namespace finite

variables {R A}

lemma finite_type {f : A →ₐ[R] B} (hf : f.finite) : finite_type f :=
ring_hom.finite.finite_type hf

end finite

namespace finite_type

variables (R A)

lemma id : finite_type (alg_hom.id R A) := ring_hom.finite_type.id A

variables {R A}

lemma comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.finite_type) (hf : f.finite_type) :
  (g.comp f).finite_type :=
ring_hom.finite_type.comp hg hf

lemma comp_surjective {f : A →ₐ[R] B} {g : B →ₐ[R] C} (hf : f.finite_type) (hg : surjective g) :
  (g.comp f).finite_type :=
ring_hom.finite_type.comp_surjective hf hg

lemma of_surjective (f : A →ₐ[R] B) (hf : surjective f) : f.finite_type :=
ring_hom.finite_type.of_surjective f hf

lemma of_comp_finite_type {f : A →ₐ[R] B} {g : B →ₐ[R] C} (h : (g.comp f).finite_type) :
g.finite_type :=
ring_hom.finite_type.of_comp_finite_type h

end finite_type

end alg_hom

section monoid_algebra

variables {R : Type*} {M : Type*}

namespace add_monoid_algebra

open algebra add_submonoid submodule

section span

section semiring

variables [comm_semiring R] [add_monoid M]

/-- An element of `add_monoid_algebra R M` is in the subalgebra generated by its support. -/
lemma mem_adjoin_support (f : add_monoid_algebra R M) : f ∈ adjoin R (of' R M '' f.support) :=
begin
  suffices : span R (of' R M '' f.support) ≤ (adjoin R (of' R M '' f.support)).to_submodule,
  { exact this (mem_span_support f) },
  rw submodule.span_le,
  exact subset_adjoin
end

/-- If a set `S` generates, as algebra, `add_monoid_algebra R M`, then the set of supports of
elements of `S` generates `add_monoid_algebra R M`. -/
lemma support_gen_of_gen {S : set (add_monoid_algebra R M)} (hS : algebra.adjoin R S = ⊤) :
  algebra.adjoin R (⋃ f ∈ S, (of' R M '' (f.support : set M))) = ⊤ :=
begin
  refine le_antisymm le_top _,
  rw [← hS, adjoin_le_iff],
  intros f hf,
  have hincl : of' R M '' f.support ⊆
    ⋃ (g : add_monoid_algebra R M) (H : g ∈ S), of' R M '' g.support,
  { intros s hs,
    exact set.mem_Union₂.2 ⟨f, ⟨hf, hs⟩⟩ },
  exact adjoin_mono hincl (mem_adjoin_support f)
end

/-- If a set `S` generates, as algebra, `add_monoid_algebra R M`, then the image of the union of
the supports of elements of `S` generates `add_monoid_algebra R M`. -/
lemma support_gen_of_gen' {S : set (add_monoid_algebra R M)} (hS : algebra.adjoin R S = ⊤) :
  algebra.adjoin R (of' R M '' (⋃ f ∈ S, (f.support : set M))) = ⊤ :=
begin
  suffices : of' R M '' (⋃ f ∈ S, (f.support : set M)) = ⋃ f ∈ S, (of' R M '' (f.support : set M)),
  { rw this,
    exact support_gen_of_gen hS },
  simp only [set.image_Union]
end

end semiring

section ring

variables [comm_ring R] [add_comm_monoid M]

/-- If `add_monoid_algebra R M` is of finite type, there there is a `G : finset M` such that its
image generates, as algera, `add_monoid_algebra R M`. -/
lemma exists_finset_adjoin_eq_top [h : finite_type R (add_monoid_algebra R M)] :
  ∃ G : finset M, algebra.adjoin R (of' R M '' G) = ⊤ :=
begin
  unfreezingI { obtain ⟨S, hS⟩ := h },
  letI : decidable_eq M := classical.dec_eq M,
  use finset.bUnion S (λ f, f.support),
  have : (finset.bUnion S (λ f, f.support) : set M) = ⋃ f ∈ S, (f.support : set M),
  { simp only [finset.set_bUnion_coe, finset.coe_bUnion] },
  rw [this],
  exact support_gen_of_gen' hS
end

/-- The image of an element `m : M` in `add_monoid_algebra R M` belongs the submodule generated by
`S : set M` if and only if `m ∈ S`. -/
lemma of'_mem_span [nontrivial R] {m : M} {S : set M} :
  of' R M m ∈ span R (of' R M '' S) ↔ m ∈ S :=
begin
  refine ⟨λ h, _, λ h, submodule.subset_span $ set.mem_image_of_mem (of R M) h⟩,
  rw [of', ← finsupp.supported_eq_span_single, finsupp.mem_supported,
    finsupp.support_single_ne_zero _ (one_ne_zero' R)] at h,
  simpa using h
end

/--If the image of an element `m : M` in `add_monoid_algebra R M` belongs the submodule generated by
the closure of some `S : set M` then `m ∈ closure S`. -/
lemma mem_closure_of_mem_span_closure [nontrivial R] {m : M} {S : set M}
  (h : of' R M m ∈ span R (submonoid.closure (of' R M '' S) : set (add_monoid_algebra R M))) :
  m ∈ closure S :=
begin
  suffices : multiplicative.of_add m ∈ submonoid.closure (multiplicative.to_add ⁻¹' S),
  { simpa [← to_submonoid_closure] },
  let S' := @submonoid.closure M multiplicative.mul_one_class S,
  have h' : submonoid.map (of R M) S' = submonoid.closure ((λ (x : M), (of R M) x) '' S) :=
    monoid_hom.map_mclosure _ _,
  rw [set.image_congr' (show ∀ x, of' R M x = of R M x, from λ x, of'_eq_of x), ← h'] at h,
  simpa using of'_mem_span.1 h
end

end ring

end span

variables [add_comm_monoid M]

/-- If a set `S` generates an additive monoid `M`, then the image of `M` generates, as algebra,
`add_monoid_algebra R M`. -/
lemma mv_polynomial_aeval_of_surjective_of_closure [comm_semiring R] {S : set M}
  (hS : closure S = ⊤) : function.surjective (mv_polynomial.aeval
  (λ (s : S), of' R M ↑s) : mv_polynomial S R → add_monoid_algebra R M) :=
begin
  refine λ f, induction_on f (λ m, _) _ _,
  { have : m ∈ closure S := hS.symm ▸ mem_top _,
    refine closure_induction this (λ m hm, _) _ _,
    { exact ⟨mv_polynomial.X ⟨m, hm⟩, mv_polynomial.aeval_X _ _⟩ },
    { exact ⟨1, alg_hom.map_one _⟩ },
    { rintro m₁ m₂ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩,
      exact ⟨P₁ * P₂, by rw [alg_hom.map_mul, hP₁, hP₂, of_apply, of_apply, of_apply,
        single_mul_single, one_mul]; refl⟩ } },
  { rintro f g ⟨P, rfl⟩ ⟨Q, rfl⟩,
    exact ⟨P + Q, alg_hom.map_add _ _ _⟩ },
  { rintro r f ⟨P, rfl⟩,
    exact ⟨r • P, alg_hom.map_smul _ _ _⟩ }
end

variables (R M)

/-- If an additive monoid `M` is finitely generated then `add_monoid_algebra R M` is of finite
type. -/
instance finite_type_of_fg [comm_ring R] [h : add_monoid.fg M] :
  finite_type R (add_monoid_algebra R M) :=
begin
  obtain ⟨S, hS⟩ := h.out,
  exact (finite_type.mv_polynomial R (S : set M)).of_surjective (mv_polynomial.aeval
    (λ (s : (S : set M)), of' R M ↑s)) (mv_polynomial_aeval_of_surjective_of_closure hS)
end

variables {R M}

/-- An additive monoid `M` is finitely generated if and only if `add_monoid_algebra R M` is of
finite type. -/
lemma finite_type_iff_fg [comm_ring R] [nontrivial R] :
  finite_type R (add_monoid_algebra R M) ↔ add_monoid.fg M :=
begin
  refine ⟨λ h, _, λ h, @add_monoid_algebra.finite_type_of_fg _ _ _ _ h⟩,
  obtain ⟨S, hS⟩ := @exists_finset_adjoin_eq_top R M _ _ h,
  refine add_monoid.fg_def.2 ⟨S, (eq_top_iff' _).2 (λ m, _)⟩,
  have hm : of' R M m ∈ (adjoin R (of' R M '' ↑S)).to_submodule,
  { simp only [hS, top_to_submodule, submodule.mem_top], },
  rw [adjoin_eq_span] at hm,
  exact mem_closure_of_mem_span_closure hm
end

/-- If `add_monoid_algebra R M` is of finite type then `M` is finitely generated. -/
lemma fg_of_finite_type [comm_ring R] [nontrivial R] [h : finite_type R (add_monoid_algebra R M)] :
  add_monoid.fg M :=
finite_type_iff_fg.1 h

/-- An additive group `G` is finitely generated if and only if `add_monoid_algebra R G` is of
finite type. -/
lemma finite_type_iff_group_fg {G : Type*} [add_comm_group G] [comm_ring R] [nontrivial R] :
  finite_type R (add_monoid_algebra R G) ↔ add_group.fg G :=
by simpa [add_group.fg_iff_add_monoid.fg] using finite_type_iff_fg

end add_monoid_algebra

namespace monoid_algebra

open algebra submonoid submodule

section span

section semiring

variables [comm_semiring R] [monoid M]

/-- An element of `monoid_algebra R M` is in the subalgebra generated by its support. -/
lemma mem_adjoin_support (f : monoid_algebra R M) : f ∈ adjoin R (of R M '' f.support) :=
begin
  suffices : span R (of R M '' f.support) ≤ (adjoin R (of R M '' f.support)).to_submodule,
  { exact this (mem_span_support f) },
  rw submodule.span_le,
  exact subset_adjoin
end

/-- If a set `S` generates, as algebra, `monoid_algebra R M`, then the set of supports of elements
of `S` generates `monoid_algebra R M`. -/
lemma support_gen_of_gen {S : set (monoid_algebra R M)} (hS : algebra.adjoin R S = ⊤) :
  algebra.adjoin R (⋃ f ∈ S, (of R M '' (f.support : set M))) = ⊤ :=
begin
  refine le_antisymm le_top _,
  rw [← hS, adjoin_le_iff],
  intros f hf,
  have hincl : (of R M) '' f.support ⊆
    ⋃ (g : monoid_algebra R M) (H : g ∈ S), of R M '' g.support,
  { intros s hs,
    exact set.mem_Union₂.2 ⟨f, ⟨hf, hs⟩⟩ },
  exact adjoin_mono hincl (mem_adjoin_support f)
end

/-- If a set `S` generates, as algebra, `monoid_algebra R M`, then the image of the union of the
supports of elements of `S` generates `monoid_algebra R M`. -/
lemma support_gen_of_gen' {S : set (monoid_algebra R M)} (hS : algebra.adjoin R S = ⊤) :
  algebra.adjoin R (of R M '' (⋃ f ∈ S, (f.support : set M))) = ⊤ :=
begin
  suffices : of R M '' (⋃ f ∈ S, (f.support : set M)) = ⋃ f ∈ S, (of R M '' (f.support : set M)),
  { rw this,
    exact support_gen_of_gen hS },
  simp only [set.image_Union]
end

end semiring

section ring

variables [comm_ring R] [comm_monoid M]

/-- If `monoid_algebra R M` is of finite type, there there is a `G : finset M` such that its image
generates, as algera, `monoid_algebra R M`. -/
lemma exists_finset_adjoin_eq_top [h :finite_type R (monoid_algebra R M)] :
  ∃ G : finset M, algebra.adjoin R (of R M '' G) = ⊤ :=
begin
  unfreezingI { obtain ⟨S, hS⟩ := h },
  letI : decidable_eq M := classical.dec_eq M,
  use finset.bUnion S (λ f, f.support),
  have : (finset.bUnion S (λ f, f.support) : set M) = ⋃ f ∈ S, (f.support : set M),
  { simp only [finset.set_bUnion_coe, finset.coe_bUnion] },
  rw [this],
  exact support_gen_of_gen' hS
end

/-- The image of an element `m : M` in `monoid_algebra R M` belongs the submodule generated by
`S : set M` if and only if `m ∈ S`. -/
lemma of_mem_span_of_iff [nontrivial R] {m : M} {S : set M} :
  of R M m ∈ span R (of R M '' S) ↔ m ∈ S :=
begin
  refine ⟨λ h, _, λ h, submodule.subset_span $ set.mem_image_of_mem (of R M) h⟩,
  rw [of, monoid_hom.coe_mk, ← finsupp.supported_eq_span_single, finsupp.mem_supported,
    finsupp.support_single_ne_zero _ (one_ne_zero' R)] at h,
  simpa using h
end

/--If the image of an element `m : M` in `monoid_algebra R M` belongs the submodule generated by the
closure of some `S : set M` then `m ∈ closure S`. -/
lemma mem_closure_of_mem_span_closure [nontrivial R] {m : M} {S : set M}
  (h : of R M m ∈ span R (submonoid.closure (of R M '' S) : set (monoid_algebra R M))) :
  m ∈ closure S :=
begin
  rw ← monoid_hom.map_mclosure at h,
  simpa using of_mem_span_of_iff.1 h
end

end ring

end span

variables [comm_monoid M]

/-- If a set `S` generates a monoid `M`, then the image of `M` generates, as algebra,
`monoid_algebra R M`. -/
lemma mv_polynomial_aeval_of_surjective_of_closure [comm_semiring R] {S : set M}
  (hS : closure S = ⊤) : function.surjective (mv_polynomial.aeval
  (λ (s : S), of R M ↑s) : mv_polynomial S R → monoid_algebra R M) :=
begin
  refine λ f, induction_on f (λ m, _) _ _,
  { have : m ∈ closure S := hS.symm ▸ mem_top _,
    refine closure_induction this (λ m hm, _) _ _,
    { exact ⟨mv_polynomial.X ⟨m, hm⟩, mv_polynomial.aeval_X _ _⟩ },
    { exact ⟨1, alg_hom.map_one _⟩ },
    { rintro m₁ m₂ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩,
      exact ⟨P₁ * P₂, by rw [alg_hom.map_mul, hP₁, hP₂, of_apply, of_apply, of_apply,
        single_mul_single, one_mul]⟩ } },
  { rintro f g ⟨P, rfl⟩ ⟨Q, rfl⟩,
    exact ⟨P + Q, alg_hom.map_add _ _ _⟩ },
  { rintro r f ⟨P, rfl⟩,
    exact ⟨r • P, alg_hom.map_smul _ _ _⟩ }
end

/-- If a monoid `M` is finitely generated then `monoid_algebra R M` is of finite type. -/
instance finite_type_of_fg [comm_ring R] [monoid.fg M] : finite_type R (monoid_algebra R M) :=
(add_monoid_algebra.finite_type_of_fg R (additive M)).equiv (to_additive_alg_equiv R M).symm

/-- A monoid `M` is finitely generated if and only if `monoid_algebra R M` is of finite type. -/
lemma finite_type_iff_fg [comm_ring R] [nontrivial R] :
  finite_type R (monoid_algebra R M) ↔ monoid.fg M :=
⟨λ h, monoid.fg_iff_add_fg.2 $ add_monoid_algebra.finite_type_iff_fg.1 $ h.equiv $
  to_additive_alg_equiv R M, λ h, @monoid_algebra.finite_type_of_fg _ _ _ _ h⟩

/-- If `monoid_algebra R M` is of finite type then `M` is finitely generated. -/
lemma fg_of_finite_type [comm_ring R] [nontrivial R] [h : finite_type R (monoid_algebra R M)] :
  monoid.fg M :=
finite_type_iff_fg.1 h

/-- A group `G` is finitely generated if and only if `add_monoid_algebra R G` is of finite type. -/
lemma finite_type_iff_group_fg {G : Type*} [comm_group G] [comm_ring R] [nontrivial R] :
  finite_type R (monoid_algebra R G) ↔ group.fg G :=
by simpa [group.fg_iff_monoid.fg] using finite_type_iff_fg

end monoid_algebra

end monoid_algebra

section vasconcelos
variables {R : Type*} [comm_ring R] {M : Type*} [add_comm_group M] [module R M] (f : M →ₗ[R] M)

noncomputable theory

/-- The structure of a module `M` over a ring `R` as a module over `R[X]` when given a
choice of how `X` acts by choosing a linear map `f : M →ₗ[R] M` -/
def module_polynomial_of_endo : module R[X] M :=
module.comp_hom M (polynomial.aeval f).to_ring_hom

lemma module_polynomial_of_endo_smul_def (n : R[X]) (a : M) :
  @@has_smul.smul (module_polynomial_of_endo f).to_has_smul n a = polynomial.aeval f n a := rfl

local attribute [simp] module_polynomial_of_endo_smul_def

include f
lemma module_polynomial_of_endo.is_scalar_tower : @is_scalar_tower R R[X] M _
  (by { letI := module_polynomial_of_endo f, apply_instance }) _ :=
begin
  letI := module_polynomial_of_endo f,
  constructor,
  intros x y z,
  simp,
end

open polynomial module

/-- A theorem/proof by Vasconcelos, given a finite module `M` over a commutative ring, any
surjective endomorphism of `M` is also injective. Based on,
https://math.stackexchange.com/a/239419/31917,
https://www.ams.org/journals/tran/1969-138-00/S0002-9947-1969-0238839-5/.
This is similar to `is_noetherian.injective_of_surjective_endomorphism` but only applies in the
commutative case, but does not use a Noetherian hypothesis. -/
theorem module.finite.injective_of_surjective_endomorphism [hfg : finite R M]
  (f_surj : function.surjective f) : function.injective f :=
begin
  letI := module_polynomial_of_endo f,
  haveI : is_scalar_tower R R[X] M := module_polynomial_of_endo.is_scalar_tower f,
  have hfgpoly : finite R[X] M, from finite.of_restrict_scalars_finite R _ _,
  have X_mul : ∀ o, (X : R[X]) • o = f o,
  { intro,
    simp, },
  have : (⊤ : submodule R[X] M) ≤ ideal.span {X} • ⊤,
  { intros a ha,
    obtain ⟨y, rfl⟩ := f_surj a,
    rw [← X_mul y],
    exact submodule.smul_mem_smul (ideal.mem_span_singleton.mpr (dvd_refl _)) trivial, },
  obtain ⟨F, hFa, hFb⟩ := submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul _
    (⊤ : submodule R[X] M) (finite_def.mp hfgpoly) this,
  rw [← linear_map.ker_eq_bot, linear_map.ker_eq_bot'],
  intros m hm,
  rw ideal.mem_span_singleton' at hFa,
  obtain ⟨G, hG⟩ := hFa,
  suffices : (F - 1) • m = 0,
  { have Fmzero := hFb m (by simp),
    rwa [← sub_add_cancel F 1, add_smul, one_smul, this, zero_add] at Fmzero, },
  rw [← hG, mul_smul, X_mul m, hm, smul_zero],
end

end vasconcelos
