/-
Copyright (c) 2020 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.limits.shapes.pullbacks
import ring_theory.tensor_product
import algebra.category.CommRing.limits
import algebra.category.CommRing.colimits
import category_theory.limits.shapes.strict_initial

/-!
# Constructions of (co)limit in CommRing

In this file we prove that tensor product is indeed the fibered coproduct in `CommRing`, and
provide the explicit pushout cocone.

-/

universe u

open category_theory category_theory.limits
open_locale tensor_product

variables {R A B : CommRing.{u}} (f : R ⟶ A) (g : R ⟶ B)

namespace CommRing

section pushout

/-- The explicit cocone with tensor products as the fibered product in `CommRing`. -/
def pushout_cocone : limits.pushout_cocone f g :=
begin
  letI := ring_hom.to_algebra f,
  letI := ring_hom.to_algebra g,
  apply limits.pushout_cocone.mk,
  show CommRing, from CommRing.of (A ⊗[R] B),
  show A ⟶ _,  from algebra.tensor_product.include_left.to_ring_hom,
  show B ⟶ _,  from algebra.tensor_product.include_right.to_ring_hom,
  ext r,
  transitivity algebra_map R (A ⊗[R] B) r,
  exact algebra.tensor_product.include_left.commutes r,
  exact (algebra.tensor_product.include_right.commutes r).symm,
end

@[simp]
lemma pushout_cocone_inl : (pushout_cocone f g).inl = (by
{ letI := f.to_algebra, letI := g.to_algebra,
  exactI algebra.tensor_product.include_left.to_ring_hom }) := rfl

@[simp]
lemma pushout_cocone_inr : (pushout_cocone f g).inr = (by
{ letI := f.to_algebra, letI := g.to_algebra,
  exactI algebra.tensor_product.include_right.to_ring_hom }) := rfl

@[simp]
lemma pushout_cocone_X : (pushout_cocone f g).X = (by
{ letI := f.to_algebra, letI := g.to_algebra,
  exactI CommRing.of (A ⊗[R] B) }) := rfl

/-- Verify that the `pushout_cocone` is indeed the colimit. -/
def pushout_cocone_is_colimit : limits.is_colimit (pushout_cocone f g) :=
limits.pushout_cocone.is_colimit_aux' _ (λ s,
begin
  letI := ring_hom.to_algebra f,
  letI := ring_hom.to_algebra g,
  letI := ring_hom.to_algebra (f ≫ s.inl),
  let f' : A →ₐ[R] s.X := { commutes' := λ r, by
      { change s.inl.to_fun (f r) = (f ≫ s.inl) r, refl }, ..s.inl },
  let g' : B →ₐ[R] s.X := { commutes' := λ r, by
      { change (g ≫ s.inr) r = (f ≫ s.inl) r,
        congr' 1,
        exact (s.ι.naturality limits.walking_span.hom.snd).trans
          (s.ι.naturality limits.walking_span.hom.fst).symm }, ..s.inr },
  /- The factor map is a ⊗ b ↦ f(a) * g(b). -/
  use alg_hom.to_ring_hom (algebra.tensor_product.product_map f' g'),
  simp only [pushout_cocone_inl, pushout_cocone_inr],
  split, { ext x, exact algebra.tensor_product.product_map_left_apply  _ _ x, },
  split, { ext x, exact algebra.tensor_product.product_map_right_apply _ _ x, },
  intros h eq1 eq2,
  let h' : (A ⊗[R] B) →ₐ[R] s.X :=
    { commutes' := λ r, by
    { change h ((f r) ⊗ₜ[R] 1) = s.inl (f r),
      rw ← eq1, simp }, ..h },
  suffices : h' = algebra.tensor_product.product_map f' g',
  { ext x,
    change h' x = algebra.tensor_product.product_map f' g' x,
    rw this },
  apply algebra.tensor_product.ext,
  intros a b,
  simp [← eq1, ← eq2, ← h.map_mul],
end)

end pushout

lemma punit_is_terminal : is_terminal (CommRing.of punit) :=
begin
  apply_with is_terminal.of_unique { instances := ff },
  tidy
end

instance CommRing_has_strict_terminal_objects : has_strict_terminal_objects CommRing.{u} :=
begin
  apply has_strict_terminal_objects_of_terminal_is_strict (CommRing.of punit),
  intros X f,
  refine ⟨⟨by tidy, by ext, _⟩⟩,
  ext,
  have e : (0 : X) = 1 := by { rw [← f.map_one, ← f.map_zero], congr },
  replace e : 0 * x = 1 * x := congr_arg (λ a, a * x) e,
  rw [one_mul, zero_mul, ← f.map_zero] at e,
  exact e,
end

lemma Z_is_terminal : is_initial (CommRing.of ℤ) :=
begin
  apply_with is_initial.of_unique { instances := ff },
  exact λ R, ⟨⟨int.cast_ring_hom R⟩, λ a, a.ext_int _⟩,
end

end CommRing
