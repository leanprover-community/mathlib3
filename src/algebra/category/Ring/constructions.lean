/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.limits.shapes.pullbacks
import ring_theory.tensor_product
import algebra.category.Ring.limits
import algebra.category.Ring.colimits
import category_theory.limits.shapes.strict_initial
import ring_theory.subring.basic
import ring_theory.ideal.local_ring
import category_theory.limits.preserves.limits

/-!
# Constructions of (co)limits in CommRing

In this file we provide the explicit (co)cones for various (co)limits in `CommRing`, including
* tensor product is the pushout
* `Z` is the initial object
* `0` is the strict terminal object
* cartesian product is the product
* `ring_hom.eq_locus` is the equalizer

-/

universes u u'

open category_theory category_theory.limits
open_locale tensor_product

namespace CommRing

section pushout

variables {R A B : CommRing.{u}} (f : R ⟶ A) (g : R ⟶ B)

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
  { exact algebra.tensor_product.include_left.commutes r },
  { exact (algebra.tensor_product.include_right.commutes r).symm }
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

section terminal

/-- The trivial ring is the (strict) terminal object of `CommRing`. -/
def punit_is_terminal : is_terminal (CommRing.of.{u} punit) :=
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

lemma subsingleton_of_is_terminal {X : CommRing} (hX : is_terminal X) : subsingleton X :=
(hX.unique_up_to_iso punit_is_terminal).CommRing_iso_to_ring_equiv.to_equiv
  .subsingleton_congr.mpr (show subsingleton punit, by apply_instance)

/-- `ℤ` is the initial object of `CommRing`. -/
def Z_is_initial : is_initial (CommRing.of ℤ) :=
begin
  apply_with is_initial.of_unique { instances := ff },
  exact λ R, ⟨⟨int.cast_ring_hom R⟩, λ a, a.ext_int _⟩,
end

end terminal

section product

variables (A B : CommRing.{u})

/-- The product in `CommRing` is the cartesian product. This is the binary fan. -/
@[simps X]
def prod_fan : binary_fan A B :=
binary_fan.mk (CommRing.of_hom $ ring_hom.fst A B) (CommRing.of_hom $ ring_hom.snd A B)

/-- The product in `CommRing` is the cartesian product. -/
def prod_fan_is_limit : is_limit (prod_fan A B) :=
{ lift := λ c, ring_hom.prod (c.π.app walking_pair.left) (c.π.app walking_pair.right),
  fac' := λ c j, by { ext, cases j;
    simpa only [binary_fan.π_app_left, binary_fan.π_app_right, comp_apply, ring_hom.prod_apply] },
  uniq' := λ s m h, by { ext, { simpa using congr_hom (h walking_pair.left) x },
    { simpa using congr_hom (h walking_pair.right) x } } }

end product

section equalizer

variables {A B : CommRing.{u}} (f g : A ⟶ B)

/-- The equalizer in `CommRing` is the equalizer as sets. This is the equalizer fork. -/
def equalizer_fork : fork f g :=
fork.of_ι (CommRing.of_hom (ring_hom.eq_locus f g).subtype) (by { ext ⟨x, e⟩, simpa using e })

/-- The equalizer in `CommRing` is the equalizer as sets. -/
def equalizer_fork_is_limit : is_limit (equalizer_fork f g) :=
begin
  fapply fork.is_limit.mk',
  intro s,
  use s.ι.cod_restrict' _ (λ x, (concrete_category.congr_hom s.condition x : _)),
  split,
  { ext, refl },
  { intros m hm, ext x, exact concrete_category.congr_hom hm x }
end

instance : is_local_ring_hom (equalizer_fork f g).ι :=
begin
  constructor,
  rintros ⟨a, (h₁ : _ = _)⟩ (⟨⟨x,y,h₃,h₄⟩,(rfl : x = _)⟩ : is_unit a),
  have : y ∈ ring_hom.eq_locus f g,
  { apply (f.is_unit_map ⟨⟨x,y,h₃,h₄⟩,rfl⟩ : is_unit (f x)).mul_left_inj.mp,
    conv_rhs { rw h₁ },
    rw [← f.map_mul, ← g.map_mul, h₄, f.map_one, g.map_one] },
  rw is_unit_iff_exists_inv,
  exact ⟨⟨y, this⟩, subtype.eq h₃⟩,
end

instance equalizer_ι_is_local_ring_hom (F : walking_parallel_pair.{u} ⥤ CommRing.{u}) :
  is_local_ring_hom (limit.π F walking_parallel_pair.zero) :=
begin
  have := lim_map_π (diagram_iso_parallel_pair F).hom walking_parallel_pair.zero,
  rw ← is_iso.comp_inv_eq at this,
  rw ← this,
  rw ← limit.iso_limit_cone_hom_π ⟨_, equalizer_fork_is_limit
    (F.map walking_parallel_pair_hom.left) (F.map walking_parallel_pair_hom.right)⟩
    walking_parallel_pair.zero,
  change is_local_ring_hom ((lim.map _ ≫ _ ≫ (equalizer_fork _ _).ι) ≫ _),
  apply_instance
end

open category_theory.limits.walking_parallel_pair opposite
open category_theory.limits.walking_parallel_pair_hom

instance equalizer_ι_is_local_ring_hom' (F : walking_parallel_pair.{u}ᵒᵖ ⥤ CommRing.{u}) :
  is_local_ring_hom (limit.π F (opposite.op walking_parallel_pair.one)) :=
begin
  have : _ = limit.π F (walking_parallel_pair_op_equiv.{u u}.functor.obj _) :=
    (limit.iso_limit_cone_inv_π ⟨_, is_limit.whisker_equivalence (limit.is_limit F)
      walking_parallel_pair_op_equiv⟩ walking_parallel_pair.zero : _),
  erw ← this,
  apply_instance
end

end equalizer

end CommRing
