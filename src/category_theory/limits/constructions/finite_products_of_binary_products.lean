/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.shapes.finite_products
import category_theory.limits.shapes.binary_products
import category_theory.limits.preserves.shapes.products
import category_theory.limits.preserves.shapes.binary_products
import category_theory.limits.shapes.pullbacks
import category_theory.pempty
import data.equiv.fin

/-!
# Constructing finite products from binary products and terminal.

If a category has binary products and a terminal object then it has finite products.
If a functor preserves binary products and the terminal object then it preserves finite products.

# TODO

Provide the dual results.
Show the analogous results for functors which reflect or create (co)limits.
-/

universes v u u'

noncomputable theory
open category_theory category_theory.category category_theory.limits
namespace category_theory

variables {J : Type v} [small_category J]
variables {C : Type u} [category.{v} C]
variables {D : Type u'} [category.{v} D]

/--
Given `n+1` objects of `C`, a fan for the last `n` with point `c₁.X` and a binary fan on `c₁.X` and
`f 0`, we can build a fan for all `n+1`.

In `extend_fan_is_limit` we show that if the two given fans are limits, then this fan is also a
limit.
-/
@[simps {rhs_md := semireducible}]
def extend_fan {n : ℕ} {f : ulift (fin (n+1)) → C}
  (c₁ : fan (λ (i : ulift (fin n)), f ⟨i.down.succ⟩))
  (c₂ : binary_fan (f ⟨0⟩) c₁.X) :
  fan f :=
fan.mk c₂.X
begin
  rintro ⟨i⟩,
  revert i,
  refine fin.cases _ _,
  { apply c₂.fst },
  { intro i,
    apply c₂.snd ≫ c₁.π.app (ulift.up i) },
end

/--
Show that if the two given fans in `extend_fan` are limits, then the constructed fan is also a
limit.
-/
def extend_fan_is_limit {n : ℕ} (f : ulift (fin (n+1)) → C)
  {c₁ : fan (λ (i : ulift (fin n)), f ⟨i.down.succ⟩)} {c₂ : binary_fan (f ⟨0⟩) c₁.X}
  (t₁ : is_limit c₁) (t₂ : is_limit c₂) :
  is_limit (extend_fan c₁ c₂) :=
{ lift := λ s,
  begin
    apply (binary_fan.is_limit.lift' t₂ (s.π.app ⟨0⟩) _).1,
    apply t₁.lift ⟨_, discrete.nat_trans (λ i, s.π.app ⟨i.down.succ⟩)⟩
  end,
  fac' := λ s,
  begin
    rintro ⟨j⟩,
    apply fin.induction_on j,
    { apply (binary_fan.is_limit.lift' t₂ _ _).2.1 },
    { rintro i -,
      dsimp only [extend_fan_π_app],
      rw [fin.cases_succ, ← assoc, (binary_fan.is_limit.lift' t₂ _ _).2.2, t₁.fac],
      refl }
  end,
  uniq' := λ s m w,
  begin
    apply binary_fan.is_limit.hom_ext t₂,
    { rw (binary_fan.is_limit.lift' t₂ _ _).2.1,
      apply w ⟨0⟩ },
    { rw (binary_fan.is_limit.lift' t₂ _ _).2.2,
      apply t₁.uniq ⟨_, _⟩,
      rintro ⟨j⟩,
      rw assoc,
      dsimp only [discrete.nat_trans_app],
      rw ← w ⟨j.succ⟩,
      dsimp only [extend_fan_π_app],
      rw fin.cases_succ }
  end }

section
variables [has_binary_products.{v} C] [has_terminal C]

/--
If `C` has a terminal object and binary products, then it has a product for objects indexed by
`ulift (fin n)`.
This is a helper lemma for `has_finite_products_of_has_binary_and_terminal`, which is more general
than this.
-/
private lemma has_product_ulift_fin :
  Π (n : ℕ) (f : ulift (fin n) → C), has_product f
| 0 := λ f,
  begin
    letI : has_limits_of_shape (discrete (ulift (fin 0))) C :=
      has_limits_of_shape_of_equivalence
        (discrete.equivalence (equiv.ulift.trans fin_zero_equiv').symm),
    apply_instance,
  end
| (n+1) := λ f,
  begin
    haveI := has_product_ulift_fin n,
    apply has_limit.mk ⟨_, extend_fan_is_limit f (limit.is_limit _) (limit.is_limit _)⟩,
  end

/--
If `C` has a terminal object and binary products, then it has limits of shape
`discrete (ulift (fin n))` for any `n : ℕ`.
This is a helper lemma for `has_finite_products_of_has_binary_and_terminal`, which is more general
than this.
-/
private lemma has_limits_of_shape_ulift_fin (n : ℕ) :
  has_limits_of_shape (discrete (ulift (fin n))) C :=
{ has_limit := λ K,
begin
  letI := has_product_ulift_fin n K.obj,
  let : discrete.functor K.obj ≅ K := discrete.nat_iso (λ i, iso.refl _),
  apply has_limit_of_iso this,
end }

/-- If `C` has a terminal object and binary products, then it has finite products. -/
lemma has_finite_products_of_has_binary_and_terminal : has_finite_products C :=
⟨λ J 𝒥₁ 𝒥₂, begin
  resetI,
  let e := fintype.equiv_fin J,
  apply has_limits_of_shape_of_equivalence (discrete.equivalence (e.trans equiv.ulift.symm)).symm,
  refine has_limits_of_shape_ulift_fin (fintype.card J),
end⟩

end

section preserves
variables (F : C ⥤ D)
variables [preserves_limits_of_shape (discrete walking_pair) F]
variables [preserves_limits_of_shape (discrete pempty) F]
variables [has_finite_products.{v} C]

/--
If `F` preserves the terminal object and binary products, then it preserves products indexed by
`ulift (fin n)` for any `n`.
-/
noncomputable def preserves_fin_of_preserves_binary_and_terminal  :
  Π (n : ℕ) (f : ulift (fin n) → C), preserves_limit (discrete.functor f) F
| 0 := λ f,
  begin
    letI : preserves_limits_of_shape (discrete (ulift (fin 0))) F :=
      preserves_limits_of_shape_of_equiv
        (discrete.equivalence (equiv.ulift.trans fin_zero_equiv').symm) _,
    apply_instance,
  end
| (n+1) :=
  begin
    haveI := preserves_fin_of_preserves_binary_and_terminal n,
    intro f,
    refine preserves_limit_of_preserves_limit_cone
      (extend_fan_is_limit f (limit.is_limit _) (limit.is_limit _)) _,
    apply (is_limit_map_cone_fan_mk_equiv _ _ _).symm _,
    let := extend_fan_is_limit (λ i, F.obj (f i))
              (is_limit_of_has_product_of_preserves_limit F _)
              (is_limit_of_has_binary_product_of_preserves_limit F _ _),
    refine is_limit.of_iso_limit this _,
    apply cones.ext _ _,
    apply iso.refl _,
    rintro ⟨j⟩,
    apply fin.induction_on j,
    { apply (category.id_comp _).symm },
    { rintro i -,
      dsimp only [extend_fan_π_app, iso.refl_hom, fan.mk_π_app],
      rw [fin.cases_succ, fin.cases_succ],
      change F.map _ ≫ _ = 𝟙 _ ≫ _,
      rw [id_comp, ←F.map_comp],
      refl }
  end

/--
If `F` preserves the terminal object and binary products, then it preserves limits of shape
`discrete (ulift (fin n))`.
-/
def preserves_ulift_fin_of_preserves_binary_and_terminal (n : ℕ) :
  preserves_limits_of_shape (discrete (ulift (fin n))) F :=
{ preserves_limit := λ K,
  begin
    let : discrete.functor K.obj ≅ K := discrete.nat_iso (λ i, iso.refl _),
    haveI := preserves_fin_of_preserves_binary_and_terminal F n K.obj,
    apply preserves_limit_of_iso_diagram F this,
  end }

/-- If `F` preserves the terminal object and binary products then it preserves finite products. -/
def preserves_finite_products_of_preserves_binary_and_terminal
  (J : Type v) [fintype J] :
  preserves_limits_of_shape.{v} (discrete J) F :=
begin
  classical,
  let e := fintype.equiv_fin J,
  haveI := preserves_ulift_fin_of_preserves_binary_and_terminal F (fintype.card J),
  apply preserves_limits_of_shape_of_equiv (discrete.equivalence (e.trans equiv.ulift.symm)).symm,
end

end preserves

/--
Given `n+1` objects of `C`, a cofan for the last `n` with point `c₁.X`
and a binary cofan on `c₁.X` and `f 0`, we can build a cofan for all `n+1`.

In `extend_cofan_is_colimit` we show that if the two given cofans are colimits,
then this cofan is also a colimit.
-/
@[simps {rhs_md := semireducible}]
def extend_cofan {n : ℕ} {f : ulift (fin (n+1)) → C}
  (c₁ : cofan (λ (i : ulift (fin n)), f ⟨i.down.succ⟩))
  (c₂ : binary_cofan (f ⟨0⟩) c₁.X) :
  cofan f :=
cofan.mk c₂.X
begin
  rintro ⟨i⟩,
  revert i,
  refine fin.cases _ _,
  { apply c₂.inl },
  { intro i,
    apply c₁.ι.app (ulift.up i) ≫ c₂.inr },
end

/--
Show that if the two given cofans in `extend_cofan` are colimits,
then the constructed cofan is also a colimit.
-/
def extend_cofan_is_colimit {n : ℕ} (f : ulift (fin (n+1)) → C)
  {c₁ : cofan (λ (i : ulift (fin n)), f ⟨i.down.succ⟩)} {c₂ : binary_cofan (f ⟨0⟩) c₁.X}
  (t₁ : is_colimit c₁) (t₂ : is_colimit c₂) :
  is_colimit (extend_cofan c₁ c₂) :=
{ desc := λ s,
  begin
    apply (binary_cofan.is_colimit.desc' t₂ (s.ι.app ⟨0⟩) _).1,
    apply t₁.desc ⟨_, discrete.nat_trans (λ i, s.ι.app ⟨i.down.succ⟩)⟩
  end,
  fac' := λ s,
  begin
    rintro ⟨j⟩,
    apply fin.induction_on j,
    { apply (binary_cofan.is_colimit.desc' t₂ _ _).2.1 },
    { rintro i -,
      dsimp only [extend_cofan_ι_app],
      rw [fin.cases_succ, assoc, (binary_cofan.is_colimit.desc' t₂ _ _).2.2, t₁.fac],
      refl }
  end,
  uniq' := λ s m w,
  begin
    apply binary_cofan.is_colimit.hom_ext t₂,
    { rw (binary_cofan.is_colimit.desc' t₂ _ _).2.1,
      apply w ⟨0⟩ },
    { rw (binary_cofan.is_colimit.desc' t₂ _ _).2.2,
      apply t₁.uniq ⟨_, _⟩,
      rintro ⟨j⟩,
      dsimp only [discrete.nat_trans_app],
      rw ← w ⟨j.succ⟩,
      dsimp only [extend_cofan_ι_app],
      rw [fin.cases_succ, assoc], }
  end }

section
variables [has_binary_coproducts.{v} C] [has_initial C]

/--
If `C` has an initial object and binary coproducts, then it has a coproduct for objects indexed by
`ulift (fin n)`.
This is a helper lemma for `has_cofinite_products_of_has_binary_and_terminal`, which is more general
than this.
-/
private lemma has_coproduct_ulift_fin :
  Π (n : ℕ) (f : ulift (fin n) → C), has_coproduct f
| 0 := λ f,
  begin
    letI : has_colimits_of_shape (discrete (ulift (fin 0))) C :=
      has_colimits_of_shape_of_equivalence
        (discrete.equivalence (equiv.ulift.trans fin_zero_equiv').symm),
    apply_instance,
  end
| (n+1) := λ f,
  begin
    haveI := has_coproduct_ulift_fin n,
    apply has_colimit.mk
      ⟨_, extend_cofan_is_colimit f (colimit.is_colimit _) (colimit.is_colimit _)⟩,
  end

/--
If `C` has an initial object and binary coproducts, then it has colimits of shape
`discrete (ulift (fin n))` for any `n : ℕ`.
This is a helper lemma for `has_cofinite_products_of_has_binary_and_terminal`, which is more general
than this.
-/
private lemma has_colimits_of_shape_ulift_fin (n : ℕ) :
  has_colimits_of_shape (discrete (ulift (fin n))) C :=
{ has_colimit := λ K,
begin
  letI := has_coproduct_ulift_fin n K.obj,
  let : K ≅ discrete.functor K.obj := discrete.nat_iso (λ i, iso.refl _),
  apply has_colimit_of_iso this,
end }

/-- If `C` has an initial object and binary coproducts, then it has finite coproducts. -/
lemma has_finite_coproducts_of_has_binary_and_terminal : has_finite_coproducts C :=
⟨λ J 𝒥₁ 𝒥₂, begin
  resetI,
  let e := fintype.equiv_fin J,
  apply has_colimits_of_shape_of_equivalence (discrete.equivalence (e.trans equiv.ulift.symm)).symm,
  refine has_colimits_of_shape_ulift_fin (fintype.card J),
end⟩

end

section preserves
variables (F : C ⥤ D)
variables [preserves_colimits_of_shape (discrete walking_pair) F]
variables [preserves_colimits_of_shape (discrete pempty) F]
variables [has_finite_coproducts.{v} C]

/--
If `F` preserves the initial object and binary coproducts, then it preserves products indexed by
`ulift (fin n)` for any `n`.
-/
noncomputable def preserves_fin_of_preserves_binary_and_initial  :
  Π (n : ℕ) (f : ulift (fin n) → C), preserves_colimit (discrete.functor f) F
| 0 := λ f,
  begin
    letI : preserves_colimits_of_shape (discrete (ulift (fin 0))) F :=
      preserves_colimits_of_shape_of_equiv
        (discrete.equivalence (equiv.ulift.trans fin_zero_equiv').symm) _,
    apply_instance,
  end
| (n+1) :=
  begin
    haveI := preserves_fin_of_preserves_binary_and_initial n,
    intro f,
    refine preserves_colimit_of_preserves_colimit_cocone
      (extend_cofan_is_colimit f (colimit.is_colimit _) (colimit.is_colimit _)) _,
    apply (is_colimit_map_cocone_cofan_mk_equiv _ _ _).symm _,
    let := extend_cofan_is_colimit (λ i, F.obj (f i))
              (is_colimit_of_has_coproduct_of_preserves_colimit F _)
              (is_colimit_of_has_binary_coproduct_of_preserves_colimit F _ _),
    refine is_colimit.of_iso_colimit this _,
    apply cocones.ext _ _,
    apply iso.refl _,
    rintro ⟨j⟩,
    apply fin.induction_on j,
    { apply category.comp_id },
    { rintro i -,
      dsimp only [extend_cofan_ι_app, iso.refl_hom, cofan.mk_ι_app],
      rw [fin.cases_succ, fin.cases_succ],
      erw [comp_id, ←F.map_comp],
      refl, }
  end

/--
If `F` preserves the initial object and binary coproducts, then it preserves colimits of shape
`discrete (ulift (fin n))`.
-/
def preserves_ulift_fin_of_preserves_binary_and_initial (n : ℕ) :
  preserves_colimits_of_shape (discrete (ulift (fin n))) F :=
{ preserves_colimit := λ K,
  begin
    let : discrete.functor K.obj ≅ K := discrete.nat_iso (λ i, iso.refl _),
    haveI := preserves_fin_of_preserves_binary_and_initial F n K.obj,
    apply preserves_colimit_of_iso_diagram F this,
  end }

/-- If `F` preserves the initial object and binary coproducts then it preserves finite products. -/
def preserves_finite_coproducts_of_preserves_binary_and_initial
  (J : Type v) [fintype J] :
  preserves_colimits_of_shape.{v} (discrete J) F :=
begin
  classical,
  let e := fintype.equiv_fin J,
  haveI := preserves_ulift_fin_of_preserves_binary_and_initial F (fintype.card J),
  apply preserves_colimits_of_shape_of_equiv (discrete.equivalence (e.trans equiv.ulift.symm)).symm,
end

end preserves

end category_theory
