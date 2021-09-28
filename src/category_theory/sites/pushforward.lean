import category_theory.sites.sheaf
import category_theory.limits.kan_extension

universes v u
noncomputable theory

open category_theory
open opposite


section
variables {C : Type u} [category.{v} C] {D : Type u} [category.{v} D]
variables {P Q Q' : Dᵒᵖ ⥤ Type v} (F : C ⥤ D)
open category_theory.presieve

namespace category_theory
namespace presieve
def functor_pullback {X : C} (R : presieve (F.obj X)) : presieve X := λ Y f, R (F.map f)

end presieve

namespace sieve
def functor_pullback {X : C} (R : sieve (F.obj X)) : sieve X := {
  arrows := presieve.functor_pullback F R,
  downward_closed' := λ _ _ f hf g, by {
    unfold presieve.functor_pullback,
    rw F.map_comp,
    exact R.downward_closed hf (F.map g),
  }
}
end sieve

namespace presieve
namespace family_of_elements
section functor_pullback
variables {X : C} {R : presieve (F.obj X)} {x : family_of_elements P R}

def functor_pullback (x : family_of_elements P R) :
  family_of_elements (F.op ⋙ P) (R.functor_pullback F) := λ Y f hf, x (F.map f) hf

lemma compatible.functor_pullback (h : x.compatible) : (x.functor_pullback F).compatible :=
begin
  intros Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ eq,
  exact h (F.map g₁) (F.map g₂) h₁ h₂ (by simp only [← F.map_comp, eq])
end

end functor_pullback

section pullback
def pullback {X Y: D} (f : Y ⟶ X) {R : sieve X} (x : family_of_elements P R) :
  family_of_elements P (R.pullback f) := λ _ g hg, x (g ≫ f) hg

lemma compatible.pullback {X Y: D} (f : Y ⟶ X) {R : sieve X}
  {x : family_of_elements P R} (h : x.compatible) : (x.pullback f).compatible :=
begin
  simp only [compatible_iff_sieve_compatible] at h ⊢,
  intros W Z f₁ f₂ hf,
  refine eq.trans _ (h (f₁ ≫ f) f₂ hf),
  unfold pullback,
  simp only [category.assoc],
end

end pullback


def comp_presheaf_map {X : D} {R : presieve X} (f : P ⟶ Q) (x : family_of_elements P R) :
  family_of_elements Q R := λ Y g hg, f.app (op Y) (x g hg)

lemma compatible.comp_presheaf_map {X : D} {R : presieve X} (f : P ⟶ Q) {x : family_of_elements P R}
  (h : x.compatible) : (x.comp_presheaf_map f).compatible :=
begin
  intros Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ eq,
  change (f.app _ ≫ Q.map _) _ = (f.app _ ≫ Q.map _) _,
  simp only [← f.naturality],
  exact congr_arg (f.app (op W)) (h g₁ g₂ h₁ h₂ eq)
end

end family_of_elements
end presieve
end category_theory
end

/- Can't find these stuff anywhere. -/
lemma lem1 {α : Sort*} {P : α → Prop} (Q : α → Prop) (H : ∀ x, P x → Q x)
  (h : ∃ x, P x) : Q (classical.some h) :=
begin
  apply H, apply classical.some_spec,
end

lemma lem2 {α : Sort*} {P : α → Prop} {h : ∃! x, P x} {y : α} (H : P y) : y = classical.some h :=
begin
  apply lem1,
  intros x hx,
  exact hx.2 y H,
end

variables {C D A : Type u} [category.{u} C] [category.{u} D] [category.{u} A] [limits.has_limits A]

/--
Given a structured arrow `X ⟶ F(U)`, and an arrow `U ⟶ Y`, we can construct a structured
arrow given by `X ⟶ F(U) ⟶ F(Y)`.
-/
def structured_arrow.hom_mk' {F : C ⥤ D} {X : D} {Y : C}
(U : structured_arrow X F) (f : U.right ⟶ Y) :
U ⟶ structured_arrow.mk (U.hom ≫ F.map f) := { right := f }


/-
This is equivalent to the definition found in https://stacks.math.columbia.edu/tag/00XI
via `category_theory.grothendieck_topology.superset_covering`.
-/
structure cocontinuous (J : grothendieck_topology C) (K : grothendieck_topology D) (F : C ⥤ D) :=
(cover_lift : ∀ {U : C} {S : sieve (F.obj U)} (hS : S ∈ K (F.obj U)), S.functor_pullback F ∈ J U)

variables {J : grothendieck_topology C} {K : grothendieck_topology D}
variables {F : C ⥤ D} (HF : cocontinuous J K F)

namespace cocontinuous
namespace Ran_is_sheaf
open category_theory.presieve.family_of_elements
open category_theory.presieve
open category_theory.sieve
open category_theory.limits
/-
Suppose there is a compatible family `x` of elements on `U`, we ought to glue them together
to form a unique section on `S`. We will achieve this by restricting `x` onto objects of the form
`F(Y)` with `Y : C`, and glueing them via the sheaf property.
The uniqueness also follows from the uniqueness provided by the sheaf property.
-/
variable (ℱ : Sheaf J A)
variables {X : A} {U : D} {S : sieve U} (hS : S ∈ K U)
variables {x : S.arrows.family_of_elements ((Ran F.op).obj ℱ.val ⋙ coyoneda.obj (op X))}
variable (hx : x.compatible)

include HF hS hx

/-- Given a `F(Y) ⟶ U`, we can find a unique section in `ℱ(Y)` that agrees with `x` on `Y`. -/
def get_section (Y : structured_arrow (op U) F.op) :
 ∃! (t : (ℱ.val ⋙ coyoneda.obj (op X)).obj (op (unop Y.right))),
  presieve.family_of_elements.is_amalgamation
    (((x.pullback Y.3.unop).functor_pullback F).comp_presheaf_map
      (show _ ⟶ _, from whisker_right ((Ran.adjunction A F.op).counit.app ℱ.val)
        (coyoneda.obj (op X)))) t :=
begin
  let hom_sh := whisker_right ((Ran.adjunction A F.op).counit.app ℱ.val) (coyoneda.obj (op X)),
  have S' := (K.pullback_stable Y.hom.unop hS),
  have hs' := ((hx.pullback Y.3.unop).functor_pullback F).comp_presheaf_map hom_sh,
  exact ℱ.2 X _ (HF.cover_lift S') _ hs',
end

/-- The limit cone in order to glue the sections obtained via `get_section`. -/
def glued_limit_cone : limits.cone ((structured_arrow.proj (op U) (F.op)) ⋙ ℱ.val) :=
{ X := X, π :=
  { app := λ Y, classical.some (get_section HF ℱ hS hx Y),
    naturality' := λ Y Z f, by
    { simp only [functor.comp_map, structured_arrow.proj_map, functor.const.obj_map],
      erw category.id_comp,
      apply lem1 (λ x, classical.some (get_section HF ℱ hS hx Z) = x ≫ ℱ.val.map f.right),
      rintros t₁ ⟨Pt₁, _⟩,
      symmetry,
      apply lem2,
      intros W fw hw,
      dsimp only [comp_presheaf_map,
          family_of_elements.functor_pullback, family_of_elements.pullback],
      have eq := congr_arg quiver.hom.unop f.w,
      erw category.id_comp at eq,
      convert Pt₁ (fw ≫ f.right.unop) (by {
        change S (F.map _ ≫ Y.hom.unop),
        rw eq at hw,
        simpa using hw,
      }) using 3,
      { tidy },
      { simp[eq] } } } }

/-- An helper lemma for the following two lemmas. -/
lemma helper {V} (f : V ⟶ U) (y : ((Ran F.op).obj ℱ.val ⋙ coyoneda.obj (op X)).obj (op V)) (W)
  (H : ∀ {V'} {fV : F.obj V' ⟶ V} (hV),
    ((Ran F.op).obj ℱ.val ⋙ coyoneda.obj (op X)).map fV.op y = x (fV ≫ f) hV) :
  y ≫ limit.π (Ran.diagram F.op ℱ.val (op V)) W =
    (glued_limit_cone HF ℱ hS hx).π.app ((structured_arrow.map f.op).obj W) :=
begin
  apply lem2,
  intros V' fV' hV',
  dsimp only [comp_presheaf_map, Ran.adjunction, Ran.equiv,
    family_of_elements.functor_pullback, family_of_elements.pullback],
  delta structured_arrow.map comma.map_left at hV' ⊢,
  change S _ at hV',
  simp only [quiver.hom.unop_op, functor.const.map_app, unop_comp, ← category.assoc] at hV' ⊢,
  -- rw  at hV',
  erw ← H hV',
  simp,
  erw category.id_comp,
  erw limit.pre_π,
  erw limit.pre_π,
  congr,
  convert limit.w (Ran.diagram F.op ℱ.val (op V)) (structured_arrow.hom_mk' W fV'.op),
  rw structured_arrow.map_mk,
  rw structured_arrow.map_mk,
  erw category.comp_id,
  simp
end

/-- The obtained section is indeed the amalgamation. -/
lemma glued_section_is_amalgamation :
  x.is_amalgamation
    (limit.lift (structured_arrow.proj (op U) F.op ⋙ ℱ.val) (glued_limit_cone HF ℱ hS hx)) :=
begin
  intros V fV hV,
  ext W,
  simp only [functor.comp_map, limit.lift_pre, coyoneda_obj_map, Ran_obj_map],
  erw limit.lift_π,
  symmetry,
  apply helper HF ℱ hS hx _ (x fV hV),
  intros V' fV' hV',
  convert hx (fV') (𝟙 _) hV hV' (by simp),
  simp
end

/-- The amalgamation is indeed unique. -/
lemma glued_section_is_unique (y) (hy: x.is_amalgamation y) :
  y = limit.lift (structured_arrow.proj (op U) F.op ⋙ ℱ.val) (glued_limit_cone HF ℱ hS hx) :=
begin
  unfold limit.lift,
  ext W,
  erw limit.lift_π,
  convert helper HF ℱ hS hx (𝟙 _) y W _,
  { cases W, simp },
  { intros V' fV' hV',
    convert hy fV' (by simpa using hV'),
    erw category.comp_id }
end

end Ran_is_sheaf

/--
If `F` is cocontinuous, then `Ran F.op` pushes sheaves to sheaves.
Basically https://stacks.math.columbia.edu/tag/00XK but without the condition that C or D
has pullbacks
-/
lemma Ran_is_sheaf (HF : cocontinuous J K F) (ℱ : Sheaf J A) :
  presheaf.is_sheaf K ((Ran F.op).obj ℱ.val) :=
begin
  intros X U S hS x hx,
  split, swap,
  { exact limits.limit.lift _ (Ran_is_sheaf.glued_limit_cone HF ℱ hS hx) },
  split,
  { apply Ran_is_sheaf.glued_section_is_amalgamation },
  { apply Ran_is_sheaf.glued_section_is_unique }
end

end cocontinuous
