import category_theory.category
import category_theory.arrow
import category_theory.isomorphism
import category_theory.limits.shapes.pullbacks
import category_theory.eq_to_hom
import category_theory.functor
import category_theory.Fintype
import category_theory.adjunction.basic
import data.subtype
import category_theory.model_categories.lifting_properties

universes v v' u u'

namespace category_theory

open category_theory

variables {C : Type u} [category.{v} C]
variables {D : Type u'} [category.{v'} D]

/-- A shorthand for the condition singling out some arrows in a category `C`. -/
def arrow_cond (C : Type u) [category.{v} C] := set (arrow C)

instance : has_inter (arrow_cond C) := ⟨set.inter⟩

instance : has_subset (arrow_cond C) := ⟨set.subset⟩

lemma arrow_cond.inter_subset_left {I J : arrow_cond C} : I ∩ J ⊆ I :=
  set.inter_subset_left I J

lemma arrow_cond.inter_subset_right {I J : arrow_cond C} : I ∩ J ⊆ J :=
  set.inter_subset_right I J

@[ext] def arrow_cond.ext {I J : arrow_cond C}
  (h : ∀ f, I f ↔ J f) : I = J :=
by ext x y f; apply h

lemma arrow_cond.subset_antisymm {I J : arrow_cond C} (h : I ⊆ J) (h' : J ⊆ I) :
  I = J :=
by ext; tauto

/- The condition singling out all arrows. -/
def arrow_cond.univ : arrow_cond C :=
  λ i, true

/- The condition singling out all arrows. -/
def arrow_cond_iso : arrow_cond C :=
  λ i, nonempty (is_iso i.hom)

/- The condition singling out all identity morphisms. -/
def arrow_cond_ids : arrow_cond C :=
  λ i, ∃ X : C, i.left = X ∧ i.right = X /- todo ! ∧ i.hom = 𝟙 X -/

/-- The essential image of an arrow class under a given functor. -/
def arrow_cond.ess_image (F : C ⥤ D) (Z : arrow_cond C) : arrow_cond D :=
  λ i, ∃ j : arrow C, ∃ i ≅ (functor.map_arrow F).obj j, Z j

/-- The preimage of an arrow class under a given functor. -/
def arrow_cond.preimage (F : C ⥤ D) (Z : arrow_cond D) : arrow_cond C :=
  λ i, Z ((functor.map_arrow F).obj i)

/-- The left lifting property against another condition. -/
def left_lifting_property (R : arrow_cond C) : arrow_cond C :=
  λ l, ∀ r : arrow C, R r → has_lifting_property l r

/-- The right lifting property against another condition. -/
def right_lifting_property (L : arrow_cond C) : arrow_cond C :=
  λ r, ∀ l : arrow C, L l → has_lifting_property l r

/-- Reversal of implications for left lifting properties -/
lemma left_lifting_property_sub (R R' : arrow_cond C) : R ⊆ R' →
  left_lifting_property R' ⊆ left_lifting_property R :=
begin
  tauto, -- λ h f hf g hg, begin apply hf, apply h, apply hg end
end

/-- Reversal of implications for left lifting properties -/
lemma right_lifting_property_sub (L L' : arrow_cond C) : L ⊆ L' →
  right_lifting_property L' ⊆ right_lifting_property L :=
begin
  tauto --λ h f hf g hg, begin apply hf, apply h, apply hg end
end

lemma sub_left_of_sub_right (Z Z' : arrow_cond C) :
  Z ⊆ right_lifting_property Z' → Z' ⊆ left_lifting_property Z :=
begin
  tauto
end

lemma sub_right_of_sub_left (Z Z' : arrow_cond C) :
  Z' ⊆ left_lifting_property Z → Z ⊆ right_lifting_property Z' :=
begin
  tauto
end

lemma sub_right_iff_sub_left (Z Z' : arrow_cond C) :
  Z' ⊆ left_lifting_property Z ↔ Z ⊆ right_lifting_property Z' :=
begin
  tauto,
end

lemma sub_right_left (Z : arrow_cond C) :
  Z ⊆ right_lifting_property (left_lifting_property Z) :=
begin
  tauto,
end

lemma sub_left_right (Z : arrow_cond C) :
  Z ⊆ left_lifting_property (right_lifting_property Z) :=
begin
  tauto,
end

/-- Repeating closure processes stops: `r(ight lifting property) l r = r`. -/
lemma right_eq_right_left_right (Z : arrow_cond C) :
  right_lifting_property Z =
  right_lifting_property (left_lifting_property (right_lifting_property Z)) :=
begin
  apply arrow_cond.subset_antisymm,
  { tauto,  },
  { apply right_lifting_property_sub,
    exact sub_left_right Z, }
end

/-- Given two composable squares, a lift of the second can be precomposed to get a lift of the
composite square. -/
def pullback_lift_struct {f g h : arrow C} (sq₁ : f ⟶ g) (sq₂ : g ⟶ h) :
  arrow.lift_struct sq₂ → arrow.lift_struct (sq₁ ≫ sq₂) :=
λ lift₂,
begin
  fconstructor,
  { exact sq₁.right ≫ lift₂.lift },
  { rw comma.comp_left,
    rw ←category.assoc,
    rw ←lift₂.fac_left,
    have : f.hom ≫ sq₁.right = sq₁.left ≫ g.hom := begin tidy, end,
    rw this,
    rw category.assoc, },
  { rw comma.comp_right,
    rw category.assoc,
    rw lift₂.fac_right, }
end

lemma lifting_iso {i i' p : arrow C} [h: i ≅ i']: has_lifting_property i' p → has_lifting_property i p :=
begin
  intro hi'p,
  intro sq,
  let sq' := h.inv ≫ sq,
  haveI hlift' := hi'p sq',
  fconstructor,
  fconstructor,
  have lift' := arrow.lift sq',

  sorry,
  /-let hs := h.hom,
  let s := pullback_lift_struct h.hom sq' lift',
  --let lift' := lift sq',
  --use (arrow.has_lift.struct (arrow.hom_mk comm)).lift,
    -/
end

lemma lifting_adjunction {F : C ⥤ D} {G : D ⥤ C} [adj : F ⊣ G]
  (i : arrow C) (p : arrow D) :
  has_lifting_property ((functor.map_arrow F).obj i) p →
  has_lifting_property i ((functor.map_arrow G).obj p) :=
begin
  intros h sq,

  -- convert the square from i ⟶ G p into F i ⟶ p
  let sq_adjoint := ((adjunction_arrow_category F G adj).hom_equiv i p).inv_fun sq,
  haveI := h sq_adjoint,

  fconstructor,
  fconstructor,
  fconstructor,
  { simp,
    exact (adj.hom_equiv i.right p.left).to_fun (arrow.lift sq_adjoint), },
  {
    sorry
  },
  { sorry, }
end

lemma lifting_properties_adjunction
  (A : arrow_cond C) (B : arrow_cond D)
  {F : C ⥤ D} {G : D ⥤ C} [F ⊣ G] :
  arrow_cond.ess_image F A ⊆ left_lifting_property B ↔ A ⊆ arrow_cond.ess_image G B :=
begin
  -- use lifting_adjunction
  sorry
end

variable (Z : arrow_cond C)

/-- The condition of being closed under isomorphisms. -/
def closed_under_isos : Prop :=
  ∀ i : arrow C, ∀ f : arrow C, ∀ sq : i ≅ f, Z i → Z f

/-- The condition of containing all isomorphisms. -/
def contains_isos : Prop :=
  arrow_cond_iso ⊆ Z

/-- The condition of containing all identity maps. -/
def contains_ids : Prop :=
  ∀ X : C, Z (arrow.mk (𝟙 X))

def is_pushout_square {i f : arrow C} (sq : i ⟶ f) : Prop := true
--begin
  -- let r := span i.hom sq.left,
  --sorry
--end

/-- The condition of being closed under composition -/
def closed_under_composition : Prop :=
  ∀ A B C : C, ∀ i : A ⟶ B, ∀ j : B ⟶ C, Z (arrow.mk i) → Z (arrow.mk j) →
  Z (arrow.mk (i ≫ j))

/-- The condition of being closed under cancellation at the left -/
def closed_under_left_cancellation : Prop :=
  ∀ A B C : C, ∀ i : A ⟶ B, ∀ j : B ⟶ C, Z (arrow.mk j) →
  Z (arrow.mk (i ≫ j)) → Z (arrow.mk i)

/-- The condition of being closed under cancellation at the left -/
def closed_under_right_cancellation : Prop :=
  ∀ A B C : C, ∀ i : A ⟶ B, ∀ j : B ⟶ C, Z (arrow.mk i) →
  Z (arrow.mk (i ≫ j)) → Z (arrow.mk j)

/-- The two-out-of-three property: if 2 among {f, g, g ∘ f} are in there, the third is as well. -/
def two_out_of_three : Prop :=
  closed_under_composition Z ∧
  closed_under_left_cancellation Z ∧
  closed_under_right_cancellation Z

/-- The condition of being closed under pushouts along arrows satisfying another condition. -/
def closed_under_pushouts_rel (Z' : arrow_cond C) : Prop :=
  ∀ i : arrow C, ∀ f : arrow C, ∀ (sq : i ⟶ f),
  /- Z' (arrow.mk sq.left) → -/ is_pushout_square sq → Z i → Z f

/-- Definition: X is a retract of U if there are maps X → U → X whose composite is the identity. -/
def is_retract (X U : C) : Prop :=
∃ i : X ⟶ U, ∃ p : U ⟶ X, i ≫ p = 𝟙 X

/-- The condition of being closed under retracts. -/
def closed_under_retracts (Z : arrow_cond C) : Prop :=
  ∀ i : arrow C, ∀ f : arrow C, is_retract i f → Z f → Z i

end category_theory
