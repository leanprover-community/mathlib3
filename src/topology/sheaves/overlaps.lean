import topology.sheaves.sheaf
import category_theory.limits.preserves.basic

/-!
# Equivalent formulations of the sheaf condition

We give an equivalent formulation of the sheaf condition.

Given any indexed type `ι`, we define `overlap ι`,
a category with objects corresponding to
* individual open sets, `single i`, and
* intersections of pairs of open sets, `pair i j`,
with morphisms from `pair i j` to both `single i` and `single j`.

Any open cover `U : ι → opens X` provides a functor `diagram U : overlap ι ⥤ (opens X)ᵒᵖ`.

There is a canonical cone over this functor, `cone U`, whose cone point is `supr U`,
and in fact this is a limit cone.

A presheaf `F : presheaf C X` is a sheaf precisely if it preserves this limit.
We express this in two equivalent ways, as
* `is_limit (F.map_cone (cone U))`, or
* `preserves_limit (diagram U) F`
-/

universes v u

open topological_space
open Top
open opposite
open category_theory
open category_theory.limits

namespace category_theory

inductive overlap (ι : Type v)
| single : ι → overlap
| pair : ι → ι → overlap

variables {ι : Type v}

namespace overlap

inductive hom : overlap ι → overlap ι → Type v
| id_single : Π i, hom (single i) (single i)
| id_pair : Π i j, hom (pair i j) (pair i j)
| left : Π i j, hom (single i) (pair i j)
| right : Π i j, hom (single j) (pair i j)

open hom

def id : Π (o : overlap ι), hom o o
| (single i) := id_single i
| (pair i j) := id_pair i j

def comp : Π {o₁ o₂ o₃ : overlap ι} (f : hom o₁ o₂) (g : hom o₂ o₃), hom o₁ o₃
| _ _ _ (id_single i) g := g
| _ _ _ (id_pair i j) g := g
| _ _ _ (left i j) (id_pair _ _) := left i j
| _ _ _ (right i j) (id_pair _ _) := right i j

section
local attribute [tidy] tactic.case_bash

instance : category (overlap ι) :=
{ hom := hom,
  id := id,
  comp := λ X Y Z f g, comp f g, }

end

end overlap

end category_theory

namespace Top.cover

open category_theory
open category_theory.overlap category_theory.overlap.hom

variables {X : Top.{v}}
variables {ι : Type v}
variables (U : ι → opens X)

def diagram_obj : overlap ι → (opens X)ᵒᵖ
| (single i) := op (U i)
| (pair i j) := op (U i ⊓ U j)

def diagram_map : Π {o₁ o₂ : overlap ι} (f : o₁ ⟶ o₂), diagram_obj U o₁ ⟶ diagram_obj U o₂
| _ _ (id_single i) := 𝟙 _
| _ _ (id_pair i j) := 𝟙 _
| _ _ (left i j) := (opens.inf_le_left _ _).op
| _ _ (right i j) := (opens.inf_le_right _ _).op

def diagram : overlap ι ⥤ (opens X)ᵒᵖ :=
{ obj := diagram_obj U,
  map := λ X Y f, diagram_map U f, }

def cone_π_app : Π (o : overlap ι), op (supr U) ⟶ diagram_obj U o
| (single i) := (opens.le_supr _ _).op
| (pair i j) := (opens.inf_le_left _ _ ≫ opens.le_supr _ _).op

@[simps]
def cone : cone (diagram U) :=
{ X := op (supr U),
  π := { app := cone_π_app U, } }

-- TODO move these
variables {α : Type u} [preorder α]
def op_hom_of_le {U V : αᵒᵖ} (h : unop V ≤ unop U) : U ⟶ V :=
has_hom.hom.op (hom_of_le h)
def le_of_op_hom {U V : αᵒᵖ} (h : U ⟶ V) : unop V ≤ unop U :=
le_of_hom (h.unop)

def cone_is_limit : is_limit (cone U) :=
{ lift := λ s, op_hom_of_le (λ x h,
  begin
    simp [opens.mem_supr] at h,
    cases h with i mem,
    exact le_of_op_hom (s.π.app (single i)) mem,
  end) }

end Top.cover

namespace Top.presheaf

open Top.cover
open category_theory.overlap category_theory.overlap.hom

variables {X : Top.{v}}
variables {ι : Type v}
variables (U : ι → opens X)

variables {C : Type u} [category.{v} C] [has_products C]

section

local attribute [tidy] tactic.case_bash

@[simps]
def cone_equiv_functor (F : presheaf C X)
  ⦃ι : Type v⦄ (U : ι → opens ↥X) :
  limits.cone (diagram U ⋙ F) ⥤ limits.cone (presheaf.sheaf_condition.diagram F U) :=
{ obj := λ c,
  { X := c.X,
    π :=
    { app :=
      begin
        rintro (_|_),
        { apply pi.lift,
          intro i,
          exact c.π.app (single i), },
        { apply pi.lift,
          rintro ⟨i, j⟩,
          exact c.π.app (pair i j), }
      end,
      naturality' :=
      begin
        rintro (_|_) (_|_) ⟨⟩,
        { ext i, dsimp, simp, dsimp, simp, },
        { ext ⟨i, j⟩, dsimp [presheaf.sheaf_condition.left_res],
          simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app, category.assoc],
          have h := c.π.naturality (hom.left i j),
          dsimp at h,
          simpa using h, },
        { ext ⟨i, j⟩, dsimp [presheaf.sheaf_condition.right_res],
          simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app, category.assoc],
          have h := c.π.naturality (hom.right i j),
          dsimp at h,
          simpa using h,  },
        { ext, dsimp, simp, dsimp, simp, },
      end, }, },
  map := λ c c' f,
  { hom := f.hom, }, }.

@[simps]
def cone_equiv_inverse (F : presheaf C X)
  ⦃ι : Type v⦄ (U : ι → opens ↥X) :
  limits.cone (presheaf.sheaf_condition.diagram F U) ⥤ limits.cone (diagram U ⋙ F) :=
{ obj := λ c,
  { X := c.X,
    π :=
    { app :=
      begin
        rintro (⟨i⟩|⟨i,j⟩),
        { exact c.π.app (walking_parallel_pair.zero) ≫ pi.π _ i, },
        { exact c.π.app (walking_parallel_pair.one) ≫ pi.π _ (i, j), }
      end,
      naturality' :=
      begin
        rintro (⟨i⟩|⟨⟩) (⟨⟩|⟨j,j⟩) ⟨⟩,
        { dsimp, erw [F.map_id], simp, },
        { dsimp, simp only [category.id_comp, category.assoc],
          have h := c.π.naturality (walking_parallel_pair_hom.left),
          dsimp [presheaf.sheaf_condition.left_res] at h,
          simp only [category.id_comp] at h,
          have h' := h =≫ pi.π _ (i, j),
          rw h',
          simp,
          refl, },
        { dsimp, simp only [category.id_comp, category.assoc],
          have h := c.π.naturality (walking_parallel_pair_hom.right),
          dsimp [presheaf.sheaf_condition.right_res] at h,
          simp only [category.id_comp] at h,
          have h' := h =≫ pi.π _ (j, i),
          rw h',
          simp,
          refl, },
        { dsimp, erw [F.map_id], simp, },
      end, }, },
  map := λ c c' f,
  { hom := f.hom,
    w' :=
    begin
      rintro (⟨i⟩|⟨i,j⟩),
      { dsimp,
        rw [←(f.w walking_parallel_pair.zero), category.assoc], },
      { dsimp,
        rw [←(f.w walking_parallel_pair.one), category.assoc], },
    end }, }.

@[simps {rhs_md := semireducible}]
def cone_equiv_unit_iso (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens X) :
  𝟭 (limits.cone (diagram U ⋙ F)) ≅
    cone_equiv_functor F U ⋙ cone_equiv_inverse F U :=
nat_iso.of_components (λ c, { hom := { hom := 𝟙 _ }, inv := { hom := 𝟙 _ }}) (by tidy).

@[simps {rhs_md := semireducible}]
def cone_equiv_counit_iso (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens X) :
  cone_equiv_inverse F U ⋙ cone_equiv_functor F U ≅
    𝟭 (limits.cone (presheaf.sheaf_condition.diagram F U)) :=
nat_iso.of_components (λ c,
{ hom :=
  { hom := 𝟙 _,
    w' :=
    begin
      rintro ⟨_|_⟩,
      { ext, dsimp, simp, },
      { ext ⟨i,j⟩, dsimp, simp, },
    end },
  inv :=
  { hom := 𝟙 _,
    w' :=
    begin
      rintro ⟨_|_⟩,
      { ext, dsimp, simp, },
      { ext ⟨i,j⟩, dsimp, simp, },
    end, }}) (by tidy)

@[simps]
def cone_equiv (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens X) :
  limits.cone (diagram U ⋙ F) ≌ limits.cone (presheaf.sheaf_condition.diagram F U) :=
{ functor := cone_equiv_functor F U,
  inverse := cone_equiv_inverse F U,
  unit_iso := cone_equiv_unit_iso F U,
  counit_iso := cone_equiv_counit_iso F U, }

end

local attribute [reducible] presheaf.sheaf_condition.res presheaf.sheaf_condition.left_res

def is_limit_map_cone_of_is_limit_sheaf_condition_fork
  (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens X)
  (P : is_limit (presheaf.sheaf_condition.fork F U)) :
  is_limit (functor.map_cone F (cone U)) :=
is_limit.of_iso_limit ((is_limit.of_cone_equiv (cone_equiv F U).symm).symm P)
{ hom :=
  { hom := 𝟙 _,
    w' :=
    begin
      rintro ⟨⟩,
      { dsimp, simp, refl, },
      { dsimp,
        simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app, category.assoc],
        rw ←F.map_comp,
        refl, }
    end },
  inv :=
  { hom := 𝟙 _,
    w' :=
    begin
      rintro ⟨⟩,
      { dsimp, simp, refl, },
      { dsimp,
        simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app, category.assoc],
        rw ←F.map_comp,
        refl, }
    end }, }

def is_limit_sheaf_condition_fork_of_is_limit_map_cone
  (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens X)
  (Q : is_limit (functor.map_cone F (cone U))) :
  is_limit (presheaf.sheaf_condition.fork F U) :=
is_limit.of_iso_limit ((is_limit.of_cone_equiv (cone_equiv F U)).symm Q)
{ hom :=
  { hom := 𝟙 _,
    w' :=
    begin
      rintro ⟨⟩,
      { dsimp, simp, refl, },
      { dsimp, ext ⟨i, j⟩,
        simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app, category.assoc],
        rw ←F.map_comp,
        refl, }
    end },
  inv :=
  { hom := 𝟙 _,
    w' :=
    begin
      rintro ⟨⟩,
      { dsimp, simp, refl, },
      { dsimp, ext ⟨i, j⟩,
        simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app, category.assoc],
        rw ←F.map_comp,
        refl, }
    end }, }

@[derive subsingleton]
def sheaf_condition' (F : presheaf C X) : Type (max u (v+1)) :=
Π ⦃ι : Type v⦄ (U : ι → opens X), is_limit (F.map_cone (cone U))

@[derive subsingleton]
def sheaf_condition'' (F : presheaf C X) : Type (max u (v+1)) :=
Π ⦃ι : Type v⦄ (U : ι → opens X), preserves_limit (diagram U) F

/--
The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of a limit diagram over `U i` and `U i ⊓ U j`.
-/
def sheaf_condition_equiv (F : presheaf C X) :
  F.sheaf_condition ≃ F.sheaf_condition' :=
equiv.Pi_congr_right (λ i, equiv.Pi_congr_right (λ U,
  equiv_of_subsingleton_of_subsingleton
    (is_limit_map_cone_of_is_limit_sheaf_condition_fork F U)
    (is_limit_sheaf_condition_fork_of_is_limit_map_cone F U)))

def sheaf_condition_equiv'
(F : presheaf C X) :
  F.sheaf_condition' ≃ F.sheaf_condition'' :=
equiv.Pi_congr_right (λ i, equiv.Pi_congr_right (λ U,
  equiv_of_subsingleton_of_subsingleton
   (λ P, preserves_limit_of_preserves_limit_cone (cone_is_limit U) P)
   (by { introI, exact preserves_limit.preserves (cone_is_limit U) })))

end Top.presheaf

namespace Top.cover

open category_theory
open category_theory.overlap category_theory.overlap.hom

variables {X : Top.{v}}
variables {ι : Type v}
variables (U : ι → opens X)

@[simps]
def finset_functor : finset ι ⥤ (opens X)ᵒᵖ :=
{ obj := λ s, op (Inf (U '' ↑s)),
  map := λ s s' f, op_hom_of_le (Inf_le_Inf (set.monotone_image (le_of_hom f))), }

def nonempty_finset_functor : { s : finset ι // s.nonempty } ⥤ (opens X)ᵒᵖ :=
full_subcategory_inclusion _ ⋙ finset_functor U

@[simp]
lemma nonempty_finset_functor_obj (s : { s : finset ι // s.nonempty }) :
  (nonempty_finset_functor U).obj s = op (Inf (U '' ↑s.val)) := rfl

def nonempty_finset_functor_cone : limits.cone (nonempty_finset_functor U) :=
{ X := op (supr U),
  π :=
  { app := λ s, op_hom_of_le
    begin
      dsimp,
      rcases s with ⟨s, ⟨i, m⟩⟩,
      have h₁ : Inf (U '' ↑s) ≤ U i := Inf_le ⟨i, ⟨m, rfl⟩⟩,
      have h₂ : U i ≤ supr U := le_supr U i,
      exact h₁.trans h₂,
    end }, }

def nonempty_finset_functor_cone_is_limit : is_limit (nonempty_finset_functor_cone U) :=
{ lift := λ s, op_hom_of_le (λ x h,
  begin
    simp [opens.mem_supr] at h,
    rcases h with ⟨_, ⟨⟨H, ⟨⟨i, rfl⟩, rfl⟩⟩, m⟩⟩,
    exact le_of_op_hom (s.π.app ⟨{i}, finset.singleton_nonempty i⟩) (by simpa using m),
  end) }

-- TODO yet another formulation of the sheaf condition

open_locale classical

@[simp]
noncomputable def overlap_to_nonempty_finset_functor_obj :
  overlap ι → { s : finset ι // s.nonempty }
| (single i) := ⟨[i].to_finset, ⟨i, by simp⟩⟩
| (pair i j) := ⟨[i,j].to_finset, ⟨i, by simp⟩⟩

@[simp]
noncomputable def overlap_to_nonempty_finset_functor_map :
  Π {X Y : overlap ι} (f : X ⟶ Y),
  overlap_to_nonempty_finset_functor_obj X ⟶ overlap_to_nonempty_finset_functor_obj Y
| _ _ (id_single i) := hom_of_le (le_refl _)
| _ _ (id_pair i j) := hom_of_le (le_refl _)
| _ _ (left i j) := hom_of_le (λ x h, by { simp, left, rcases h with ⟨rfl⟩|w, refl, cases w, })
| _ _ (right i j) := hom_of_le (λ x h, by { simp, right, rcases h with ⟨rfl⟩|w, refl, cases w, })

@[simps]
noncomputable def overlap_to_nonempty_finset_functor :
  overlap ι ⥤ { s : finset ι // s.nonempty } :=
{ obj := overlap_to_nonempty_finset_functor_obj,
  map := λ X Y f, overlap_to_nonempty_finset_functor_map f, }

-- TODO show this is initial?

end Top.cover
