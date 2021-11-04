/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/

import topology.sheaves.sheaf_condition.opens_le_cover

/-!
# Consequences of the sheaf condition about covers by open sets in a topological basis

Let `B` be a basis of a topological space `X`.

This file shows that if `G` is a sheaf on `X`,
then `G(U)` is the limit of all `G(V)` with `V ∈ B, V ⊆ U`,
and if `α : F ⟶ G` is a homomorphism of presheaves on `X`
defined only on open sets in `B`, it uniquely extends to an
actual homomorphism on all open sets.

-/

universes v u

noncomputable theory

open category_theory
open category_theory.limits
open topological_space
open opposite
open topological_space.opens

namespace Top

variables {C : Type u} [category.{v} C] (X : Top.{v})

/-- Bundled indexed family of open sets. -/
structure opens_index_struct :=
(ι : Type v)
(f : ι → opens X)
-- if ι and B are separate then Lean cannot infer induced category instance on ι

instance : inhabited (opens_index_struct X) := ⟨⟨ulift empty, empty.elim ∘ ulift.down⟩⟩

variables {X} (B : X.opens_index_struct) (U : opens X) (F G : presheaf C X)

/-- The proposition that the range of the family `B` is a basis. -/
def is_basis_range := is_basis (set.range (B.f))

namespace presheaf

namespace sheaf_condition

/--
The subtype of indices `i` of the family `B` (normally an indexed basis) whose
corresponding open sets `B.f i` are contained in `U`.
-/
@[nolint has_inhabited_instance]
def basis_le : Type v := { i // B.f i ≤ U }

instance : category B.ι := induced_category.category (op ∘ B.f)
instance : category (basis_le B U) := category_theory.full_subcategory _

namespace basis_le

private abbreviation bl2b := full_subcategory_inclusion (λ i, B.f i ≤ U)
private abbreviation idf := induced_functor (op ∘ B.f)
private abbreviation bli := bl2b B U ⋙ idf B

/-- The family of opens `{ V ∈ B | B ⊆ U }`. -/
def basis_le_fam := λ i : basis_le B U, B.f i.1
example : (bli B U).obj = op ∘ basis_le_fam B U := rfl

/-- The cone over `{ V ∈ B | B ⊆ U }` with cone point `U`. -/
def basis_le_cone : cone (bli B U) :=
{ X := op U,
  π := { app := λ i, i.2.hom.op } }

/-- The cone over `{ V ∈ B | B ⊆ U }` with cone point the union of all `V`. -/
def basis_le_cone' : cone (bli B U) :=
{ X := op (supr (basis_le_fam B U)),
  π := { app := λ i, (opens.le_supr _ i).op } }

/-- A cone in the category of open sets is determined by the cone point (and the diagram). -/
@[ext] lemma cone_ext {J : Type*} [category J] {f : J ⥤ (opens X)ᵒᵖ}
  {c₁ c₂ : cone f} (h : c₁.X = c₂.X) : c₁ = c₂ :=
-- or any category with subsingleton hom sets in place of (opens X)ᵒᵖ
by { cases c₁, cases c₂, congr, exact h,
     convert cast_heq _ _, dsimp at h, rw h }

/-- If `B` is an indexed basis, `⋃{ V ∈ B | B ⊆ U } = U`. -/
lemma supr_basis_le_eq_self {B} (hB : is_basis_range B) :
  supr (basis_le_fam B U) = U :=
begin
  apply subtype.eq, rw [hB.open_eq_sUnion' U.2, ←set.range_comp],
  ext, exact ⟨λ ⟨_,⟨_,⟨⟨i,hi⟩,rfl⟩,rfl⟩,hx⟩, ⟨_,⟨⟨⟨i,rfl⟩,hi⟩,hx⟩⟩,
              λ ⟨_,⟨⟨⟨i,rfl⟩,hi⟩,hx⟩⟩, ⟨_,⟨_,⟨⟨i,hi⟩,rfl⟩,rfl⟩,hx⟩⟩,
end

/-- If `B` is an indexed basis, the two cones are equal. -/
lemma basis_le_cone_eq {B} (hB : is_basis_range B) :
  basis_le_cone B U = basis_le_cone' B U :=
let h := congr_arg op (supr_basis_le_eq_self U hB).symm in cone_ext h
-- `h` can't be inlined

/-- `F(U)` over all `F(V)` with `V ∈ B, V ⊆ U`. -/
def basis_le_presheaf_cone := F.map_cone (basis_le_cone B U)

lemma basis_le_presheaf_cone_app (i : basis_le B U) :
  (basis_le_presheaf_cone B U F).π.app i = F.map i.2.hom.op := rfl

lemma basis_le_presheaf_cone_app_id (i : B.ι) :
  (basis_le_presheaf_cone B (B.f i) F).π.app ⟨i, le_of_eq rfl⟩ = 𝟙 _
:= by { dunfold basis_le_presheaf_cone, dsimp, rw ← F.map_id, refl }

/-- The condition that `F(U)` is the limit of all `F(V)` with `V ∈ B, V ⊆ U`. -/
@[nolint has_inhabited_instance]
def lim_basis_le : Type (max u v) :=
  Π (U : opens X), is_limit (basis_le_presheaf_cone B U F)

/-- If `F` is a sheaf, `F(U) ⟶ F(V)` for `V` in a cover of `U` are jointly monomorphic. -/
lemma mono_to_cover_of_sheaf {U F} (hF : is_sheaf_opens_le_cover F)
   (hU : supr B.f = U) {A : C} {f g : A ⟶ F.obj (op U)}
   -- hU is a hack to get rid of "motive not type correct" in mono_to_basis_le_of_sheaf below
   (h : ∀ i, f ≫ F.map (hU.rec (opens.le_supr B.f i)).op
           = g ≫ F.map (hU.rec (opens.le_supr B.f i)).op) :
   f = g :=
begin
  subst hU, apply (hF B.f).some.hom_ext,
  intro V, dsimp, let i := V.unop.2.some,
  let i1 := opens.le_supr B.f i, let i2 := V.unop.2.some_spec.hom,
  have : (opens_le_cover_cocone B.f).ι.app V.unop = i2 ≫ i1 := rfl,
  rw [this, op_comp, F.map_comp, ←category.assoc, h i, category.assoc],
end

/-- If `F` is a sheaf and `B` a basis, `F(U) ⟶ F(V)` for `V ∈ B, V ⊆ U` are jointly monomorphic. -/
lemma mono_to_basis_le_of_sheaf {B F} (hB : is_basis_range B)
  (hF : is_sheaf_opens_le_cover F) {A : C} {f g : A ⟶ F.obj (op U)}
  (h : ∀ i : basis_le B U, f ≫ F.map i.2.hom.op = g ≫ F.map i.2.hom.op) :
  f = g :=
mono_to_cover_of_sheaf ⟨basis_le B U, _⟩ hF
  (supr_basis_le_eq_self U hB) (λ V, by convert h V)

/-- Technical lemma. -/
lemma cone_opens_w (c : cone (bli B U ⋙ F))
  {i : basis_le B U} {j : B.ι} {h : B.f j ≤ U}
  (f : (bli B U).obj i ⟶ (idf B).obj j) :
  c.π.app i ≫ F.map f = c.π.app ⟨j,h⟩ :=
let f' : i ⟶ (⟨j,h⟩ : basis_le B U) := f  in  c.w f'

/--
Construct a cone over `{ F(W) | ∃ V ∈ B, W ⊆ V ⊆ U }`
    given a cone over `{ F(V) | V ∈ B, V ⊆ U }` and that `F` is a sheaf.
-/
def cone_opens_le_cover_of_cone_basis_le {B} (hB : is_basis_range B)
  (hF : F.is_sheaf_opens_le_cover) (c : cone (bli B U ⋙ F)) :
  cone ((full_subcategory_inclusion _ : opens_le_cover (basis_le_fam B U) ⥤ opens X).op ⋙ F) :=
begin
  use c.X, refine ⟨λW, c.π.app (W.unop.2.some) ≫ F.map W.unop.2.some_spec.hom.op, _⟩,
  intros W₁ W₂ _, apply mono_to_basis_le_of_sheaf W₂.unop.1 hB hF,
  intro i, dsimp, simp only [category.id_comp, category.assoc, ←F.map_comp, ←op_comp],
  iterate 2 {rw cone_opens_w},
  exact i.2.trans (W₂.unop.2.some_spec.trans W₂.unop.2.some.2),
end

/-- If `F` is the sheaf, `F(U)` is the limit of all `F(V)` with `V ∈ B, V ⊆ U`. -/
def lim_basis_le_of_sheaf {B} (hB : is_basis_range B)
  (hF : F.is_sheaf_opens_le_cover) : lim_basis_le B F :=
begin
  intro U, unfold basis_le_presheaf_cone, rw basis_le_cone_eq U hB,
  let f := cone_opens_le_cover_of_cone_basis_le U F hB hF,
  have hU := hF (basis_le_fam B U), fsplit,
    exact λ c, hU.some.lift (f c),
    intros c i, abstract fac { dsimp,
      let hi : ∃ j, B.f i ≤ basis_le_fam B U j := ⟨i, le_of_eq rfl⟩,
      convert hU.some.fac (f c) (op ⟨B.f i,hi⟩) using 1,
      exact (c.w hi.some_spec.hom.op).symm },
    intros c ι h,
    apply mono_to_cover_of_sheaf ⟨basis_le B U, _⟩ hF rfl,
    intro i, specialize h i,
    rwa ← lim_basis_le_of_sheaf.fac F hB hF U hU c i at h,
end

namespace sheaf_hom

variables {B F G}

/--
The condition that the presheaf hom `lift` is the unique extension of `α`,
a "presheaf hom on the basic opens".
-/
@[nolint has_inhabited_instance]
structure uniq_extn_struct (α : idf B ⋙ F ⟶ idf B ⋙ G) :=
  (lift : F ⟶ G)
  (fac : whisker_left (idf B) lift = α)
  (uniq : ∀ {β}, whisker_left (idf B) β = α → β = lift)

/--
If the target `G` is a sheaf and `B` is a basis,
a presheaf hom on `B` extends uniquely to a actual presheaf hom (on all opens).
-/
def uniq_extn_from_basis (hG : G.is_sheaf_opens_le_cover)
  (hB : is_basis_range B) (α : idf B ⋙ F ⟶ idf B ⋙ G) :
  uniq_extn_struct α :=
begin
  have hl := lim_basis_le_of_sheaf G hB hG,
  let c : Π U, cone (bli B U ⋙ G) :=
    λ U, let α' := whisker_left (bl2b B U) α in
    ⟨F.obj (op U), (basis_le_presheaf_cone B U F).π ≫ α'⟩,
/- strange error when α' is inlined: type mismatch at application
   whisker_left (bl2b B U).op, term (bl2b B U).op has type ... ⥤ (B.ι)ᵒᵖ
           but is expected to have type {X_1 // B.f X_1 ≤ U}ᵒᵖ ⥤ (opens ↥X)ᵒᵖ -/
  fsplit, fsplit, exact λ U, (hl U.unop).lift (c U.unop),
  { intros U V f,
    apply mono_to_basis_le_of_sheaf V.unop hB hG,
    cases f.unop, cases down, intro i, rw category.assoc,
    convert whisker_eq (F.map f) ((hl V.unop).fac (c V.unop) i) using 1,
    convert (hl U.unop).fac (c U.unop) ⟨i.1,i.2.trans down⟩ using 1,
    rw [category.assoc, ←G.map_comp], refl,
    rw [nat_trans.comp_app, nat_trans.comp_app, ←category.assoc],
    congr, rw [basis_le_presheaf_cone_app, ←F.map_comp], refl },
  { ext i, convert (hl (B.f i)).fac (c (B.f i)) ⟨i,le_of_eq rfl⟩ using 1,
    rw basis_le_presheaf_cone_app_id, exact (category.comp_id _).symm,
    dsimp, rw basis_le_presheaf_cone_app_id,
    convert (category.id_comp _).symm },
  { intros β h, ext U, apply (hl U.unop).uniq (c U.unop),
    intro V, rw [basis_le_presheaf_cone_app, ←β.naturality],
    dsimp, rw ← h, dsimp, refl },
end

lemma ext' (hG : G.is_sheaf_opens_le_cover) (hB : is_basis_range B) {β γ : F ⟶ G}
  (h : whisker_left (idf B) β = whisker_left (idf B) γ) : β = γ :=
by { rw (uniq_extn_from_basis hG hB _).uniq h,
  exact ((uniq_extn_from_basis hG hB _).uniq rfl).symm }

/-- It suffices to verify a sheaf hom equalities on basic opens. -/
theorem ext (hG : G.is_sheaf_opens_le_cover) (hB : is_basis_range B) {β γ : F ⟶ G}
  (h : ∀ i, β.app (op $ B.f i) = γ.app (op $ B.f i)) : β = γ :=
by { apply ext' hG hB, ext, exact h x }

end sheaf_hom

end basis_le

end sheaf_condition

end presheaf


namespace sheaf

open presheaf.sheaf_condition.basis_le

variables {ι : Type v} {f : ι → opens X} {F G} [has_products C]

private abbreviation idf := induced_functor (op ∘ f)

/--
If the target `G` is a sheaf and `B` is a basis,
a presheaf hom on `B` extends uniquely to a actual presheaf hom (on all opens).
-/
@[irreducible] def uniq_hom_extn_from_basis (hG : G.is_sheaf) (hB : is_basis_range B)
  (α : idf ⋙ F ⟶ idf ⋙ G) : sheaf_hom.uniq_extn_struct α :=
sheaf_hom.uniq_extn_from_basis
  ((presheaf.is_sheaf_iff_is_sheaf_opens_le_cover _).1 hG) hB α

/-- It suffices to verify sheaf hom equalities on basic opens. -/
theorem hom_ext (hG : G.is_sheaf) (hB : is_basis_range B) (β γ : F ⟶ G)
  (h : ∀ i, β.app (op $ B.f i) = γ.app (op $ B.f i)) : β = γ :=
sheaf_hom.ext ((presheaf.is_sheaf_iff_is_sheaf_opens_le_cover _).1 hG) hB h

end sheaf

end Top
