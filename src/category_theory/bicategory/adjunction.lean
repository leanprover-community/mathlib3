/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.bicategory.coherence_tactic

namespace category_theory

namespace bicategory

open category
open_locale bicategory

universes w v u

variables {B : Type u} [bicategory.{w v} B] {a b c : B} {f : a ⟶ b} {g : b ⟶ a}

/--
The 2-morphism defined by the following pasting diagram:
```
a －－－－－－ ▸ a
  ＼    η      ◥   ＼
  f ＼   g  ／       ＼ f
       ◢  ／     ε      ◢
        b －－－－－－ ▸ b
```
-/
@[simp] def left_zigzag (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) := η ▷ f ⊗≫ f ◁ ε

/--
The 2-morphism defined by the following pasting diagram:
```
        a －－－－－－ ▸ a
       ◥  ＼     η      ◥
  g ／      ＼ f     ／ g
  ／    ε      ◢   ／
b －－－－－－ ▸ b
```
-/
@[simp] def right_zigzag (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) := g ◁ η ⊗≫ ε ▷ g

/-- Adjunction between two 1-morphisms. -/
structure adjunction (f : a ⟶ b) (g : b ⟶ a) :=
(unit   : 𝟙 a ⟶ f ≫ g)
(counit : g ≫ f ⟶ 𝟙 b)
(left_triangle'  : left_zigzag  unit counit = (λ_ _).hom ≫ (ρ_ _).inv . obviously)
(right_triangle' : right_zigzag unit counit = (ρ_ _).hom ≫ (λ_ _).inv . obviously)

localized "infix ` ⊣ `:15 := adjunction" in bicategory

namespace adjunction

restate_axiom left_triangle'
restate_axiom right_triangle'
attribute [simp] left_triangle right_triangle

/-- Adjunction between identities. -/
def id (a : B) : 𝟙 a ⊣ 𝟙 a :=
{ unit            := (ρ_ _).inv,
  counit          := (ρ_ _).hom,
  left_triangle'  := by { dsimp, tactic.coherence.liftable_prefixes, pure_coherence, },
  right_triangle' := by { dsimp, tactic.coherence.liftable_prefixes, pure_coherence } }

instance : inhabited (adjunction (𝟙 a) (𝟙 a)) := ⟨id a⟩

set_option class.instance_max_depth 90

lemma right_adjoint_uniq_aux {f : a ⟶ b} {g₁ g₂ : b ⟶ a} (adj₁ : f ⊣ g₁) (adj₂ : f ⊣ g₂) :
  (𝟙 g₁ ⊗≫ g₁ ◁ adj₂.unit ⊗≫ adj₁.counit ▷ g₂ ⊗≫ 𝟙 g₂) ≫
    (𝟙 g₂ ⊗≫ g₂ ◁ adj₁.unit ⊗≫ adj₂.counit ▷ g₁ ⊗≫ 𝟙 g₁) =
      𝟙 g₁ :=
begin
  calc _ =
  𝟙 _ ⊗≫ g₁ ◁ adj₂.unit ⊗≫ (adj₁.counit ▷ (g₂ ≫ 𝟙 a) ≫
    𝟙 b ◁ g₂ ◁ adj₁.unit) ⊗≫ adj₂.counit ▷ g₁ ⊗≫ 𝟙 _ : _
  ... =
  𝟙 _ ⊗≫ g₁ ◁ (adj₂.unit ▷ 𝟙 a ≫ (f ≫ g₂) ◁ adj₁.unit) ⊗≫
    (adj₁.counit ▷ (g₂ ≫ f) ≫ 𝟙 b ◁ adj₂.counit) ▷ g₁ ⊗≫ 𝟙 _ : _
  ... =
  𝟙 _ ⊗≫ g₁ ◁ adj₁.unit ⊗≫ g₁ ◁ (adj₂.unit ▷ f ⊗≫
    f ◁ adj₂.counit) ▷ g₁ ⊗≫ adj₁.counit ▷ g₁ ⊗≫ 𝟙 _ : _
  ... =
  𝟙 _ ⊗≫ (g₁ ◁ adj₁.unit ⊗≫ adj₁.counit ▷ g₁) ⊗≫ 𝟙 _ : _
  ... = _ : _,
  { coherence },
  { rw ←whisker_exchange, coherence },
  { simp_rw ←whisker_exchange, coherence },
  { rw left_triangle, coherence },
  { rw right_triangle, coherence },
end

lemma left_adjoint_uniq_aux {f₁ f₂ : a ⟶ b} {g : b ⟶ a} (adj₁ : f₁ ⊣ g) (adj₂ : f₂ ⊣ g) :
  (𝟙 f₁ ⊗≫ adj₂.unit ▷ f₁ ⊗≫ f₂ ◁ adj₁.counit ⊗≫ 𝟙 f₂) ≫
    (𝟙 f₂ ⊗≫ adj₁.unit ▷ f₂ ⊗≫ f₁ ◁ adj₂.counit ⊗≫ 𝟙 f₁) =
      𝟙 f₁ :=
begin
  calc _ =
  𝟙 _ ⊗≫ adj₂.unit ▷ f₁ ⊗≫ (𝟙 a ◁ f₂ ◁ adj₁.counit ≫
    adj₁.unit ▷ (f₂ ≫ 𝟙 b)) ⊗≫ f₁ ◁ adj₂.counit ⊗≫ 𝟙 _ : _
  ... =
  𝟙 _ ⊗≫ (𝟙 a ◁ adj₂.unit ≫ adj₁.unit ▷ (f₂ ≫ g)) ▷ f₁ ⊗≫
    f₁ ◁ ((g ≫ f₂) ◁ adj₁.counit ≫ adj₂.counit ▷ 𝟙 b) ⊗≫ 𝟙 _ : _
  ... =
  𝟙 _ ⊗≫ adj₁.unit ▷ f₁ ⊗≫ f₁ ◁ (g ◁ adj₂.unit ⊗≫
    adj₂.counit ▷ g) ▷ f₁ ⊗≫ f₁ ◁ adj₁.counit ⊗≫ 𝟙 _ : _
  ... =
  𝟙 _ ⊗≫ (adj₁.unit ▷ f₁ ⊗≫ f₁ ◁ adj₁.counit) ⊗≫ 𝟙 _ : _
  ... = _ : _,
  { coherence },
  { rw whisker_exchange, coherence },
  { simp_rw whisker_exchange, coherence },
  { rw right_triangle, coherence },
  { rw left_triangle, coherence },
end

/-- If `g₁` and `g₂` are both right adjoint to `f`, then they are isomorphic. -/
def right_adjoint_uniq {f : a ⟶ b} {g₁ g₂ : b ⟶ a}
  (adj₁ : f ⊣ g₁) (adj₂ : f ⊣ g₂) : g₁ ≅ g₂ :=
{ hom := 𝟙 g₁ ⊗≫ g₁ ◁ adj₂.unit ⊗≫ adj₁.counit ▷ g₂ ⊗≫ 𝟙 g₂,
  inv := 𝟙 g₂ ⊗≫ g₂ ◁ adj₁.unit ⊗≫ adj₂.counit ▷ g₁ ⊗≫ 𝟙 g₁,
  hom_inv_id' := right_adjoint_uniq_aux adj₁ adj₂,
  inv_hom_id' := right_adjoint_uniq_aux adj₂ adj₁ }

/-- If `f₁` and `f₂` are both left adjoint to `g`, then they are isomorphic. -/
def left_adjoint_uniq {f₁ f₂ : a ⟶ b} {g : b ⟶ a}
  (adj₁ : f₁ ⊣ g) (adj₂ : f₂ ⊣ g) : f₁ ≅ f₂ :=
{ hom := 𝟙 f₁ ⊗≫ adj₂.unit ▷ f₁ ⊗≫ f₂ ◁ adj₁.counit ⊗≫ 𝟙 f₂,
  inv := 𝟙 f₂ ⊗≫ adj₁.unit ▷ f₂ ⊗≫ f₁ ◁ adj₂.counit ⊗≫ 𝟙 f₁,
  hom_inv_id' := left_adjoint_uniq_aux adj₁ adj₂,
  inv_hom_id' := left_adjoint_uniq_aux adj₂ adj₁ }

section composition
variables {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}

/-- Auxiliary definition for `adjunction.comp`. -/
@[simp]
def comp_unit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : 𝟙 a ⟶ (f₁ ≫ f₂) ≫ g₂ ≫ g₁ :=
𝟙 _ ⊗≫ adj₁.unit ⊗≫ f₁ ◁ adj₂.unit ▷ g₁ ⊗≫ 𝟙 _

/-- Auxiliary definition for `adjunction.comp`. -/
@[simp]
def comp_counit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : (g₂ ≫ g₁) ≫ f₁ ≫ f₂ ⟶ 𝟙 c :=
𝟙 _ ⊗≫ g₂ ◁ adj₁.counit ▷ f₂ ⊗≫ adj₂.counit ⊗≫ 𝟙 _

lemma comp_left_triangle_aux (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
  left_zigzag (comp_unit adj₁ adj₂) (comp_counit adj₁ adj₂) = (λ_ _).hom ≫ (ρ_ _).inv :=
begin
  calc _ =
  𝟙 _ ⊗≫ adj₁.unit ▷ (f₁ ≫ f₂) ⊗≫ f₁ ◁ (adj₂.unit ▷ (g₁ ≫ f₁) ≫
    (f₂ ≫ g₂) ◁ adj₁.counit) ▷ f₂ ⊗≫ (f₁ ≫ f₂) ◁ adj₂.counit ⊗≫ 𝟙 _ : _
  ... =
  𝟙 _ ⊗≫ (adj₁.unit ▷ f₁ ⊗≫ f₁ ◁ adj₁.counit) ▷ f₂ ⊗≫
    f₁ ◁ (adj₂.unit ▷ f₂ ⊗≫ f₂ ◁ adj₂.counit) ⊗≫ 𝟙 _ : _
  ... = _ : _,
  { dsimp, coherence },
  { rw ←whisker_exchange, coherence },
  { simp_rw left_triangle, coherence }
end

lemma comp_right_triangle_aux (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
  right_zigzag (comp_unit adj₁ adj₂) (comp_counit adj₁ adj₂) = (ρ_ _).hom ≫ (λ_ _).inv :=
begin
  calc _ =
  𝟙 _ ⊗≫ (g₂ ≫ g₁) ◁ adj₁.unit ⊗≫ g₂ ◁ ((g₁ ≫ f₁) ◁ adj₂.unit ≫
    adj₁.counit ▷ (f₂ ≫ g₂)) ▷ g₁ ⊗≫ adj₂.counit ▷ (g₂ ≫ g₁) ⊗≫ 𝟙 _: _
  ... =
  𝟙 _ ⊗≫ g₂ ◁ (g₁ ◁ adj₁.unit ⊗≫ adj₁.counit ▷ g₁) ⊗≫
    (g₂ ◁ adj₂.unit ⊗≫ adj₂.counit ▷ g₂) ▷ g₁ ⊗≫ 𝟙 _ : _
  ... = _ : _,
  { dsimp, coherence },
  { rw whisker_exchange, coherence },
  { simp_rw right_triangle, coherence }
end

/-- Composition of adjunctions. -/
def comp (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : f₁ ≫ f₂ ⊣ g₂ ≫ g₁ :=
{ unit            := comp_unit adj₁ adj₂,
  counit          := comp_counit adj₁ adj₂,
  left_triangle'  := by apply comp_left_triangle_aux,
  right_triangle' := by apply comp_right_triangle_aux }

end composition

end adjunction

section
noncomputable theory
-- In this section we convert an arbitrary equivalence to a half-adjoint equivalence.

variables (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b)

@[simp]
def left_zigzag_iso (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :=
whisker_right_iso η f ≪⊗≫ whisker_left_iso f ε

@[simp]
def right_zigzag_iso (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :=
whisker_left_iso g η ≪⊗≫ whisker_right_iso ε g

lemma left_zigzag_iso_hom  : (left_zigzag_iso  η ε).hom = left_zigzag  η.hom ε.hom := rfl
lemma right_zigzag_iso_hom : (right_zigzag_iso η ε).hom = right_zigzag η.hom ε.hom := rfl
lemma left_zigzag_iso_inv  : (left_zigzag_iso  η ε).inv = right_zigzag ε.inv η.inv :=
by simp [bicategorical_comp, bicategorical_iso_comp]
lemma right_zigzag_iso_inv : (right_zigzag_iso η ε).inv = left_zigzag  ε.inv η.inv :=
by simp [bicategorical_comp, bicategorical_iso_comp]
lemma left_zigzag_iso_symm  : (left_zigzag_iso  η ε).symm = right_zigzag_iso ε.symm η.symm :=
iso.ext (left_zigzag_iso_inv η ε)
lemma right_zigzag_iso_symm : (right_zigzag_iso η ε).symm = left_zigzag_iso  ε.symm η.symm :=
iso.ext (right_zigzag_iso_inv η ε)

lemma right_triangle_of_left_triangle {η : 𝟙 a ≅ f ≫ g} {ε : g ≫ f ≅ 𝟙 b} :
  left_zigzag_iso η ε = λ_ f ≪≫ (ρ_ f).symm → right_zigzag_iso η ε = ρ_ g ≪≫ (λ_ g).symm :=
begin
  intros H,
  replace H : left_zigzag η.hom ε.hom = (λ_ f).hom ≫ (ρ_ f).inv := congr_arg iso.hom H,
  apply iso.ext,
  dsimp [bicategorical_iso_comp] at H ⊢,
  calc _ =
  𝟙 _ ⊗≫ g ◁ η.hom ⊗≫ ε.hom ▷ g ⊗≫ 𝟙 (g ≫ 𝟙 a) ⊗≫ 𝟙 _ : _
  ... =
  𝟙 _ ⊗≫ g ◁ η.hom ⊗≫ ε.hom ▷ g ⊗≫ g ◁ (η.hom ≫ η.inv) ⊗≫ 𝟙 _ : _
  ... =
  𝟙 _ ⊗≫ g ◁ η.hom ⊗≫ ε.hom ▷ g ⊗≫ g ◁ η.hom ⊗≫ (ε.hom ≫ ε.inv) ▷ g ⊗≫ g ◁ η.inv ⊗≫ 𝟙 _ : _
  ... =
  𝟙 _ ⊗≫ g ◁ η.hom ⊗≫ (ε.hom ▷ (g ≫ 𝟙 a) ≫ 𝟙 b ◁ g ◁ η.hom) ⊗≫
    ε.hom ▷ g ⊗≫ ε.inv ▷ g ⊗≫ g ◁ η.inv ⊗≫ 𝟙 _ : _
  ... =
  𝟙 _ ⊗≫ g ◁ (η.hom ▷ 𝟙 a ≫ (f ≫ g) ◁ η.hom) ⊗≫ ε.hom ▷ (g ≫ f ≫ g) ⊗≫
    ε.hom ▷ g ⊗≫ ε.inv ▷ g ⊗≫ g ◁ η.inv ⊗≫ 𝟙 _ : _
  ... =
  𝟙 _ ⊗≫ g ◁ η.hom ⊗≫ g ◁ η.hom ▷ f ▷ g ⊗≫ (ε.hom ▷ (g ≫ f) ≫ 𝟙 b ◁ ε.hom) ▷ g ⊗≫
    ε.inv ▷ g ⊗≫ g ◁ η.inv ⊗≫ 𝟙 _ : _
  ... =
  𝟙 _ ⊗≫ g ◁ η.hom ⊗≫ g ◁ (η.hom ▷ f ⊗≫ f ◁ ε.hom) ▷ g ⊗≫
    ε.hom ▷ g ⊗≫ ε.inv ▷ g ⊗≫ g ◁ η.inv ⊗≫ 𝟙 _ : _
  ... =
  𝟙 _ ⊗≫ g ◁ η.hom ⊗≫ (ε.hom ≫ ε.inv) ▷ g ⊗≫ g ◁ η.inv ⊗≫ 𝟙 _ : _
  ... =
  𝟙 _ ⊗≫ g ◁ (η.hom ≫ η.inv) ⊗≫ 𝟙 _ : _
  ... = _ : _,
  { rw [←comp_id (ε.hom ▷ g)], coherence },
  { rw [iso.hom_inv_id η, whisker_left_id] },
  { rw [iso.hom_inv_id ε], coherence },
  { coherence },
  { rw ←whisker_exchange, coherence },
  { rw ←whisker_exchange, coherence },
  { rw ←whisker_exchange, coherence },
  { rw H, coherence },
  { rw iso.hom_inv_id ε, coherence },
  { rw iso.hom_inv_id η, coherence },
end

lemma left_triangle_iff_right_triangle {η : 𝟙 a ≅ f ≫ g} {ε : g ≫ f ≅ 𝟙 b} :
  left_zigzag_iso η ε = λ_ f ≪≫ (ρ_ f).symm ↔ right_zigzag_iso η ε = ρ_ g ≪≫ (λ_ g).symm :=
iff.intro right_triangle_of_left_triangle
begin
  intros H,
  rw ←iso.symm_eq_iff at H ⊢,
  rw left_zigzag_iso_symm,
  rw right_zigzag_iso_symm at H,
  exact right_triangle_of_left_triangle H
end

def adjointify_unit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : 𝟙 a ≅ f ≫ g :=
η ≪≫ whisker_right_iso ((ρ_ f).symm ≪≫ right_zigzag_iso ε.symm η.symm ≪≫ λ_ f) g

def adjointify_counit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : g ≫ f ≅ 𝟙 b :=
whisker_left_iso g ((ρ_ f).symm ≪≫ right_zigzag_iso ε.symm η.symm ≪≫ λ_ f) ≪≫ ε

@[simp]
lemma adjointify_counit_symm (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
  (adjointify_counit η ε).symm = adjointify_unit ε.symm η.symm :=
begin
  apply iso.ext,
  rw [←cancel_mono (adjointify_unit ε.symm η.symm).inv, iso.hom_inv_id],
  dsimp [adjointify_unit, adjointify_counit, bicategorical_iso_comp],
  simp only [id_whisker_right, id_comp, is_iso.iso.inv_inv],
  calc _ =
  ε.inv ⊗≫ g ◁ η.hom ▷ f ⊗≫ (𝟙 b ◁ (g ≫ f) ◁ ε.hom ≫ ε.inv ▷ ((g ≫ f) ≫ 𝟙 b)) ⊗≫
    (g ◁ η.inv) ▷ f ⊗≫ ε.hom : _
  ... =
  ε.inv ⊗≫ (𝟙 b ◁ g ◁ η.hom ≫ ε.inv ▷ (g ≫ f ≫ g)) ▷ f ⊗≫ g ◁
    ((f ≫ g) ◁ f ◁ ε.hom ≫ η.inv ▷ (f ≫ 𝟙 b)) ⊗≫ ε.hom : _
  ...=
  ε.inv ⊗≫ ε.inv ▷ g ▷ f ⊗≫ g ◁ ((f ≫ g) ◁ η.hom ≫ η.inv ▷ (f ≫ g)) ▷ f ⊗≫
    g ◁ f ◁ ε.hom ⊗≫ ε.hom : _
  ... =
  ε.inv ⊗≫ ε.inv ▷ g ▷ f ⊗≫ g ◁ (η.inv ≫ η.hom) ▷ f ⊗≫ g ◁ f ◁ ε.hom ⊗≫ ε.hom : _
  ... =
  ε.inv ⊗≫ (ε.inv ▷ (g ≫ f) ≫ (g ≫ f) ◁ ε.hom) ⊗≫ ε.hom : _
  ... =
  ε.inv ⊗≫ (ε.hom ≫ ε.inv) ⊗≫ ε.hom : _
  ... =
  ε.inv ≫ ε.hom : _
  ... = _ : _ ,
  sorry; { coherence },
  sorry; { rw [whisker_exchange], coherence },
  { rw [whisker_exchange, whisker_exchange],
    tactic.coherence.assoc_simps,
    tactic.coherence.liftable_prefixes,
    congr' 3, pure_coherence,
    congr' 2, pure_coherence,
    congr' 2, pure_coherence,
    congr' 2, pure_coherence,
    congr' 2, pure_coherence },
  { rw [whisker_exchange], coherence },
  { rw [iso.inv_hom_id], coherence },
  { rw [←whisker_exchange], coherence },
  { rw [iso.hom_inv_id], coherence },
  { rw [iso.inv_hom_id] }
end

@[simp]
lemma adjointify_unit_symm (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
  (adjointify_unit η ε).symm = adjointify_counit ε.symm η.symm :=
iso.symm_eq_iff.mpr (adjointify_counit_symm ε.symm η.symm).symm

lemma adjointify_counit_left_triangle (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
  left_zigzag_iso η (adjointify_counit η ε) = λ_ f ≪≫ (ρ_ f).symm :=
begin
  sorry
end

lemma adjointify_unit_right_triangle (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
  right_zigzag_iso (adjointify_unit η ε) ε = ρ_ g ≪≫ (λ_ g).symm :=
begin
  rw [←iso.symm_eq_iff, right_zigzag_iso_symm, adjointify_unit_symm],
  exact adjointify_counit_left_triangle ε.symm η.symm
end

structure equivalence (a b : B) :=
(hom : a ⟶ b)
(inv : b ⟶ a)
(unit   : 𝟙 a ≅ hom ≫ inv)
(counit : inv ≫ hom ≅ 𝟙 b)
(left_triangle' : left_zigzag_iso unit counit = λ_ hom ≪≫ (ρ_ hom).symm . obviously)

localized "infixr ` ≌ `:10  := equivalence" in bicategory

namespace equivalence

restate_axiom left_triangle'
attribute [simp] left_triangle

@[simp]
lemma right_triangle (f : a ≌ b) :
  whisker_left_iso f.inv f.unit ≪⊗≫ whisker_right_iso f.counit f.inv =
    ρ_ f.inv ≪≫ (λ_ f.inv).symm :=
right_triangle_of_left_triangle f.left_triangle

def id (a : B) : a ≌ a :=
⟨_, _, (ρ_ _).symm, ρ_ _, by { ext, dsimp [bicategorical_iso_comp], coherence }⟩

instance : inhabited (equivalence a a) := ⟨id a⟩

definition mk_of_adjointify_counit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : a ≌ b :=
{ hom     := f,
  inv     := g,
  unit    := η,
  counit  := adjointify_counit η ε,
  left_triangle' := adjointify_counit_left_triangle η ε }

definition mk_of_adjointify_unit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : a ≌ b :=
{ hom     := f,
  inv     := g,
  unit    := adjointify_unit η ε,
  counit  := ε,
  left_triangle' := left_triangle_iff_right_triangle.mpr (adjointify_unit_right_triangle η ε) }

end equivalence

def adjunction.of_equivalence (f : a ≌ b) : f.hom ⊣ f.inv :=
{ unit   := f.unit.hom,
  counit := f.counit.hom,
  left_triangle'  := congr_arg iso.hom f.left_triangle,
  right_triangle' := congr_arg iso.hom f.right_triangle }

def adjunction.of_equivalence_symm (f : a ≌ b) : f.inv ⊣ f.hom :=
{ unit   := f.counit.inv,
  counit := f.unit.inv,
  left_triangle'  := right_zigzag_iso_inv f.unit f.counit ▸ congr_arg iso.inv f.right_triangle,
  right_triangle' := left_zigzag_iso_inv  f.unit f.counit ▸ congr_arg iso.inv f.left_triangle }

end

end bicategory

end category_theory
