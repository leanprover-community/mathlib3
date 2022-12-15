import category_theory.limits.preserves.shapes.zero

/-!

# Short complexes

If `C` is a category that has zero morphisms, we introduce the category
`short_complex C`. Objects `S : short_complex C` consist of composable
morphisms `S.f : S.X₁ ⟶ S.X₂` and `S.g : S.X₂ ⟶ S.X₃` such that
the composition `S.f ≫ S.g` is zero.

TODO: refactor exact sequences and homology in mathlib using this category.

-/

namespace category_theory

open limits category

open_locale zero_object

variables (C D : Type*) [category C] [category D]

/-- A short complex in a category `C` with zero morphisms is the datum
of two composable morphisms `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` such that
`f ≫ g = 0`. -/
structure short_complex [has_zero_morphisms C] :=
{X₁ X₂ X₃ : C}
(f : X₁ ⟶ X₂)
(g : X₂ ⟶ X₃)
(zero : f ≫ g = 0)

variables {C} [has_zero_morphisms C] [has_zero_morphisms D]

namespace short_complex

noncomputable instance [has_zero_object C] : inhabited (short_complex C) :=
⟨short_complex.mk (0 : 0 ⟶ 0) (0 : 0 ⟶ 0) comp_zero⟩

attribute [simp, reassoc] zero

/-- Morphisms of short complexes are the commutative diagrams of the obvious shape. -/
@[ext]
structure hom (S₁ S₂ : short_complex C) :=
(τ₁ : S₁.X₁ ⟶ S₂.X₁)
(τ₂ : S₁.X₂ ⟶ S₂.X₂)
(τ₃ : S₁.X₃ ⟶ S₂.X₃)
(comm₁₂' : τ₁ ≫ S₂.f = S₁.f ≫ τ₂ . obviously)
(comm₂₃' : τ₂ ≫ S₂.g = S₁.g ≫ τ₃ . obviously)

restate_axiom hom.comm₁₂'
restate_axiom hom.comm₂₃'
attribute [reassoc] hom.comm₁₂ hom.comm₂₃
local attribute [simp] hom.comm₁₂ hom.comm₂₃ hom.comm₁₂_assoc hom.comm₂₃_assoc

variables (S : short_complex C) {S₁ S₂ S₃ : short_complex C}

/-- The identity morphism of a short complex. -/
@[simps]
def hom.id : hom S S := { τ₁ := 𝟙 _, τ₂ :=  𝟙 _, τ₃ := 𝟙 _ }

instance : inhabited (hom S S) := ⟨hom.id S⟩

/-- The composition of morphisms of short complexes. -/
@[simps]
def hom.comp (φ₁₂ : hom S₁ S₂) (φ₂₃ : hom S₂ S₃) : hom S₁ S₃ :=
{ τ₁ := φ₁₂.τ₁ ≫ φ₂₃.τ₁,
  τ₂ := φ₁₂.τ₂ ≫ φ₂₃.τ₂,
  τ₃ := φ₁₂.τ₃ ≫ φ₂₃.τ₃, }

instance : category (short_complex C) :=
{ hom := hom,
  id := hom.id,
  comp := λ S₁ S₂ S₃, hom.comp, }

/-- A constructor for morphisms in `short_complex C` when the commutativity conditions
are not obvious. -/
@[simps]
def hom.mk' {S₁ S₂ : short_complex C} (τ₁ : S₁.X₁ ⟶ S₂.X₁) (τ₂ : S₁.X₂ ⟶ S₂.X₂)
  (τ₃ : S₁.X₃ ⟶ S₂.X₃) (comm₁₂ : τ₁ ≫ S₂.f = S₁.f ≫ τ₂)
  (comm₂₃ : τ₂ ≫ S₂.g = S₁.g ≫ τ₃) : S₁ ⟶ S₂ :=
⟨τ₁, τ₂, τ₃, comm₁₂, comm₂₃⟩

@[simp] lemma id_τ₁ : hom.τ₁ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_τ₂ : hom.τ₂ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_τ₃ : hom.τ₃ (𝟙 S) = 𝟙 _ := rfl
@[reassoc] lemma comp_τ₁ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) : (φ₁₂ ≫ φ₂₃).τ₁ = φ₁₂.τ₁ ≫ φ₂₃.τ₁ := rfl
@[reassoc] lemma comp_τ₂ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) : (φ₁₂ ≫ φ₂₃).τ₂ = φ₁₂.τ₂ ≫ φ₂₃.τ₂ := rfl
@[reassoc] lemma comp_τ₃ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) : (φ₁₂ ≫ φ₂₃).τ₃ = φ₁₂.τ₃ ≫ φ₂₃.τ₃ := rfl
attribute [simp] comp_τ₁ comp_τ₂ comp_τ₃

instance : has_zero (S₁ ⟶ S₂) := ⟨{ τ₁ := 0, τ₂ := 0, τ₃ := 0, }⟩

variables (S₁ S₂)
@[simp] lemma zero_τ₁ : hom.τ₁ (0 : S₁ ⟶ S₂) = 0 := rfl
@[simp] lemma zero_τ₂ : hom.τ₂ (0 : S₁ ⟶ S₂) = 0 := rfl
@[simp] lemma zero_τ₃ : hom.τ₃ (0 : S₁ ⟶ S₂) = 0 := rfl
variables {S₁ S₂}

instance : has_zero_morphisms (short_complex C) := { }

/-- The first projection functor `short_complex C ⥤ C`. -/
@[simps]
def π₁ : short_complex C ⥤ C :=
{ obj := λ S, S.X₁,
  map := λ S₁ S₂ f, f.τ₁, }

/-- The second projection functor `short_complex C ⥤ C`. -/
@[simps]
def π₂ : short_complex C ⥤ C :=
{ obj := λ S, S.X₂,
  map := λ S₁ S₂ f, f.τ₂, }

/-- The third projection functor `short_complex C ⥤ C`. -/
@[simps]
def π₃ : short_complex C ⥤ C :=
{ obj := λ S, S.X₃,
  map := λ S₁ S₂ f, f.τ₃, }

instance π₁_preserves_zero_morphisms :
  functor.preserves_zero_morphisms (π₁ : _ ⥤ C) := { }
instance π₂_preserves_zero_morphisms :
  functor.preserves_zero_morphisms (π₂ : _ ⥤ C) := { }
instance π₃_preserves_zero_morphisms :
  functor.preserves_zero_morphisms (π₃ : _ ⥤ C) := { }

instance (f : S₁ ⟶ S₂) [is_iso f] : is_iso f.τ₁ :=
by { change is_iso (π₁.map_iso (as_iso f)).hom, apply_instance, }
instance (f : S₁ ⟶ S₂) [is_iso f] : is_iso f.τ₂ :=
by { change is_iso (π₂.map_iso (as_iso f)).hom, apply_instance, }
instance (f : S₁ ⟶ S₂) [is_iso f] : is_iso f.τ₃ :=
by { change is_iso (π₃.map_iso (as_iso f)).hom, apply_instance, }

/-- The natural transformation `π₁ ⟶ π₂` induced by `S.f` for all `S : short_complex C`. -/
@[simps]
def π₁_to_π₂ : (π₁ : _ ⥤ C) ⟶ π₂ := { app := λ S, S.f, }

/-- The natural transformation `π₂ ⟶ π₃` induced by `S.g` for all `S : short_complex C`. -/
@[simps]
def π₂_to_π₃ : (π₂ : _ ⥤ C) ⟶ π₃ := { app := λ S, S.g, }

@[simp, reassoc]
lemma π₁_to_π₂_comp_π₂_to_π₃ : (π₁_to_π₂ : (_ : _ ⥤ C) ⟶ _) ≫ π₂_to_π₃ = 0 :=
by { ext, apply short_complex.zero, }

variables {C D}

/-- The short complex in `D` obtained by applying a functor `F : C ⥤ D` to a
short complex in `C`, assuming that `F` preserves zero morphisms. -/
@[simps]
def map (F : C ⥤ D) [F.preserves_zero_morphisms] : short_complex D :=
short_complex.mk (F.map S.f) (F.map S.g) (by rw [← F.map_comp, S.zero, F.map_zero])

/-- The morphism of short complexes `S.map F ⟶ S.map G` induced by
a natural transformation `F ⟶ G`. -/
@[simps]
def map_nat_trans {F G : C ⥤ D} [F.preserves_zero_morphisms]
  [G.preserves_zero_morphisms] (τ : F ⟶ G) : S.map F ⟶ S.map G :=
{ τ₁ := τ.app _,
  τ₂ := τ.app _,
  τ₃ := τ.app _, }

/-- The isomorphism of short complexes `S.map F ≅ S.map G` induced by
a natural isomorphism `F ≅ G`. -/
--@[simps]
def map_nat_iso {F G : C ⥤ D} [F.preserves_zero_morphisms]
  [G.preserves_zero_morphisms] (τ : F ≅ G) : S.map F ≅ S.map G :=
{ hom := S.map_nat_trans τ.hom,
  inv := S.map_nat_trans τ.inv, }

/-- The functor `short_complex C ⥤ short_complex D` induced by a functor `C ⥤ D` which
preserves zero morphisms. -/
@[simps]
def _root_.category_theory.functor.map_short_complex
  (F : C ⥤ D) [F.preserves_zero_morphisms] :
  short_complex C ⥤ short_complex D :=
{ obj := λ S, S.map F,
  map := λ S₁ S₂ φ, ⟨F.map φ.τ₁, F.map φ.τ₂, F.map φ.τ₃,
    by { dsimp, simp only [← F.map_comp, φ.comm₁₂], },
    by { dsimp, simp only [← F.map_comp, φ.comm₂₃], }⟩ }

/-- A constructor for isomorphisms in the category `short_complex C`-/
@[simps]
def mk_iso (e₁ : S₁.X₁ ≅ S₂.X₁) (e₂ : S₁.X₂ ≅ S₂.X₂) (e₃ : S₁.X₃ ≅ S₂.X₃)
  (comm₁₂ : e₁.hom ≫ S₂.f = S₁.f ≫ e₂.hom) (comm₂₃ : e₂.hom ≫ S₂.g = S₁.g ≫ e₃.hom) :
  S₁ ≅ S₂ :=
{ hom := ⟨e₁.hom, e₂.hom, e₃.hom, comm₁₂, comm₂₃⟩,
  inv := hom.mk' e₁.inv e₂.inv e₃.inv
    (by simp only [← cancel_mono e₂.hom, assoc, e₂.inv_hom_id, comp_id,
      ← comm₁₂, e₁.inv_hom_id_assoc])
    (by simp only [← cancel_mono e₃.hom, assoc, e₃.inv_hom_id, comp_id,
      ← comm₂₃, e₂.inv_hom_id_assoc]), }

/-- The opposite short_complex in `Cᵒᵖ` associated to a short complex in `C`. -/
@[simps]
def op : short_complex Cᵒᵖ :=
mk S.g.op S.f.op (by simpa only [← op_comp, S.zero])

/-- The opposite morphism in `short_complex Cᵒᵖ` associated to a morphism in `short_complex C` -/
@[simps]
def op_map (φ : S₁ ⟶ S₂) : S₂.op ⟶ S₁.op :=
⟨φ.τ₃.op, φ.τ₂.op, φ.τ₁.op,
  by { dsimp, simp only [← op_comp, φ.comm₂₃], },
  by { dsimp, simp only [← op_comp, φ.comm₁₂], }⟩

/-- The short_complex in `C` associated to a short complex in `Cᵒᵖ`. -/
@[simps]
def unop (S : short_complex Cᵒᵖ) : short_complex C :=
mk S.g.unop S.f.unop (by simpa only [← unop_comp, S.zero])

/-- The morphism in `short_complex C` associated to a morphism in `short_complex Cᵒᵖ` -/
@[simps]
def unop'_map {S₁ S₂ : short_complex Cᵒᵖ} (φ : S₁ ⟶ S₂) : S₂.unop ⟶ S₁.unop :=
⟨φ.τ₃.unop, φ.τ₂.unop, φ.τ₁.unop,
  by { dsimp, simp only [← unop_comp, φ.comm₂₃], },
  by { dsimp, simp only [← unop_comp, φ.comm₁₂], }⟩

/-- The morphism in `short_complex C` associated to a morphism in `short_complex Cᵒᵖ` -/
@[simps]
def unop_map {S₁ S₂ : short_complex C} (φ : S₁.op ⟶ S₂.op) : S₂ ⟶ S₁ :=
⟨φ.τ₃.unop, φ.τ₂.unop, φ.τ₁.unop, quiver.hom.op_inj φ.comm₂₃.symm,
  quiver.hom.op_inj φ.comm₁₂.symm⟩

/-- The obvious isomorphism `S.op.unop ≅ S` for `S : short_complex C`. -/
@[simps]
def op_unop : S.op.unop ≅ S :=
mk_iso (iso.refl _) (iso.refl _) (iso.refl _) (by tidy) (by tidy)

/-- The obvious isomorphism `S.unop.op ≅ S` for `S : short_complex Cᵒᵖ`. -/
@[simps]
def unop_op (S : short_complex Cᵒᵖ) : S.unop.op ≅ S :=
mk_iso (iso.refl _) (iso.refl _) (iso.refl _) (by tidy) (by tidy)

variable (C)

/-- The obvious functor `(short_complex C)ᵒᵖ ⥤ short_complex Cᵒᵖ`. -/
@[simps]
def op_functor : (short_complex C)ᵒᵖ ⥤ short_complex Cᵒᵖ :=
{ obj := λ S, (opposite.unop S).op,
  map := λ S₁ S₂ φ, op_map φ.unop, }

/-- The obvious functor `short_complex Cᵒᵖ ⥤ (short_complex C)ᵒᵖ`. -/
@[simps]
def unop_functor : short_complex Cᵒᵖ ⥤ (short_complex C)ᵒᵖ :=
{ obj := λ S, opposite.op (unop S),
  map := λ S₁ S₂ φ, (unop'_map φ).op, }

/-- The obvious equivalence of categories `(short_complex C)ᵒᵖ ≌ short_complex Cᵒᵖ`. -/
@[simps]
def op_equiv : (short_complex C)ᵒᵖ ≌ short_complex Cᵒᵖ :=
{ functor := op_functor C,
  inverse := unop_functor C,
  unit_iso := nat_iso.of_components (λ S, (op_unop (opposite.unop S)).op)
    (λ S₁ S₂ f, quiver.hom.unop_inj (by tidy)),
  counit_iso := nat_iso.of_components (unop_op) (by tidy), }

end short_complex

end category_theory
