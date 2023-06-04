import category_theory.preadditive.basic
import category_theory.abelian.projective
import category_theory.abelian.diagram_lemmas.four

import data.matrix.notation

import .abelian_category
import .fin_functor
import .split_exact

noncomputable theory

open category_theory
open category_theory.limits
open category_theory.preadditive

universes v u

namespace category_theory
variables (𝒞 : Type u) [category.{v} 𝒞]

@[ext]
structure short_exact_sequence [has_images 𝒞] [has_zero_morphisms 𝒞] [has_kernels 𝒞] :=
(fst snd trd : 𝒞)
(f : fst ⟶ snd)
(g : snd ⟶ trd)
[mono'  : mono f]
[epi'   : epi g]
(exact' : exact f g)

namespace short_exact_sequence

attribute [instance] mono' epi'

variables {𝒞} [has_images 𝒞] [has_zero_morphisms 𝒞] [has_kernels 𝒞]

@[simp, reassoc] lemma f_comp_g (A : short_exact_sequence 𝒞) : A.f ≫ A.g = 0 := A.exact'.w

@[ext]
structure hom (A B : short_exact_sequence 𝒞) :=
(fst : A.1 ⟶ B.1)
(snd : A.2 ⟶ B.2)
(trd : A.3 ⟶ B.3)
(sq1' : fst ≫ B.f = A.f ≫ snd . obviously)
(sq2' : snd ≫ B.g = A.g ≫ trd . obviously)

namespace hom

restate_axiom sq1' sq1
restate_axiom sq2' sq2

attribute [reassoc] sq1 sq2

end hom

instance : quiver (short_exact_sequence 𝒞) := ⟨hom⟩

def id (A : short_exact_sequence 𝒞) : A ⟶ A :=
{ fst := 𝟙 _,
  snd := 𝟙 _,
  trd := 𝟙 _,
  sq1' := by simp only [category.id_comp, category.comp_id],
  sq2' := by simp only [category.id_comp, category.comp_id], }

def comp {A B C : short_exact_sequence 𝒞} (f : A ⟶ B) (g : B ⟶ C) : A ⟶ C :=
{ fst := f.1 ≫ g.1,
  snd := f.2 ≫ g.2,
  trd := f.3 ≫ g.3,
  sq1' := by rw [category.assoc, hom.sq1, hom.sq1_assoc],
  sq2' := by rw [category.assoc, hom.sq2, hom.sq2_assoc], }

instance : category (short_exact_sequence 𝒞) :=
{ id := id,
  comp := λ A B C f g, comp f g,
  id_comp' := by { intros, ext; dsimp; apply category.id_comp, },
  comp_id' := by { intros, ext; dsimp; apply category.comp_id, },
  assoc' := by { intros, ext; dsimp; apply category.assoc, },
  .. (infer_instance : quiver (short_exact_sequence 𝒞)) }

@[simp] lemma id_fst (A : short_exact_sequence 𝒞) : hom.fst (𝟙 A) = 𝟙 A.1 := rfl
@[simp] lemma id_snd (A : short_exact_sequence 𝒞) : hom.snd (𝟙 A) = 𝟙 A.2 := rfl
@[simp] lemma id_trd (A : short_exact_sequence 𝒞) : hom.trd (𝟙 A) = 𝟙 A.3 := rfl

variables {A B C : short_exact_sequence 𝒞} (f : A ⟶ B) (g : B ⟶ C)

@[simp, reassoc] lemma comp_fst : (f ≫ g).1 = f.1 ≫ g.1 := rfl
@[simp, reassoc] lemma comp_snd : (f ≫ g).2 = f.2 ≫ g.2 := rfl
@[simp, reassoc] lemma comp_trd : (f ≫ g).3 = f.3 ≫ g.3 := rfl

variables (𝒞)

@[simps] def Fst : short_exact_sequence 𝒞 ⥤ 𝒞 :=
{ obj := fst, map := λ A B f, f.1 }

@[simps] def Snd : short_exact_sequence 𝒞 ⥤ 𝒞 :=
{ obj := snd, map := λ A B f, f.2 }

@[simps] def Trd : short_exact_sequence 𝒞 ⥤ 𝒞 :=
{ obj := trd, map := λ A B f, f.3 }

@[simps] def f_nat : Fst 𝒞 ⟶ Snd 𝒞 :=
{ app := λ A, A.f,
  naturality' := λ A B f, f.sq1 }

@[simps] def g_nat : Snd 𝒞 ⟶ Trd 𝒞 :=
{ app := λ A, A.g,
  naturality' := λ A B f, f.sq2 }

instance : has_zero_morphisms (short_exact_sequence 𝒞) :=
{ has_zero := λ A B, ⟨{ fst := 0, snd := 0, trd := 0 }⟩,
  comp_zero' := by { intros, ext; apply comp_zero },
  zero_comp' := by { intros, ext; apply zero_comp }, }
.

@[simp] lemma hom_zero_fst : (0 : A ⟶ B).1 = 0 := rfl

@[simp] lemma hom_zero_snd : (0 : A ⟶ B).2 = 0 := rfl

@[simp] lemma hom_zero_trd : (0 : A ⟶ B).3 = 0 := rfl

variables {𝒞}

protected def functor (A : short_exact_sequence 𝒞) : fin 3 ⥤ 𝒞 :=
fin3_functor_mk ![A.1, A.2, A.3] A.f A.g

def functor_map {A B : short_exact_sequence 𝒞} (f : A ⟶ B) :
  Π i, A.functor.obj i ⟶ B.functor.obj i
| ⟨0,h⟩ := f.1
| ⟨1,h⟩ := f.2
| ⟨2,h⟩ := f.3
| ⟨i+3,hi⟩ := by { exfalso, revert hi, dec_trivial }

meta def aux_tac : tactic unit :=
`[simp only [hom_of_le_refl, functor.map_id, category.id_comp, category.comp_id]]

lemma functor_map_naturality {A B : short_exact_sequence 𝒞} (f : A ⟶ B) :
  ∀ (i j : fin 3) (hij : i ≤ j),
    functor_map f i ≫ B.functor.map hij.hom = A.functor.map hij.hom ≫ functor_map f j
| ⟨0,hi⟩ ⟨0,hj⟩ hij := by aux_tac
| ⟨1,hi⟩ ⟨1,hj⟩ hij := by aux_tac
| ⟨2,hi⟩ ⟨2,hj⟩ hij := by aux_tac
| ⟨0,hi⟩ ⟨1,hj⟩ hij := f.sq1
| ⟨1,hi⟩ ⟨2,hj⟩ hij := f.sq2
| ⟨i+3,hi⟩ _ _ := by { exfalso, revert hi, dec_trivial }
| _ ⟨j+3,hj⟩ _ := by { exfalso, revert hj, dec_trivial }
| ⟨i+1,hi⟩ ⟨0,hj⟩ H := by { exfalso, revert H, dec_trivial }
| ⟨i+2,hi⟩ ⟨1,hj⟩ H := by { exfalso, revert H, dec_trivial }
| ⟨0,hi⟩ ⟨2,hj⟩ hij :=
begin
  have h01 : (0 : fin 3) ⟶ 1 := hom_of_le dec_trivial,
  have h12 : (1 : fin 3) ⟶ 2 := hom_of_le dec_trivial,
  calc functor_map f ⟨0, hi⟩ ≫ B.functor.map hij.hom
      = functor_map f ⟨0, hi⟩ ≫ B.functor.map h01 ≫ B.functor.map h12 : _
  ... = (functor_map f ⟨0, hi⟩ ≫ B.functor.map h01) ≫ B.functor.map h12 : by rw category.assoc
  ... = (A.functor.map h01 ≫ functor_map f _) ≫ B.functor.map h12 : _
  ... = A.functor.map h01 ≫ functor_map f _ ≫ B.functor.map h12 : category.assoc _ _ _
  ... = A.functor.map h01 ≫ A.functor.map h12 ≫ functor_map f _ : _
  ... = A.functor.map hij.hom ≫ functor_map f ⟨2, hj⟩ : _,
  { rw [← functor.map_comp], congr, },
  { congr' 1, exact f.sq1 },
  { congr' 1, exact f.sq2 },
  { rw [← functor.map_comp_assoc], congr, },
end

@[simps] def Functor : short_exact_sequence 𝒞 ⥤ fin 3 ⥤ 𝒞 :=
{ obj := short_exact_sequence.functor,
  map := λ A B f,
  { app := functor_map f,
    naturality' := λ i j hij, (functor_map_naturality f i j hij.le).symm },
  map_id' := λ A, by { ext i, fin_cases i; refl },
  map_comp' := λ A B C f g, by { ext i, fin_cases i; refl } }

end short_exact_sequence

namespace short_exact_sequence

variables {𝒞} [abelian 𝒞]
variables {A B C : short_exact_sequence 𝒞} (f : A ⟶ B) (g : B ⟶ C)

section iso

variables {A B C} (f g)

open_locale zero_object

/-- One form of the five lemma: if a morphism of short exact sequences has isomorphisms
as first and third component, then the second component is also an isomorphism. -/
lemma snd_is_iso (h1 : is_iso f.1) (h3 : is_iso f.3) : is_iso f.2 :=
@abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso 𝒞 _ _
  0 A.1 A.2 A.3
  0 B.1 B.2 B.3
  0 A.f A.g
  0 B.f B.g
  0 f.1 f.2 f.3 (by rw [zero_comp, zero_comp]) f.sq1 f.sq2
  0 0
  0 0 0 (by rw [comp_zero, comp_zero])
  (exact_zero_left_of_mono _)
  A.exact'
  ((epi_iff_exact_zero_right _).mp infer_instance)
  (exact_zero_left_of_mono _)
  B.exact'
  ((epi_iff_exact_zero_right _).mp infer_instance) _ _ _ _

/-- One form of the five lemma: if a morphism `f` of short exact sequences has isomorphisms
as first and third component, then `f` itself is an isomorphism. -/
lemma is_iso_of_fst_of_trd (h1 : is_iso f.1) (h3 : is_iso f.3) : is_iso f :=
{ out :=
  begin
    haveI : is_iso f.2 := snd_is_iso f h1 h3,
    refine ⟨⟨inv f.1, inv f.2, inv f.3, _, _⟩, _, _⟩,
    { dsimp, simp only [is_iso.inv_comp_eq, f.sq1_assoc, category.comp_id, is_iso.hom_inv_id], },
    { dsimp, simp only [is_iso.inv_comp_eq, f.sq2_assoc, category.comp_id, is_iso.hom_inv_id], },
    { ext; dsimp; simp only [is_iso.hom_inv_id], },
    { ext; dsimp; simp only [is_iso.inv_hom_id], },
  end }

@[simps] def iso_of_components (f₁ : A.1 ≅ B.1) (f₂ : A.2 ≅ B.2) (f₃ : A.3 ≅ B.3)
  (sq1 : f₁.hom ≫ B.f = A.f ≫ f₂.hom) (sq2 : f₂.hom ≫ B.g = A.g ≫ f₃.hom) :
  A ≅ B :=
{ hom := ⟨f₁.hom, f₂.hom, f₃.hom, sq1, sq2⟩,
  inv :=
  begin
    refine ⟨f₁.inv, f₂.inv, f₃.inv, _, _⟩; dsimp,
    rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, sq1],
    rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, sq2],
  end,
  hom_inv_id' := by { ext; apply iso.hom_inv_id, },
  inv_hom_id' := by { ext; apply iso.inv_hom_id, } }

@[simps] def iso_of_components' (f₁ : A.1 ≅ B.1) (f₂ : A.2 ⟶ B.2) (f₃ : A.3 ≅ B.3)
  (sq1 : f₁.hom ≫ B.f = A.f ≫ f₂) (sq2 : f₂ ≫ B.g = A.g ≫ f₃.hom) :
  A ≅ B :=
let F : A ⟶ B := ⟨f₁.hom, f₂, f₃.hom, sq1, sq2⟩ in
{ hom := F,
  inv :=
  begin
    haveI : is_iso F.2 := snd_is_iso _ infer_instance infer_instance,
    refine ⟨f₁.inv, inv F.2, f₃.inv, _, _⟩; dsimp,
    rw [iso.inv_comp_eq, ← category.assoc, is_iso.eq_comp_inv, sq1],
    rw [is_iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, sq2],
  end,
  hom_inv_id' := by { ext; try { apply iso.hom_inv_id, }, apply is_iso.hom_inv_id },
  inv_hom_id' := by { ext; try { apply iso.inv_hom_id, }, apply is_iso.inv_hom_id } }

end iso

section split

/-- A short exact sequence `0 ⟶ A₁ -f⟶ A₂ -g⟶ A₃ ⟶ 0` is *left split*
if there exists a morphism `φ : A₂ ⟶ A₁` such that `f ≫ φ = 𝟙 A₁`. -/
def left_split (A : short_exact_sequence 𝒞) : Prop :=
∃ φ : A.2 ⟶ A.1, A.f ≫ φ = 𝟙 A.1

/-- A short exact sequence `0 ⟶ A₁ -f⟶ A₂ -g⟶ A₃ ⟶ 0` is *right split*
if there exists a morphism `φ : A₂ ⟶ A₁` such that `f ≫ φ = 𝟙 A₁`. -/
def right_split (A : short_exact_sequence 𝒞) : Prop :=
∃ χ : A.3 ⟶ A.2, χ ≫ A.g = 𝟙 A.3

variables {𝒜 : Type*} [category 𝒜] [abelian 𝒜]

lemma exact_of_split {A B C : 𝒜} (f : A ⟶ B) (g : B ⟶ C) (χ : C ⟶ B) (φ : B ⟶ A)
  (hfg : f ≫ g = 0) (H : φ ≫ f + g ≫ χ = 𝟙 B) : exact f g :=
{ w := hfg,
  epi :=
  begin
    let ψ : (kernel_subobject g : 𝒜) ⟶ image_subobject f :=
      subobject.arrow _ ≫ φ ≫ factor_thru_image_subobject f,
    suffices : ψ ≫ image_to_kernel f g hfg = 𝟙 _,
    { convert epi_of_epi ψ _, rw this, apply_instance },
    rw ← cancel_mono (subobject.arrow _), swap, { apply_instance },
    simp only [image_to_kernel_arrow, image_subobject_arrow_comp, category.id_comp, category.assoc],
    calc (kernel_subobject g).arrow ≫ φ ≫ f
        = (kernel_subobject g).arrow ≫ 𝟙 B : _
    ... = (kernel_subobject g).arrow        : category.comp_id _,
    rw [← H, preadditive.comp_add],
    simp only [add_zero, zero_comp, kernel_subobject_arrow_comp_assoc],
  end }

-- move this
lemma exact_inl_snd (A B : 𝒜) : exact (biprod.inl : A ⟶ A ⊞ B) biprod.snd :=
exact_of_split _ _ biprod.inr biprod.fst biprod.inl_snd biprod.total

def mk_of_split {A B C : 𝒜} (f : A ⟶ B) (g : B ⟶ C) (φ : B ⟶ A) (χ : C ⟶ B)
  (hfg : f ≫ g = 0) (hφ : f ≫ φ = 𝟙 A) (hχ : χ ≫ g = 𝟙 C) (H : φ ≫ f + g ≫ χ = 𝟙 B) :
  short_exact_sequence 𝒜 :=
{ fst := A,
  snd := B,
  trd := C,
  f := f,
  g := g,
  mono' := by { haveI : mono (f ≫ φ), { rw hφ, apply_instance }, exact mono_of_mono f φ, },
  epi' := by { haveI : epi (χ ≫ g), { rw hχ, apply_instance }, exact epi_of_epi χ g, },
  exact' := exact_of_split f g χ φ hfg H }

def mk_of_split' {A B C : 𝒜} (f : A ⟶ B) (g : B ⟶ C)
  (H : ∃ (φ : B ⟶ A) (χ : C ⟶ B), f ≫ g = 0 ∧ f ≫ φ = 𝟙 A ∧ χ ≫ g = 𝟙 C ∧ φ ≫ f + g ≫ χ = 𝟙 B) :
  short_exact_sequence 𝒜 :=
mk_of_split f g H.some H.some_spec.some H.some_spec.some_spec.1 H.some_spec.some_spec.2.1
  H.some_spec.some_spec.2.2.1 H.some_spec.some_spec.2.2.2

@[simp] def mk_split (A B : 𝒜) : short_exact_sequence 𝒜 :=
{ fst := A,
  snd := A ⊞ B,
  trd := B,
  f := biprod.inl,
  g := biprod.snd,
  exact' := exact_inl_snd _ _ }

/-- A *splitting* of a short exact sequence `0 ⟶ A₁ -f⟶ A₂ -g⟶ A₃ ⟶ 0` is
an isomorphism to the short exact sequence `0 ⟶ A₁ ⟶ A₁ ⊕ A₃ ⟶ A₃ ⟶ 0`,
where the left and right components of the isomorphism are identity maps. -/
structure splitting (A : short_exact_sequence 𝒜) extends A ≅ (mk_split A.1 A.3) :=
(fst_eq_id : hom.1 = 𝟙 A.1)
(trd_eq_id : hom.3 = 𝟙 A.3)

/-- A short exact sequence `0 ⟶ A₁ -f⟶ A₂ -g⟶ A₃ ⟶ 0` is *split* if there exist
`φ : A₂ ⟶ A₁` and `χ : A₃ ⟶ A₂` such that:
* `f ≫ φ = 𝟙 A₁`
* `χ ≫ g = 𝟙 A₃`
* `χ ≫ φ = 0`
* `φ ≫ f + g ≫ χ = 𝟙 A₂`
-/
def split (A : short_exact_sequence 𝒜) : Prop :=
∃ (φ : A.2 ⟶ A.1) (χ : A.3 ⟶ A.2),
   A.f ≫ φ = 𝟙 A.1 ∧ χ ≫ A.g = 𝟙 A.3 ∧ χ ≫ φ = 0 ∧ φ ≫ A.f + A.g ≫ χ = 𝟙 A.2

lemma mk_split_split (A B : 𝒜) : (mk_split A B).split :=
⟨biprod.fst, biprod.inr, biprod.inl_fst, biprod.inr_snd, biprod.inr_fst, biprod.total⟩

lemma splitting.split {A : short_exact_sequence 𝒜} (i : splitting A) : A.split :=
begin
  refine ⟨i.hom.2 ≫ biprod.fst ≫ i.inv.1, i.hom.3 ≫ biprod.inr ≫ i.inv.2, _⟩,
  simp only [category.assoc, ← hom.sq1_assoc, hom.sq2], dsimp,
  simp only [biprod.inl_fst_assoc, biprod.inr_snd_assoc, category.comp_id, category.assoc,
    ← comp_fst, ← comp_snd_assoc, ← comp_trd, i.to_iso.hom_inv_id, i.to_iso.inv_hom_id],
  dsimp,
  simp only [true_and, biprod.inr_fst_assoc, zero_comp, eq_self_iff_true, comp_zero,
    category.id_comp],
  simp only [hom.sq1, ← hom.sq2_assoc, ← comp_add],
  simp only [← category.assoc, ← add_comp, biprod.total,
    category.comp_id, ← comp_snd, i.to_iso.hom_inv_id], refl,
end

def left_split.splitting {A : short_exact_sequence 𝒜} (h : A.left_split) : A.splitting :=
{ to_iso := iso_of_components' (iso.refl _) (biprod.lift h.some A.g) (iso.refl _)
    (by { dsimp, simp only [category.id_comp], ext,
      { simpa only [biprod.inl_fst, biprod.lift_fst, category.assoc] using h.some_spec.symm, },
      { simp only [exact.w, f_comp_g, biprod.lift_snd, category.assoc, exact_inl_snd] } })
    (by { dsimp, simp only [category.comp_id, biprod.lift_snd], }),
  fst_eq_id := rfl,
  trd_eq_id := rfl }

def right_split.splitting {A : short_exact_sequence 𝒜} (h : A.right_split) : A.splitting :=
{ to_iso := iso.symm $ iso_of_components' (iso.refl _) (biprod.desc A.f h.some) (iso.refl _)
    (by { dsimp, simp only [biprod.inl_desc, category.id_comp], })
    (by { dsimp, simp only [category.comp_id], ext,
      { simp only [exact.w, f_comp_g, biprod.inl_desc_assoc, exact_inl_snd] },
      { simpa only [biprod.inr_snd, biprod.inr_desc_assoc] using h.some_spec, } }),
  fst_eq_id := rfl,
  trd_eq_id := rfl }

lemma tfae_split (A : short_exact_sequence 𝒜) :
  tfae [A.left_split, A.right_split, A.split, nonempty A.splitting] :=
begin
  tfae_have : 3 → 1, { rintro ⟨φ, χ, hφ, hχ, hχφ, H⟩, exact ⟨φ, hφ⟩ },
  tfae_have : 3 → 2, { rintro ⟨φ, χ, hφ, hχ, hχφ, H⟩, exact ⟨χ, hχ⟩ },
  tfae_have : 4 → 3, { rintro ⟨i⟩, exact i.split, },
  tfae_have : 1 → 4, { intro h, exact ⟨h.splitting⟩ },
  tfae_have : 2 → 4, { intro h, exact ⟨h.splitting⟩ },
  tfae_finish
end

end split

end short_exact_sequence

namespace short_exact_sequence

open category_theory.preadditive

variables {𝒞} [preadditive 𝒞] [has_images 𝒞] [has_kernels 𝒞]
variables (A B : short_exact_sequence 𝒞)

local notation `π₁` := congr_arg _root_.prod.fst
local notation `π₂` := congr_arg _root_.prod.snd

protected def hom_inj (f : A ⟶ B) : (A.1 ⟶ B.1) × (A.2 ⟶ B.2) × (A.3 ⟶ B.3) := ⟨f.1, f.2, f.3⟩

protected lemma hom_inj_injective : function.injective (short_exact_sequence.hom_inj A B) :=
λ f g h, let aux := π₂ h in
by { ext; [have := π₁ h, have := π₁ aux, have := π₂ aux]; exact this, }

instance : has_add (A ⟶ B) :=
{ add := λ f g,
  { fst := f.1 + g.1,
    snd := f.2 + g.2,
    trd := f.3 + g.3,
    sq1' := by { rw [add_comp, comp_add, f.sq1, g.sq1], },
    sq2' := by { rw [add_comp, comp_add, f.sq2, g.sq2], } } }

instance : has_neg (A ⟶ B) :=
{ neg := λ f,
  { fst := -f.1,
    snd := -f.2,
    trd := -f.3,
    sq1' := by { rw [neg_comp, comp_neg, f.sq1], },
    sq2' := by { rw [neg_comp, comp_neg, f.sq2], } } }

instance : has_sub (A ⟶ B) :=
{ sub := λ f g,
  { fst := f.1 - g.1,
    snd := f.2 - g.2,
    trd := f.3 - g.3,
    sq1' := by { rw [sub_comp, comp_sub, f.sq1, g.sq1], },
    sq2' := by { rw [sub_comp, comp_sub, f.sq2, g.sq2], } } }

instance has_nsmul : has_smul ℕ (A ⟶ B) :=
{ smul := λ n f,
  { fst := n • f.1,
    snd := n • f.2,
    trd := n • f.3,
    sq1' := by rw [nsmul_comp, comp_nsmul, f.sq1],
    sq2' := by rw [nsmul_comp, comp_nsmul, f.sq2] } }

instance has_zsmul : has_smul ℤ (A ⟶ B) :=
{ smul := λ n f,
  { fst := n • f.1,
    snd := n • f.2,
    trd := n • f.3,
    sq1' := by rw [zsmul_comp, comp_zsmul, f.sq1],
    sq2' := by rw [zsmul_comp, comp_zsmul, f.sq2] } }

variables (𝒞)

instance : preadditive (short_exact_sequence 𝒞) :=
{ hom_group := λ A B, (short_exact_sequence.hom_inj_injective A B).add_comm_group _
  rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl),
  add_comp' := by { intros, ext; apply add_comp },
  comp_add' := by { intros, ext; apply comp_add }, }
.

instance Fst_additive : (Fst 𝒞).additive := {}
instance Snd_additive : (Snd 𝒞).additive := {}
instance Trd_additive : (Trd 𝒞).additive := {}

end short_exact_sequence

end category_theory
