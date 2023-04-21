/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.simplicial_object
import category_theory.limits.shapes.finite_products

/-!

# Split simplicial objects

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we introduce the notion of split simplicial object.
If `C` is a category that has finite coproducts, a splitting
`s : splitting X` of a simplical object `X` in `C` consists
of the datum of a sequence of objects `s.N : ℕ → C` (which
we shall refer to as "nondegenerate simplices") and a
sequence of morphisms `s.ι n : s.N n → X _[n]` that have
the property that a certain canonical map identifies `X _[n]`
with the coproduct of objects `s.N i` indexed by all possible
epimorphisms `[n] ⟶ [i]` in `simplex_category`. (We do not
assume that the morphisms `s.ι n` are monomorphisms: in the
most common categories, this would be a consequence of the
axioms.)

Simplicial objects equipped with a splitting form a category
`simplicial_object.split C`.

## References
* [Stacks: Splitting simplicial objects] https://stacks.math.columbia.edu/tag/017O

-/

noncomputable theory

open category_theory category_theory.category category_theory.limits
  opposite simplex_category
open_locale simplicial

universe u

variables {C : Type*} [category C]

namespace simplicial_object

namespace splitting

/-- The index set which appears in the definition of split simplicial objects. -/
def index_set (Δ : simplex_categoryᵒᵖ) :=
Σ (Δ' : simplex_categoryᵒᵖ), { α : Δ.unop ⟶ Δ'.unop // epi α }

namespace index_set

/-- The element in `splitting.index_set Δ` attached to an epimorphism `f : Δ ⟶ Δ'`. -/
@[simps]
def mk {Δ Δ' : simplex_category} (f : Δ ⟶ Δ') [epi f] : index_set (op Δ) :=
⟨op Δ', f, infer_instance⟩

variables {Δ' Δ : simplex_categoryᵒᵖ} (A : index_set Δ) (θ : Δ ⟶ Δ')

/-- The epimorphism in `simplex_category` associated to `A : splitting.index_set Δ` -/
def e := A.2.1

instance : epi A.e := A.2.2

lemma ext' : A = ⟨A.1, ⟨A.e, A.2.2⟩⟩ := by tidy

lemma ext (A₁ A₂ : index_set Δ) (h₁ : A₁.1 = A₂.1)
  (h₂ : A₁.e ≫ eq_to_hom (by rw h₁) = A₂.e) : A₁ = A₂ :=
begin
  rcases A₁ with ⟨Δ₁, ⟨α₁, hα₁⟩⟩,
  rcases A₂ with ⟨Δ₂, ⟨α₂, hα₂⟩⟩,
  simp only at h₁,
  subst h₁,
  simp only [eq_to_hom_refl, comp_id, index_set.e] at h₂,
  simp only [h₂],
end

instance : fintype (index_set Δ) :=
fintype.of_injective
  ((λ A, ⟨⟨A.1.unop.len, nat.lt_succ_iff.mpr
    (len_le_of_epi (infer_instance : epi A.e))⟩, A.e.to_order_hom⟩) :
    index_set Δ → (sigma (λ (k : fin (Δ.unop.len+1)), (fin (Δ.unop.len+1) → fin (k+1)))))
begin
  rintros ⟨Δ₁, α₁⟩ ⟨Δ₂, α₂⟩ h₁,
  induction Δ₁ using opposite.rec,
  induction Δ₂ using opposite.rec,
  simp only at h₁,
  have h₂ : Δ₁ = Δ₂ := by { ext1, simpa only [fin.mk_eq_mk] using h₁.1, },
  subst h₂,
  refine ext _ _ rfl _,
  ext : 2,
  exact eq_of_heq h₁.2,
end

variable (Δ)

/-- The distinguished element in `splitting.index_set Δ` which corresponds to the
identity of `Δ`. -/
def id : index_set Δ := ⟨Δ, ⟨𝟙 _, by apply_instance,⟩⟩

instance : inhabited (index_set Δ) := ⟨id Δ⟩

variable {Δ}

/-- The condition that an element `splitting.index_set Δ` is the distinguished
element `splitting.index_set.id Δ`. -/
@[simp]
def eq_id : Prop := A = id _

lemma eq_id_iff_eq : A.eq_id ↔ A.1 = Δ :=
begin
  split,
  { intro h,
    dsimp at h,
    rw h,
    refl, },
  { intro h,
    rcases A with ⟨Δ', ⟨f, hf⟩⟩,
    simp only at h,
    subst h,
    refine ext _ _ rfl _,
    { haveI := hf,
      simp only [eq_to_hom_refl, comp_id],
      exact eq_id_of_epi f, }, },
end

lemma eq_id_iff_len_eq : A.eq_id ↔ A.1.unop.len = Δ.unop.len :=
begin
  rw eq_id_iff_eq,
  split,
  { intro h,
    rw h, },
  { intro h,
    rw ← unop_inj_iff,
    ext,
    exact h, },
end

lemma eq_id_iff_len_le : A.eq_id ↔ Δ.unop.len ≤ A.1.unop.len :=
begin
  rw eq_id_iff_len_eq,
  split,
  { intro h,
    rw h, },
  { exact le_antisymm (len_le_of_epi (infer_instance : epi A.e)), },
end

lemma eq_id_iff_mono : A.eq_id ↔ mono A.e :=
begin
  split,
  { intro h,
    dsimp at h,
    subst h,
    dsimp only [id, e],
    apply_instance, },
  { intro h,
    rw eq_id_iff_len_le,
    exact len_le_of_mono h, }
end

/-- Given `A : index_set Δ₁`, if `p.unop : unop Δ₂ ⟶ unop Δ₁` is an epi, this
is the obvious element in `A : index_set Δ₂` associated to the composition
of epimorphisms `p.unop ≫ A.e`. -/
@[simps]
def epi_comp {Δ₁ Δ₂ : simplex_categoryᵒᵖ} (A : index_set Δ₁) (p : Δ₁ ⟶ Δ₂) [epi p.unop] :
  index_set Δ₂ := ⟨A.1, ⟨p.unop ≫ A.e, epi_comp _ _⟩⟩

/--
When `A : index_set Δ` and `θ : Δ → Δ'` is a morphism in `simplex_categoryᵒᵖ`,
an element in `index_set Δ'` can be defined by using the epi-mono factorisation
of `θ.unop ≫ A.e`. -/
def pull : index_set Δ' := mk (factor_thru_image (θ.unop ≫ A.e))

@[reassoc]
lemma fac_pull : (A.pull θ).e ≫ image.ι (θ.unop ≫ A.e) = θ.unop ≫ A.e := image.fac _

end index_set

variables (N : ℕ → C) (Δ : simplex_categoryᵒᵖ)
  (X : simplicial_object C) (φ : Π n, N n ⟶ X _[n])

/-- Given a sequences of objects `N : ℕ → C` in a category `C`, this is
a family of objects indexed by the elements `A : splitting.index_set Δ`.
The `Δ`-simplices of a split simplicial objects shall identify to the
coproduct of objects in such a family. -/
@[simp, nolint unused_arguments]
def summand (A : index_set Δ) : C := N A.1.unop.len

variable [has_finite_coproducts C]

/-- The coproduct of the family `summand N Δ` -/
@[simp]
def coprod := ∐ summand N Δ

variable {Δ}

/-- The inclusion of a summand in the coproduct. -/
@[simp]
def ι_coprod (A : index_set Δ) : N A.1.unop.len ⟶ coprod N Δ := sigma.ι _ A

variables {N}

/-- The canonical morphism `coprod N Δ ⟶ X.obj Δ` attached to a sequence
of objects `N` and a sequence of morphisms `N n ⟶ X _[n]`. -/
@[simp]
def map (Δ : simplex_categoryᵒᵖ) : coprod N Δ ⟶ X.obj Δ :=
sigma.desc (λ A, φ A.1.unop.len ≫ X.map A.e.op)

end splitting

variable [has_finite_coproducts C]

/-- A splitting of a simplicial object `X` consists of the datum of a sequence
of objects `N`, a sequence of morphisms `ι : N n ⟶ X _[n]` such that
for all `Δ : simplex_categoryhᵒᵖ`, the canonical map `splitting.map X ι Δ`
is an isomorphism. -/
@[nolint has_nonempty_instance]
structure splitting (X : simplicial_object C) :=
(N : ℕ → C)
(ι : Π n, N n ⟶ X _[n])
(map_is_iso' : ∀ (Δ : simplex_categoryᵒᵖ), is_iso (splitting.map X ι Δ))

namespace splitting

variables {X Y : simplicial_object C} (s : splitting X)

instance map_is_iso (Δ : simplex_categoryᵒᵖ) : is_iso (splitting.map X s.ι Δ) :=
s.map_is_iso' Δ

/-- The isomorphism on simplices given by the axiom `splitting.map_is_iso'` -/
@[simps]
def iso (Δ : simplex_categoryᵒᵖ) : coprod s.N Δ ≅ X.obj Δ :=
as_iso (splitting.map X s.ι Δ)

/-- Via the isomorphism `s.iso Δ`, this is the inclusion of a summand
in the direct sum decomposition given by the splitting `s : splitting X`. -/
def ι_summand {Δ : simplex_categoryᵒᵖ} (A : index_set Δ) :
  s.N A.1.unop.len ⟶ X.obj Δ :=
splitting.ι_coprod s.N A ≫ (s.iso Δ).hom

@[reassoc]
lemma ι_summand_eq {Δ : simplex_categoryᵒᵖ} (A : index_set Δ) :
  s.ι_summand A = s.ι A.1.unop.len ≫ X.map A.e.op :=
begin
  dsimp only [ι_summand, iso.hom],
  erw [colimit.ι_desc, cofan.mk_ι_app],
end

lemma ι_summand_id (n : ℕ) : s.ι_summand (index_set.id (op [n])) = s.ι n :=
by { erw [ι_summand_eq, X.map_id, comp_id], refl, }

/-- As it is stated in `splitting.hom_ext`, a morphism `f : X ⟶ Y` from a split
simplicial object to any simplicial object is determined by its restrictions
`s.φ f n : s.N n ⟶ Y _[n]` to the distinguished summands in each degree `n`. -/
@[simp]
def φ (f : X ⟶ Y) (n : ℕ) : s.N n ⟶ Y _[n] := s.ι n ≫ f.app (op [n])

@[simp, reassoc]
lemma ι_summand_comp_app (f : X ⟶ Y) {Δ : simplex_categoryᵒᵖ} (A : index_set Δ) :
  s.ι_summand A ≫ f.app Δ = s.φ f A.1.unop.len ≫ Y.map A.e.op :=
by simp only [ι_summand_eq_assoc, φ, nat_trans.naturality, assoc]

lemma hom_ext' {Z : C} {Δ : simplex_categoryᵒᵖ} (f g : X.obj Δ ⟶ Z)
  (h : ∀ (A : index_set Δ), s.ι_summand A ≫ f = s.ι_summand A ≫ g) :
    f = g :=
begin
  rw ← cancel_epi (s.iso Δ).hom,
  ext A,
  discrete_cases,
  simpa only [ι_summand_eq, iso_hom, colimit.ι_desc_assoc, cofan.mk_ι_app, assoc] using h A,
end

lemma hom_ext (f g : X ⟶ Y) (h : ∀ n : ℕ, s.φ f n = s.φ g n) : f = g :=
begin
  ext Δ,
  apply s.hom_ext',
  intro A,
  induction Δ using opposite.rec,
  induction Δ using simplex_category.rec with n,
  dsimp,
  simp only [s.ι_summand_comp_app, h],
end

/-- The map `X.obj Δ ⟶ Z` obtained by providing a family of morphisms on all the
terms of decomposition given by a splitting `s : splitting X`  -/
def desc {Z : C} (Δ : simplex_categoryᵒᵖ)
  (F : Π (A : index_set Δ), s.N A.1.unop.len ⟶ Z) : X.obj Δ ⟶ Z :=
(s.iso Δ).inv ≫ sigma.desc F

@[simp, reassoc]
lemma ι_desc {Z : C} (Δ : simplex_categoryᵒᵖ)
  (F : Π (A : index_set Δ), s.N A.1.unop.len ⟶ Z) (A : index_set Δ) :
  s.ι_summand A ≫ s.desc Δ F = F A :=
begin
  dsimp only [ι_summand, desc],
  simp only [assoc, iso.hom_inv_id_assoc, ι_coprod],
  erw [colimit.ι_desc, cofan.mk_ι_app],
end

/-- A simplicial object that is isomorphic to a split simplicial object is split. -/
@[simps]
def of_iso (e : X ≅ Y) : splitting Y :=
{ N := s.N,
  ι := λ n, s.ι n ≫ e.hom.app (op [n]),
  map_is_iso' := λ Δ, begin
    convert (infer_instance : is_iso ((s.iso Δ).hom ≫ e.hom.app Δ)),
    tidy,
  end, }

@[reassoc]
lemma ι_summand_epi_naturality {Δ₁ Δ₂ : simplex_categoryᵒᵖ} (A : index_set Δ₁)
  (p : Δ₁ ⟶ Δ₂) [epi p.unop] :
  s.ι_summand A ≫ X.map p = s.ι_summand (A.epi_comp p) :=
begin
  dsimp [ι_summand],
  erw [colimit.ι_desc, colimit.ι_desc, cofan.mk_ι_app, cofan.mk_ι_app],
  dsimp only [index_set.epi_comp, index_set.e],
  rw [op_comp, X.map_comp, assoc, quiver.hom.op_unop],
end

end splitting

variable (C)

/-- The category `simplicial_object.split C` is the category of simplicial objects
in `C` equipped with a splitting, and morphisms are morphisms of simplicial objects
which are compatible with the splittings. -/
@[ext, nolint has_nonempty_instance]
structure split := (X : simplicial_object C) (s : splitting X)

namespace split

variable {C}

/-- The object in `simplicial_object.split C` attached to a splitting `s : splitting X`
of a simplicial object `X`. -/
@[simps]
def mk' {X : simplicial_object C} (s : splitting X) : split C := ⟨X, s⟩

/-- Morphisms in `simplicial_object.split C` are morphisms of simplicial objects that
are compatible with the splittings. -/
@[nolint has_nonempty_instance]
structure hom (S₁ S₂ : split C) :=
(F : S₁.X ⟶ S₂.X)
(f : Π (n : ℕ), S₁.s.N n ⟶ S₂.s.N n)
(comm' : ∀ (n : ℕ), S₁.s.ι n ≫ F.app (op [n]) = f n ≫ S₂.s.ι n)

@[ext]
lemma hom.ext {S₁ S₂ : split C} (Φ₁ Φ₂ : hom S₁ S₂) (h : ∀ (n : ℕ), Φ₁.f n = Φ₂.f n) :
  Φ₁ = Φ₂ :=
begin
  rcases Φ₁ with ⟨F₁, f₁, c₁⟩,
  rcases Φ₂ with ⟨F₂, f₂, c₂⟩,
  have h' : f₁ = f₂ := by { ext, apply h, },
  subst h',
  simp only [eq_self_iff_true, and_true],
  apply S₁.s.hom_ext,
  intro n,
  dsimp,
  rw [c₁, c₂],
end

restate_axiom hom.comm'
attribute [simp, reassoc] hom.comm

end split

instance : category (split C) :=
{ hom      := split.hom,
  id       := λ S, { F := 𝟙 _, f := λ n, 𝟙 _, comm' := by tidy, },
  comp     := λ S₁ S₂ S₃ Φ₁₂ Φ₂₃,
    { F := Φ₁₂.F ≫ Φ₂₃.F, f := λ n, Φ₁₂.f n ≫ Φ₂₃.f n, comm' := by tidy, }, }

variable {C}

namespace split

lemma congr_F {S₁ S₂ : split C} {Φ₁ Φ₂ : S₁ ⟶ S₂} (h : Φ₁ = Φ₂) : Φ₁.F = Φ₂.F := by rw h
lemma congr_f {S₁ S₂ : split C} {Φ₁ Φ₂ : S₁ ⟶ S₂} (h : Φ₁ = Φ₂) (n : ℕ) :
  Φ₁.f n = Φ₂.f n := by rw h

@[simp]
lemma id_F (S : split C) : (𝟙 S : S ⟶ S).F = 𝟙 (S.X) := rfl

@[simp]
lemma id_f (S : split C) (n : ℕ) : (𝟙 S : S ⟶ S).f n = 𝟙 (S.s.N n) := rfl

@[simp]
lemma comp_F {S₁ S₂ S₃ : split C} (Φ₁₂ : S₁ ⟶ S₂) (Φ₂₃ : S₂ ⟶ S₃) :
  (Φ₁₂ ≫ Φ₂₃).F = Φ₁₂.F ≫ Φ₂₃.F := rfl

@[simp]
lemma comp_f {S₁ S₂ S₃ : split C} (Φ₁₂ : S₁ ⟶ S₂) (Φ₂₃ : S₂ ⟶ S₃) (n : ℕ) :
  (Φ₁₂ ≫ Φ₂₃).f n = Φ₁₂.f n ≫ Φ₂₃.f n := rfl

@[simp, reassoc]
lemma ι_summand_naturality_symm {S₁ S₂ : split C} (Φ : S₁ ⟶ S₂)
  {Δ : simplex_categoryᵒᵖ} (A : splitting.index_set Δ) :
  S₁.s.ι_summand A ≫ Φ.F.app Δ = Φ.f A.1.unop.len ≫ S₂.s.ι_summand A :=
by rw [S₁.s.ι_summand_eq, S₂.s.ι_summand_eq, assoc, Φ.F.naturality, ← Φ.comm_assoc]

variable (C)

/-- The functor `simplicial_object.split C ⥤ simplicial_object C` which forgets
the splitting. -/
@[simps]
def forget : split C ⥤ simplicial_object C :=
{ obj := λ S, S.X,
  map := λ S₁ S₂ Φ, Φ.F, }

/-- The functor `simplicial_object.split C ⥤ C` which sends a simplicial object equipped
with a splitting to its nondegenerate `n`-simplices. -/
@[simps]
def eval_N (n : ℕ) : split C ⥤ C :=
{ obj := λ S, S.s.N n,
  map := λ S₁ S₂ Φ, Φ.f n, }

/-- The inclusion of each summand in the coproduct decomposition of simplices
in split simplicial objects is a natural transformation of functors
`simplicial_object.split C ⥤ C` -/
@[simps]
def nat_trans_ι_summand {Δ : simplex_categoryᵒᵖ} (A : splitting.index_set Δ) :
  eval_N C A.1.unop.len ⟶ forget C ⋙ (evaluation simplex_categoryᵒᵖ C).obj Δ :=
{ app := λ S, S.s.ι_summand A,
  naturality' := λ S₁ S₂ Φ, (ι_summand_naturality_symm Φ A).symm, }

end split

end simplicial_object
