import category_theory.limits.preserves.shapes.zero
import category_theory.limits.preserves.finite
import category_theory.limits.shapes.finite_limits
import category_theory.limits.shapes.kernels
import tactic.equiv_rw

noncomputable theory

open category_theory category_theory.category category_theory.limits
open_locale zero_object

variables {C D : Type*} [category C] [category D]

namespace category_theory

namespace functor

open limits

variable (F : C ⥤ D)

class exact :=
(preserves_finite_limits : preserves_finite_limits F)
(preserves_finite_colimits : preserves_finite_colimits F)

@[priority 100]
instance [F.exact] : preserves_finite_limits F := exact.preserves_finite_limits

@[priority 100]
instance [F.exact] : preserves_finite_colimits F := exact.preserves_finite_colimits

class preserves_homology (F : C ⥤ D) [has_zero_morphisms C] [has_zero_morphisms D] :=
(zero : F.preserves_zero_morphisms)
(preserves_kernels [] : Π ⦃X Y : C⦄ (f : X ⟶ Y), preserves_limit (parallel_pair f 0) F)
(preserves_cokernels [] : Π ⦃X Y : C⦄ (f : X ⟶ Y), preserves_colimit (parallel_pair f 0) F)

@[priority 100]
instance preserves_homology_of_exact [has_zero_morphisms C] [has_zero_morphisms D] (F : C ⥤ D)
  [F.preserves_zero_morphisms] [F.exact] :
  preserves_homology F :=
{ zero := infer_instance,
  preserves_kernels := infer_instance,
  preserves_cokernels := infer_instance, }

end functor

end category_theory

variable (C)

/-- A short complex in a category `C` with zero composition is the datum
of two composable morphisms `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` such that
`f ≫ g = 0`. -/
structure short_complex [has_zero_morphisms C] :=
{X₁ X₂ X₃ : C}
(f : X₁ ⟶ X₂)
(g : X₂ ⟶ X₃)
(zero : f ≫ g = 0)

variables {C} [has_zero_morphisms C]

namespace short_complex

instance [has_zero_object C] : inhabited (short_complex C) :=
⟨short_complex.mk (0 : 0 ⟶ 0) (0 : 0 ⟶ 0) comp_zero⟩

attribute [simp, reassoc] zero

/-- Morphisms of short complexes are the commutative diagrams of the obvious shape. -/
@[ext]
structure hom (S₁ S₂ : short_complex C) :=
(τ₁ : S₁.X₁ ⟶ S₂.X₁)
(τ₂ : S₁.X₂ ⟶ S₂.X₂)
(τ₃ : S₁.X₃ ⟶ S₂.X₃)
(comm₁₂ : τ₁ ≫ S₂.f = S₁.f ≫ τ₂)
(comm₂₃ : τ₂ ≫ S₂.g = S₁.g ≫ τ₃)

attribute [reassoc] hom.comm₁₂ hom.comm₂₃

variables (S : short_complex C) {S₁ S₂ S₃ : short_complex C}

/-- The identity morphism of a short complex. -/
@[simps]
def hom.id : hom S S := ⟨𝟙 _, 𝟙 _, 𝟙 _, by simp, by simp⟩

instance : inhabited (hom S S) := ⟨hom.id S⟩

/-- The composition of morphisms of short complexes. -/
@[simps]
def hom.comp (φ₁₂ : hom S₁ S₂) (φ₂₃ : hom S₂ S₃) : hom S₁ S₃ :=
⟨φ₁₂.τ₁ ≫ φ₂₃.τ₁, φ₁₂.τ₂ ≫ φ₂₃.τ₂, φ₁₂.τ₃ ≫ φ₂₃.τ₃,
  by simp only [assoc, hom.comm₁₂, hom.comm₁₂_assoc],
  by simp only [assoc, hom.comm₂₃, hom.comm₂₃_assoc]⟩

instance : category (short_complex C) :=
{ hom := hom,
  id := hom.id,
  comp := λ S₁ S₂ S₃, hom.comp, }

@[simp] lemma id_τ₁ : hom.τ₁ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_τ₂ : hom.τ₂ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_τ₃ : hom.τ₃ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma comp_τ₁ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) : (φ₁₂ ≫ φ₂₃).τ₁ = φ₁₂.τ₁ ≫ φ₂₃.τ₁ := rfl
@[simp] lemma comp_τ₂ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) : (φ₁₂ ≫ φ₂₃).τ₂ = φ₁₂.τ₂ ≫ φ₂₃.τ₂ := rfl
@[simp] lemma comp_τ₃ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) : (φ₁₂ ≫ φ₂₃).τ₃ = φ₁₂.τ₃ ≫ φ₂₃.τ₃ := rfl

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

instance (f : S₁ ⟶ S₂) [is_iso f] : is_iso f.τ₁ :=
by { change is_iso (π₁.map_iso (as_iso f)).hom, apply_instance, }

instance (f : S₁ ⟶ S₂) [is_iso f] : is_iso f.τ₂ :=
by { change is_iso (π₂.map_iso (as_iso f)).hom, apply_instance, }

instance (f : S₁ ⟶ S₂) [is_iso f] : is_iso f.τ₃ :=
by { change is_iso (π₃.map_iso (as_iso f)).hom, apply_instance, }

variables {C D}

@[simps]
def _root_.category_theory.functor.map_short_complex
  [has_zero_morphisms D] (F : C ⥤ D) [F.preserves_zero_morphisms] : short_complex C ⥤ short_complex D :=
{ obj := λ S, short_complex.mk (F.map S.f) (F.map S.g)
    (by rw [← F.map_comp, S.zero, F.map_zero]),
  map := λ S₁ S₂ φ, short_complex.hom.mk (F.map φ.τ₁) (F.map φ.τ₂) (F.map φ.τ₃)
    (by { dsimp, simp only [← F.map_comp, φ.comm₁₂], })
    (by { dsimp, simp only [← F.map_comp, φ.comm₂₃], }), }

@[simps]
def map [has_zero_morphisms D] (F : C ⥤ D) [F.preserves_zero_morphisms] : short_complex D :=
F.map_short_complex.obj S

/-- A constructor for isomorphisms in the category `short_complex C`-/
@[simps]
def mk_iso (e₁ : S₁.X₁ ≅ S₂.X₁) (e₂ : S₁.X₂ ≅ S₂.X₂) (e₃ : S₁.X₃ ≅ S₂.X₃)
  (comm₁₂ : e₁.hom ≫ S₂.f = S₁.f ≫ e₂.hom) (comm₂₃ : e₂.hom ≫ S₂.g = S₁.g ≫ e₃.hom) :
  S₁ ≅ S₂ :=
{ hom := hom.mk e₁.hom e₂.hom e₃.hom comm₁₂ comm₂₃,
  inv := hom.mk e₁.inv e₂.inv e₃.inv
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
⟨φ.τ₃.op, φ.τ₂.op, φ.τ₁.op ,
  (by { dsimp, simp only [← op_comp, φ.comm₂₃], }),
  (by { dsimp, simp only [← op_comp, φ.comm₁₂], })⟩

/-- The short_complex in `C` associated to a short complex in `Cᵒᵖ`. -/
@[simps]
def unop (S : short_complex Cᵒᵖ) : short_complex C :=
mk S.g.unop S.f.unop (by simpa only [← unop_comp, S.zero])

/-- The morphism in `short_complex C` associated to a morphism in `short_complex Cᵒᵖ` -/
@[simps]
def unop_map {S₁ S₂ : short_complex Cᵒᵖ} (φ : S₁ ⟶ S₂) : S₂.unop ⟶ S₁.unop :=
⟨φ.τ₃.unop, φ.τ₂.unop, φ.τ₁.unop ,
  (by { dsimp, simp only [← unop_comp, φ.comm₂₃], }),
  (by { dsimp, simp only [← unop_comp, φ.comm₁₂], })⟩

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
  map := λ S₁ S₂ φ, (unop_map φ).op, }

/-- The obvious equivalence of categories `(short_complex C)ᵒᵖ ≌ short_complex Cᵒᵖ`. -/
def op_equiv : (short_complex C)ᵒᵖ ≌ short_complex Cᵒᵖ :=
{ functor := op_functor C,
  inverse := unop_functor C,
  unit_iso := nat_iso.of_components (λ S, (op_unop (opposite.unop S)).op)
    (λ S₁ S₂ f, quiver.hom.unop_inj (by tidy)),
  counit_iso := nat_iso.of_components (unop_op) (by tidy), }

variables (S₁ S₂) {C}

/-- The zero morphism between two short complexes. -/
@[simps]
def hom.zero : S₁ ⟶ S₂ :=
⟨0, 0, 0, by simp, by simp⟩

@[simps]
instance : has_zero (S₁ ⟶ S₂) := ⟨hom.zero _ _⟩

instance : has_zero_morphisms (short_complex C) := { }

/-- If `S : short_complex C`, `h : homology_full_data S` consists of
various fields which expresses that `h.H` is the homology of `S`.
The datum includes `h.K` which is a kernel of the morphism `S.g`,
so that we may identify `h.K` as a *cycles* of the complex `S`.
Then, we require that `h.H` is a cokernel of the morphism
`S.X₁ ⟶ h.K` induced by `f` (this morphism shall be denote `h.f'`).
This expresses `h.H` as the quotient of cycles by boundaries, i.e.
as a quotient of a subobject `h.K` of `S.X₂`.
In order to make the notion of homology self-dual with respect
to taking the opposite category, we also require an object
`h.Q`, which is a cokernel of `S.f` and an identification
of `h.H` as a kernel of the morphism `h.g' : h.Q ⟶ S.X₃`
induced by `S.g`. Then, the homology `h.H` is also expressed
a subject of the quotient `h.Q` of `S.X₂`.

The primary use of this structure is for the internals of
homology API. In order to do computations, it is advisable
to use `homology_data` which involves only the expression
of the homology as a quotient of a subobject. -/
@[nolint has_nonempty_instance]
structure homology_full_data :=
(K Q H : C)
(i : K ⟶ S.X₂)
(p : S.X₂ ⟶ Q)
(π : K ⟶ H)
(ι : H ⟶ Q)
(π_ι : π ≫ ι = i ≫ p)
(hi₀ : i ≫ S.g = 0)
(hp₀ : S.f ≫ p = 0)
(hi : is_limit (kernel_fork.of_ι i hi₀))
(hp : is_colimit (cokernel_cofork.of_π p hp₀))
(hπ₀ : hi.lift (kernel_fork.of_ι _ S.zero) ≫ π = 0)
(hι₀ : ι ≫ hp.desc (cokernel_cofork.of_π _ S.zero) = 0)
(hπ : is_colimit (cokernel_cofork.of_π π hπ₀))
(hι : is_limit (kernel_fork.of_ι ι hι₀))

namespace homology_full_data

attribute [simp, reassoc] hi₀ hp₀ hπ₀ hι₀
attribute [reassoc] π_ι
variables {S} (h : homology_full_data S)

/-- The morphism `S.X₁ ⟶ h.K` induced by `S.f : S.X₁ ⟶ S.X₂` and the fact that
`h.K` is a kernel of `S.g : S.X₂ ⟶ S.X₃`. -/
def f' : S.X₁ ⟶ h.K := h.hi.lift (kernel_fork.of_ι _ S.zero)

/-- The morphism `h.Q ⟶ S.X₃` induced by `S.g : S.X₂ ⟶ S.X₃` and the fact that
`h.Q` is a cokernel of `S.f : S.X₁ ⟶ S.X₂`. -/
def g' : h.Q ⟶ S.X₃ := h.hp.desc (cokernel_cofork.of_π _ S.zero)

@[simp, reassoc]
lemma f'_i : h.f' ≫ h.i = S.f := (kernel_fork.is_limit.lift' _ _ _).2

@[simp, reassoc]
lemma f'_π : h.f' ≫ h.π = 0 := h.hπ₀

@[simp, reassoc]
lemma ι_g' : h.ι ≫ h.g' = 0 := h.hι₀

@[simp, reassoc]
lemma p_g' : h.p ≫ h.g' = S.g := (cokernel_cofork.is_colimit.desc' h.hp _ _).2

/-- For `h : homology_ful_data S`, this is a restatement of `h.hπ`, saying that
`π : h.K ⟶ h.H` is a cokernel of `h.f' : S.X₁ ⟶ h.K`. -/
@[simp]
def hπ' : is_colimit (cokernel_cofork.of_π h.π h.f'_π) := h.hπ

/-- For `h : homology_ful_data S`, this is a restatement of `h.hι`, saying that
`ι : h.H ⟶ h.Q` is a kernel of `h.g' : h.Q ⟶ S.X₃`. -/
@[simp]
def hι' : is_limit (kernel_fork.of_ι h.ι h.ι_g') := h.hι

instance : mono h.i :=
⟨λ Y l₁ l₂, fork.is_limit.hom_ext h.hi⟩

instance : mono h.ι :=
⟨λ Y l₁ l₂, fork.is_limit.hom_ext h.hι⟩

instance : epi h.p :=
⟨λ Y l₁ l₂, cofork.is_colimit.hom_ext h.hp⟩

instance : epi h.π :=
⟨λ Y l₁ l₂, cofork.is_colimit.hom_ext h.hπ⟩

end homology_full_data

/-- We shall say that a short complex `S` has homology if
the type `homology_full_data S` is not empty. -/
class has_homology : Prop :=
(cond [] : nonempty (homology_full_data S))

variable {S}
lemma has_homology.mk' (h : homology_full_data S) : has_homology S :=
⟨nonempty.intro h⟩

variable (S)

/-- A choice of term of type `homology_full_data S` when `[has_homology S]`. -/
def some_homology_full_data [has_homology S] :
  homology_full_data S := (has_homology.cond S).some

/-- The homology of `S` is definition by taking the `H` field of
`S.some_homology_full_data`. -/
def homology [has_homology S] : C := S.some_homology_full_data.H

namespace homology_full_data

section map

variables {S} (h : homology_full_data S) (F : C ⥤ D)

@[simps]
def _root_.category_theory.limits.parallel_pair.comp_nat_iso'
  {C D : Type*} [category C] [category D] (F : C ⥤ D) [has_zero_morphisms C] [has_zero_morphisms D]
  [F.preserves_zero_morphisms] {X Y : C} (f : X ⟶ Y) (f' : F.obj X ⟶ F.obj Y)
  (h : f' = F.map f) :
  parallel_pair f 0 ⋙ F ≅ parallel_pair f' 0 :=
parallel_pair.ext (iso.refl _) (iso.refl _) (by tidy) (by tidy)

@[simps]
def _root_.category_theory.limits.parallel_pair.comp_nat_iso
  {C D : Type*} [category C] [category D] (F : C ⥤ D) [has_zero_morphisms C] [has_zero_morphisms D]
  [F.preserves_zero_morphisms] {X Y : C} (f : X ⟶ Y) :
  parallel_pair f 0 ⋙ F ≅ parallel_pair (F.map f) 0 :=
category_theory.limits.parallel_pair.comp_nat_iso' F f _ rfl

namespace map

lemma π_ι : F.map h.π ≫ F.map h.ι = F.map h.i ≫ F.map h.p :=
by simp only [← F.map_comp, h.π_ι]

variables [has_zero_morphisms D] [functor.preserves_zero_morphisms F]

lemma hi₀ : F.map h.i ≫ F.map S.g = 0 :=
by simp only [← F.map_comp, h.hi₀, F.map_zero]

lemma hp₀ : F.map S.f ≫ F.map h.p = 0 :=
by simp only [← F.map_comp, h.hp₀, F.map_zero]

def hi [preserves_limit (parallel_pair S.g 0) F] :
  is_limit (kernel_fork.of_ι (F.map h.i) (hi₀ h F)) :=
begin
  equiv_rw (is_limit.postcompose_inv_equiv
    (category_theory.limits.parallel_pair.comp_nat_iso F S.g) _).symm,
  refine is_limit.of_iso_limit (is_limit_of_preserves F h.hi)
    (cones.ext (iso.refl _) _),
  rintro (_|_),
  { tidy, },
  { dsimp,
    simp only [comp_id, id_comp, F.map_comp], },
end

lemma hf' [preserves_limit (parallel_pair S.g 0) F] :
  F.map h.f' = (hi h F).lift (kernel_fork.of_ι (S.map F).f (S.map F).zero) :=
begin
  apply fork.is_limit.hom_ext (hi h F),
  rw fork.is_limit.lift_ι,
  simp only [fork.is_limit.lift_ι, kernel_fork.ι_of_ι, ← F.map_comp, h.f'_i, map_f],
end

def hp [preserves_colimit (parallel_pair S.f 0) F] :
  is_colimit (cokernel_cofork.of_π (F.map h.p) (hp₀ h F)) :=
begin
  equiv_rw (is_colimit.precompose_hom_equiv
    (category_theory.limits.parallel_pair.comp_nat_iso F S.f) _).symm,
  refine is_colimit.of_iso_colimit (is_colimit_of_preserves F h.hp)
    (cocones.ext (iso.refl _) _),
  rintro (_|_),
  { dsimp,
    simp only [id_comp, comp_id, F.map_comp], },
  { tidy, },
end

lemma hg' [preserves_colimit (parallel_pair S.f 0) F] :
  F.map h.g' = (hp h F).desc (cokernel_cofork.of_π (S.map F).g (S.map F).zero) :=
begin
  apply cofork.is_colimit.hom_ext (hp h F),
  rw cofork.is_colimit.π_desc,
  simp only [cokernel_cofork.π_of_π, ← F.map_comp, h.p_g', map_g],
end

lemma hπ₀ [preserves_limit (parallel_pair S.g 0) F] :
  (hi h F).lift (kernel_fork.of_ι (S.map F).f (S.map F).zero) ≫ F.map h.π = 0 :=
by rw [← hf', ← F.map_comp, h.f'_π, F.map_zero]

lemma hι₀ [preserves_colimit (parallel_pair S.f 0) F] :
  F.map h.ι ≫ (hp h F).desc (cokernel_cofork.of_π (S.map F).g (S.map F).zero) = 0 :=
by rw [← hg', ← F.map_comp, h.ι_g', F.map_zero]

def hπ [preserves_limit (parallel_pair S.g 0) F]
  [preserves_colimit (parallel_pair h.f' 0) F] :
  is_colimit (cokernel_cofork.of_π (F.map h.π) (hπ₀ h F)) :=
begin
  equiv_rw (is_colimit.precompose_hom_equiv
    (category_theory.limits.parallel_pair.comp_nat_iso' F h.f' _ (hf' h F).symm) _).symm,
  refine is_colimit.of_iso_colimit (is_colimit_of_preserves F h.hπ)
    (cocones.ext (iso.refl _) _),
  rintro (_|_),
  { dsimp,
    simp only [id_comp, comp_id, F.map_comp],
    erw hf',
    refl, },
  { tidy, },
end

def hι [preserves_colimit (parallel_pair S.f 0) F]
  [preserves_limit (parallel_pair h.g' 0) F] :
  is_limit (kernel_fork.of_ι (F.map h.ι) (hι₀ h F)) :=
begin
  equiv_rw (is_limit.postcompose_inv_equiv
    (category_theory.limits.parallel_pair.comp_nat_iso' F h.g' _ (hg' h F).symm) _).symm,
  refine is_limit.of_iso_limit (is_limit_of_preserves F h.hι)
    (cones.ext (iso.refl _) _),
  rintro (_|_),
  { tidy, },
  { dsimp,
    simp only [comp_id, id_comp, F.map_comp],
    erw hg',
    refl, },
end

end map

class is_preserved_by [has_zero_morphisms D] [F.preserves_zero_morphisms] :=
(hf [] : preserves_colimit (parallel_pair S.f 0) F)
(hf' [] : preserves_colimit (parallel_pair h.f' 0) F)
(hg [] : preserves_limit (parallel_pair S.g 0) F)
(hg' [] : preserves_limit (parallel_pair h.g' 0) F)

@[priority 100]
instance is_preserved_by_of_preserves_homology [has_zero_morphisms D]
  [F.preserves_zero_morphisms] [F.preserves_homology] : h.is_preserved_by F :=
{ hf := category_theory.functor.preserves_homology.preserves_cokernels F _,
  hf' := category_theory.functor.preserves_homology.preserves_cokernels F _,
  hg := category_theory.functor.preserves_homology.preserves_kernels F _,
  hg' := category_theory.functor.preserves_homology.preserves_kernels F _, }

@[simp]
def map (h : homology_full_data S) (F : C ⥤ D) [has_zero_morphisms D]
  [F.preserves_zero_morphisms] [h.is_preserved_by F] : homology_full_data (S.map F) :=
begin
  haveI := is_preserved_by.hf h F,
  haveI := is_preserved_by.hf' h F,
  haveI := is_preserved_by.hg h F,
  haveI := is_preserved_by.hg' h F,
  exact
  { K := F.obj h.K,
    Q := F.obj h.Q,
    H := F.obj h.H,
    i := F.map h.i,
    p := F.map h.p,
    π := F.map h.π,
    ι := F.map h.ι,
    π_ι := map.π_ι h F,
    hi₀ := map.hi₀ h F,
    hp₀ := map.hp₀ h F,
    hi := map.hi h F,
    hp := map.hp h F,
    hπ₀ := map.hπ₀ h F,
    hι₀ := map.hι₀ h F,
    hπ := map.hπ h F,
    hι := map.hι h F, }
end

@[simp]
lemma map_f' (h : homology_full_data S) (F : C ⥤ D) [has_zero_morphisms D]
  [F.preserves_zero_morphisms] [h.is_preserved_by F] :
  (h.map F).f' = F.map h.f' :=
by { symmetry, apply map.hf', }

@[simp]
lemma map_g' (h : homology_full_data S) (F : C ⥤ D) [has_zero_morphisms D]
  [F.preserves_zero_morphisms] [h.is_preserved_by F] :
  (h.map F).g' = F.map h.g' :=
by { symmetry, apply map.hg', }

end map

/-- to be moved -/
@[simps]
def kernel_zero {X Y : C} (f : X ⟶ Y) (hf : f = 0) :
  is_limit (kernel_fork.of_ι (𝟙 X) (show 𝟙 X ≫ f = 0, by rw [hf, comp_zero])) :=
kernel_fork.is_limit.of_ι _ _ (λ A x hx, x) (λ A x hx, comp_id _)
  (λ A x hx b hb, by rw [← hb, comp_id])

/-- to be moved -/
@[simps]
def cokernel_zero {X Y : C} (f : X ⟶ Y) (hf : f = 0) :
  is_colimit (cokernel_cofork.of_π (𝟙 Y) (show f ≫ 𝟙 Y = 0, by rw [hf, zero_comp])) :=
cokernel_cofork.is_colimit.of_π _ _ (λ A x hx, x) (λ A x hx, id_comp _)
  (λ A x hx b hb, by rw [← hb, id_comp])

/-- When the second morphism in a short complex is zero, and the first morphism
has a colimit cokernel cofork, then there is a `homology_full_data` expressing that the homology
is given by this cokernel. -/
@[simp]
def of_colimit_cokernel_cofork (c : cokernel_cofork S.f) (hc : is_colimit c) (hg : S.g = 0) :
  S.homology_full_data :=
{ K := S.X₂,
  Q := c.X,
  H := c.X,
  i := 𝟙 S.X₂,
  p := c.π,
  π := c.π,
  ι := 𝟙 c.X,
  π_ι := by rw [comp_id, id_comp],
  hi₀ := by rw [hg, comp_zero],
  hp₀ := cokernel_cofork.condition _,
  hi := kernel_zero _ hg,
  hp := is_colimit.of_iso_colimit hc (cofork.ext (iso.refl _)
    (by simpa only [iso.refl_hom, cokernel_cofork.π_of_π] using comp_id _)),
  hπ₀ := cokernel_cofork.condition _,
  hι₀ := begin
    dsimp,
    haveI := epi_of_is_colimit_cofork hc,
    simp only [id_comp, hg, ← cancel_epi c.π,
      cofork.is_colimit.π_desc, cofork.π_of_π, comp_zero],
  end,
  hπ := is_colimit.of_iso_colimit hc (cofork.ext (iso.refl _)
    (by simpa only [iso.refl_hom, cokernel_cofork.π_of_π] using comp_id _)),
  hι := kernel_zero _ begin
    dsimp,
    haveI := epi_of_is_colimit_cofork hc,
    simp only [id_comp, hg, ← cancel_epi c.π,
      cofork.is_colimit.π_desc, cofork.π_of_π, comp_zero],
  end }

/-- When the second morphism in a short complex is zero, and the first morphism
has a cokernel, then there is a `homology_full_data` expressing that the homology
is given by this cokernel. -/
@[simp]
def of_has_cokernel [has_cokernel S.f] (hg : S.g = 0) : S.homology_full_data :=
of_colimit_cokernel_cofork S _ (cokernel_is_cokernel S.f) hg

/-- When the first morphism in a short complex is zero, and the second morphism
has a limit kernel fork, then there is a `homology_full_data` expressing that the homology
is given by this kernel. -/
@[simp]
def of_limit_kernel_fork (k : kernel_fork S.g) (hk : is_limit k) (hf : S.f = 0) :
  S.homology_full_data :=
{ K := k.X,
  Q := S.X₂,
  H := k.X,
  i := k.ι,
  p := 𝟙 S.X₂,
  π := 𝟙 k.X,
  ι := k.ι,
  π_ι := by rw [id_comp, comp_id],
  hi₀ := kernel_fork.condition _,
  hp₀ := by rw [hf, zero_comp],
  hi := is_limit.of_iso_limit hk (fork.ext (iso.refl _)
    (by simp only [iso.refl_hom, kernel_fork.ι_of_ι, id_comp])),
  hp := cokernel_zero _ hf,
  hπ₀ := begin
    dsimp,
    haveI := mono_of_is_limit_fork hk,
    simp only [comp_id, hf, ← cancel_mono k.ι,
      fork.is_limit.lift_ι, kernel_fork.ι_of_ι, zero_comp],
  end,
  hι₀ := kernel_fork.condition _,
  hπ := cokernel_zero _ begin
    dsimp,
    haveI := mono_of_is_limit_fork hk,
    simp only [comp_id, hf, ← cancel_mono k.ι,
      fork.is_limit.lift_ι, kernel_fork.ι_of_ι, zero_comp],
  end,
  hι := is_limit.of_iso_limit hk (fork.ext (iso.refl _)
    (by simp only [iso.refl_hom, kernel_fork.ι_of_ι, id_comp])), }

/-- When the first morphism in a short complex is zero, and the second morphism
has a kernel, then there is a `homology_full_data` expressing that the homology
is given by this kernel. -/
@[simp]
def of_has_kernel [has_kernel S.g] (hf : S.f = 0) : S.homology_full_data :=
of_limit_kernel_fork S _ (kernel_is_kernel S.g) hf

/-- When both morphisms of a short complex are zero, there is a `homology_full_data`
expressing that the homology is the middle object. -/
@[simp]
def of_zeros (hf : S.f = 0) (hg : S.g = 0) :
  S.homology_full_data :=
{ K := S.X₂,
  Q := S.X₂,
  H := S.X₂,
  i := 𝟙 S.X₂,
  p := 𝟙 S.X₂,
  π := 𝟙 S.X₂,
  ι := 𝟙 S.X₂,
  π_ι := rfl,
  hi₀ := by rw [hg, comp_zero],
  hp₀ := by rw [hf, zero_comp],
  hi := kernel_zero _ hg,
  hp := cokernel_zero _ hf,
  hπ₀ := by { dsimp, rw [comp_id, hf], },
  hι₀ := by { dsimp, rw [id_comp, hg], },
  hπ := cokernel_zero _ (by simp only [kernel_zero_lift, kernel_fork.ι_of_ι, hf]),
  hι := kernel_zero _ (by simp only [cokernel_zero_desc, cokernel_cofork.π_of_π, hg]), }

instance has_homology_of_has_cokernel {X Y Z : C} (f : X ⟶ Y) [has_cokernel f] :
  has_homology (short_complex.mk f (0 : Y ⟶ Z) comp_zero) :=
has_homology.mk' (of_has_cokernel _ rfl)

instance has_homology_of_has_kernel  {X Y Z : C} (g : Y ⟶ Z) [has_kernel g] :
  has_homology (short_complex.mk (0 : X ⟶ Y) g zero_comp) :=
has_homology.mk' (of_has_kernel _ rfl)

instance has_homology_of_zeros {X Y Z : C} :
  has_homology (short_complex.mk (0 : X ⟶ Y) (0 : Y ⟶ Z) zero_comp) :=
has_homology.mk' (of_zeros _ rfl rfl)

variables {S₁ S₂}

@[simp]
def of_epi_of_is_iso_of_mono (h : homology_full_data S₁) (f : S₁ ⟶ S₂)
  [epi f.τ₁] [is_iso f.τ₂] [mono f.τ₃] :
  homology_full_data S₂ :=
begin
  let i : h.K ⟶ S₂.X₂ := h.i ≫ f.τ₂,
  let p : S₂.X₂ ⟶ h.Q := inv f.τ₂ ≫ h.p,
  have π_ι : h.π ≫ h.ι = i ≫ p := by simp only [h.π_ι, assoc, is_iso.hom_inv_id_assoc],
  have hi₀ : i ≫ S₂.g = 0 := by simp only [assoc, f.comm₂₃, h.hi₀_assoc, zero_comp],
  have hp₀ : S₂.f ≫ p = 0,
  { simp only [p, ← cancel_epi f.τ₁, f.comm₁₂_assoc, is_iso.hom_inv_id_assoc, h.hp₀, comp_zero], },
  have hi : is_limit (kernel_fork.of_ι i hi₀) := kernel_fork.is_limit.of_ι _ _
    (λ A x hx, h.hi.lift (kernel_fork.of_ι (x ≫ inv f.τ₂) (by simp only [← cancel_mono f.τ₃,
      assoc, zero_comp, ← f.comm₂₃, is_iso.inv_hom_id_assoc, hx])))
    (λ A x hx, by simpa only [i, ← cancel_mono (inv f.τ₂), assoc, is_iso.hom_inv_id, comp_id]
        using h.hi.fac _ walking_parallel_pair.zero)
    (λ A x hx b hb, fork.is_limit.hom_ext h.hi begin
      rw fork.is_limit.lift_ι,
      simp only [fork.is_limit.lift_ι, assoc, kernel_fork.ι_of_ι, is_iso.eq_comp_inv, hb],
    end),
  let f' := hi.lift (kernel_fork.of_ι _ S₂.zero),
  have eqf' : f' ≫ i = S₂.f := hi.fac (kernel_fork.of_ι _ S₂.zero) walking_parallel_pair.zero,
  have hf' : f.τ₁ ≫ f' = h.f',
  { simp only [← cancel_mono h.i, ← cancel_mono f.τ₂, assoc, eqf', reassoc_of h.f'_i, f.comm₁₂], },
  have hπ₀ : f' ≫ h.π = 0,
  { simp only [← cancel_epi f.τ₁, reassoc_of hf', h.f'_π, comp_zero], },
  have hπ : is_colimit (cokernel_cofork.of_π h.π hπ₀) := cokernel_cofork.is_colimit.of_π _ _
    (λ A x hx, h.hπ.desc (cokernel_cofork.of_π x begin
      change h.f' ≫ _ = _,
      simp only [← hf', assoc, hx, comp_zero],
    end))
    (λ A x hx, h.hπ.fac _ walking_parallel_pair.one)
    (λ A x hx b hb, cofork.is_colimit.hom_ext h.hπ begin
      rw cofork.is_colimit.π_desc,
      simp only [hb, cokernel_cofork.π_of_π],
    end),
  have hp : is_colimit (cokernel_cofork.of_π p hp₀) := cokernel_cofork.is_colimit.of_π _ _
    (λ A x hx, h.hp.desc (cokernel_cofork.of_π (f.τ₂ ≫ x)
      (by rw [← f.comm₁₂_assoc, hx, comp_zero])))
    (λ A x hx, by simpa only [← cancel_epi f.τ₂, assoc, is_iso.hom_inv_id_assoc] using
        h.hp.fac _ walking_parallel_pair.one)
    (λ A x hx b hb, cofork.is_colimit.hom_ext h.hp begin
      rw cofork.is_colimit.π_desc,
      simp only [cokernel_cofork.π_of_π, ← hb, assoc, is_iso.hom_inv_id_assoc],
    end),
  let g' := hp.desc (cokernel_cofork.of_π _ S₂.zero),
  have eqg' : p ≫ g' = S₂.g := hp.fac (cokernel_cofork.of_π _ S₂.zero) walking_parallel_pair.one,
  have hg' : g' = h.g' ≫ f.τ₃,
  { haveI : epi p := epi_comp _ _,
    rw [← cancel_epi p, eqg'],
    simp only [assoc, h.p_g'_assoc, ← f.comm₂₃, is_iso.inv_hom_id_assoc], },
  have hι₀ : h.ι ≫ g' = 0 := by simp only [hg', ι_g'_assoc, zero_comp],
  have hι : is_limit (kernel_fork.of_ι h.ι hι₀) := kernel_fork.is_limit.of_ι _ _
    (λ A x hx, h.hι.lift (kernel_fork.of_ι x begin
      change x ≫ h.g' = 0,
      simp only [← cancel_mono f.τ₃, assoc, ← hg', hx, zero_comp],
    end))
    (λ A x hx, h.hι.fac _ walking_parallel_pair.zero)
    (λ A x hx b hb, fork.is_limit.hom_ext h.hι begin
      rw fork.is_limit.lift_ι,
      simp only [kernel_fork.ι_of_ι, hb],
    end),
  exact
  { K := h.K,
    Q := h.Q,
    H := h.H,
    i := i,
    p := p,
    π := h.π,
    ι := h.ι,
    π_ι := π_ι,
    hi₀ := hi₀,
    hp₀ := hp₀,
    hi := hi,
    hp := hp,
    hπ₀ := hπ₀,
    hι₀ := hι₀,
    hπ := hπ,
    hι := hι, },
end

example : ℕ := 42
lemma of_epi_of_is_iso_of_mono_τ₁_f' (h : homology_full_data S₁) (f : S₁ ⟶ S₂)
  [epi f.τ₁] [is_iso f.τ₂] [mono f.τ₃] :
  f.τ₁ ≫ (h.of_epi_of_is_iso_of_mono f).f' = h.f' :=
begin
  rw ← cancel_mono (h.of_epi_of_is_iso_of_mono f).i,
  simp only [assoc, f'_i],
  dsimp,
  simp only [f'_i_assoc, f.comm₁₂],
end

lemma of_epi_of_is_iso_of_mono_g' (h : homology_full_data S₁) (f : S₁ ⟶ S₂)
  [epi f.τ₁] [is_iso f.τ₂] [mono f.τ₃] :
  (h.of_epi_of_is_iso_of_mono f).g' = h.g' ≫ f.τ₃ :=
begin
  rw ← cancel_epi (h.of_epi_of_is_iso_of_mono f).p,
  simp only [p_g'],
  dsimp,
  simp only [assoc, p_g'_assoc, is_iso.eq_inv_comp, f.comm₂₃],
end

@[simp]
def of_iso (h : homology_full_data S₁) (e : S₁ ≅ S₂) : homology_full_data S₂ :=
h.of_epi_of_is_iso_of_mono e.hom

end homology_full_data

variables {S₁ S₂}

lemma has_homology_of_iso (e : S₁ ≅ S₂) [h₁ : has_homology S₁] : has_homology S₂ :=
has_homology.mk' (S₁.some_homology_full_data.of_iso e)

lemma has_homology_iff_of_iso (e : S₁ ≅ S₂) : has_homology S₁ ↔ has_homology S₂ :=
begin
  split,
  { introI,
    exact has_homology_of_iso e, },
  { introI,
    exact has_homology_of_iso e.symm, },
end

end short_complex

variable (C)

/-- In order to study the functoriality of the homology of short complexes,
and its behaviour with respect to different choices of `homology_full_data`,
the category `short_complex_with_homology C' is introduced, it consists
of short complexes `S` equipped with `ho : S.homology_full_data`. -/
@[nolint has_nonempty_instance]
structure short_complex_with_homology :=
(S : short_complex C)
(ho : S.homology_full_data)

namespace short_complex_with_homology

open short_complex

variables {C} (Z Z₁ Z₂ Z₃ : short_complex_with_homology C)

instance : has_homology (Z.S) := has_homology.mk' Z.ho

/-- A morphism in `short_complex_with_homology C` consists of a
morphism of short complexes and morphisms on the `K`, `Q` and `H` fields
of the given `homology_full_data`, which satisfies the obvious
compatibilities. -/
@[ext]
structure hom :=
(φ : Z₁.S ⟶ Z₂.S)
(φK : Z₁.ho.K ⟶ Z₂.ho.K)
(φQ : Z₁.ho.Q ⟶ Z₂.ho.Q)
(φH : Z₁.ho.H ⟶ Z₂.ho.H)
(commi : Z₁.ho.i ≫ short_complex.hom.τ₂ φ = φK ≫ Z₂.ho.i)
(commp : Z₁.ho.p ≫ φQ = φ.τ₂ ≫ Z₂.ho.p)
(commf' : Z₁.ho.f' ≫ φK = φ.τ₁ ≫ Z₂.ho.f')
(commg' : Z₁.ho.g' ≫ φ.τ₃ = φQ ≫ Z₂.ho.g')
(commπ : Z₁.ho.π ≫ φH = φK ≫ Z₂.ho.π)
(commι : Z₁.ho.ι ≫ φQ = φH ≫ Z₂.ho.ι)

namespace hom

attribute [reassoc] commi commp commf' commg' commπ commι

/-- The identity morphisms in `short_complex_with_homology C`. -/
@[simps]
def id : hom Z Z :=
⟨𝟙 _, 𝟙 _, 𝟙 _, 𝟙 _, by simp, by simp, by simp, by simp, by simp, by simp⟩

instance : inhabited (hom Z Z) := ⟨hom.id Z⟩

variables {Z₁ Z₂ Z₃}

/-- The composition of morphisms in `short_complex_with_homology C`. -/
@[simps]
def comp (ψ : hom Z₁ Z₂) (ψ' : hom Z₂ Z₃) : hom Z₁ Z₃ :=
⟨ψ.φ ≫ ψ'.φ, ψ.φK ≫ ψ'.φK, ψ.φQ ≫ ψ'.φQ, ψ.φH ≫ ψ'.φH,
  by simp only [comp_τ₂, assoc, hom.commi_assoc, hom.commi],
  by simp only [comp_τ₂, assoc, hom.commp_assoc, hom.commp],
  by simp only [assoc, comp_τ₁, hom.commf'_assoc, hom.commf'],
  by simp only [comp_τ₃, assoc, hom.commg'_assoc, hom.commg'],
  by simp only [assoc, hom.commπ_assoc, hom.commπ],
  by simp only [assoc, hom.commι_assoc, hom.commι]⟩

lemma congr_φ {ψ ψ' : hom Z₁ Z₂} (h : ψ = ψ') : ψ.φ = ψ'.φ := by rw h
lemma congr_φK {ψ ψ' : hom Z₁ Z₂} (h : ψ = ψ') : ψ.φK = ψ'.φK := by rw h
lemma congr_φQ {ψ ψ' : hom Z₁ Z₂} (h : ψ = ψ') : ψ.φQ = ψ'.φQ := by rw h
lemma congr_φH {ψ ψ' : hom Z₁ Z₂} (h : ψ = ψ') : ψ.φH = ψ'.φH := by rw h

end hom

@[simps]
instance : category (short_complex_with_homology C) :=
{ hom := hom,
  id := hom.id,
  comp := λ Z₁ Z₂ Z₃, hom.comp, }

/-- The zero morphisms in `short_complex_with_homology C` -/
@[simps]
def hom.zero : Z₁ ⟶ Z₂ :=
⟨0, 0, 0, 0, by simp, by simp, by simp, by simp, by simp, by simp⟩

@[simps]
instance : has_zero (Z₁ ⟶ Z₂) := ⟨hom.zero _ _⟩

instance : has_zero_morphisms (short_complex_with_homology C) := { }

variable (C)

/-- The obvious functor `short_complex_with_homology C ⥤ short_complex C` which
forgets the `homology_full_data`. -/
@[simps]
def forget : short_complex_with_homology C ⥤ short_complex C :=
{ obj := λ Z, Z.S,
  map := λ Z₁ Z₂ ψ, ψ.φ, }

instance : faithful (forget C) :=
⟨λ Z₁ Z₂ ψ ψ' (h : ψ.φ = ψ'.φ), begin
  have hK : ψ.φK = ψ'.φK := by simp only [← cancel_mono Z₂.ho.i, ← hom.commi, h],
  have hQ : ψ.φQ = ψ'.φQ := by simp only [← cancel_epi Z₁.ho.p, hom.commp, h],
  have hH : ψ.φH = ψ'.φH := by simp only [← cancel_epi Z₁.ho.π, hom.commπ, hK],
  ext1,
  exacts [h, hK, hQ, hH],
end⟩

instance : full (forget C) :=
{ preimage := λ Z₁ Z₂ (φ : Z₁.S ⟶ Z₂.S), begin
    have hK : (Z₁.ho.i ≫ φ.τ₂) ≫ Z₂.S.g = 0,
    { rw [assoc, φ.comm₂₃, Z₁.ho.hi₀_assoc, zero_comp], },
    let φK := Z₂.ho.hi.lift (kernel_fork.of_ι (Z₁.ho.i ≫ φ.τ₂) hK),
    have commi : Z₁.ho.i ≫ φ.τ₂ = φK ≫ Z₂.ho.i := (kernel_fork.is_limit.lift' _ _ hK).2.symm,
    have commf' : Z₁.ho.f' ≫ φK = φ.τ₁ ≫ Z₂.ho.f',
    { rw [← cancel_mono (Z₂.ho.i), assoc, ← commi, Z₁.ho.f'_i_assoc, assoc, Z₂.ho.f'_i,
        φ.comm₁₂], },
    have hQ : Z₁.S.f ≫ φ.τ₂ ≫ Z₂.ho.p = 0,
    { rw [← φ.comm₁₂_assoc, Z₂.ho.hp₀, comp_zero], },
    let φQ := Z₁.ho.hp.desc (cokernel_cofork.of_π (φ.τ₂ ≫ Z₂.ho.p) hQ),
    have commp : Z₁.ho.p ≫ φQ = φ.τ₂ ≫ Z₂.ho.p :=
      (cokernel_cofork.is_colimit.desc' Z₁.ho.hp _ _).2,
    have commg' : Z₁.ho.g' ≫ φ.τ₃ = φQ ≫ Z₂.ho.g' ,
    { rw [← cancel_epi (Z₁.ho.p), reassoc_of commp, Z₁.ho.p_g'_assoc, Z₂.ho.p_g', φ.comm₂₃], },
    have eqH : Z₁.ho.f' ≫ φK ≫ Z₂.ho.π = 0,
    { rw [reassoc_of commf', Z₂.ho.f'_π, comp_zero], },
    let φH := Z₁.ho.hπ'.desc (cokernel_cofork.of_π (φK ≫ Z₂.ho.π) eqH),
    have eqH' : (Z₁.ho.ι ≫ φQ) ≫ Z₂.ho.g' = 0,
    { rw [assoc, ← commg', Z₁.ho.ι_g'_assoc, zero_comp], },
    let φH' := Z₂.ho.hι'.lift (kernel_fork.of_ι _ eqH'),
    have commπ : Z₁.ho.π ≫ φH = φK ≫ Z₂.ho.π :=
      (cokernel_cofork.is_colimit.desc' Z₁.ho.hπ' _ eqH).2,
    have commι : Z₁.ho.ι ≫ φQ = φH' ≫ Z₂.ho.ι :=
      (kernel_fork.is_limit.lift' Z₂.ho.hι' _ eqH').2.symm,
    have φH_eq_φH' : φH = φH',
    { rw [← cancel_epi Z₁.ho.π, ← cancel_mono Z₂.ho.ι, commπ, assoc, assoc, ← commι,
        Z₁.ho.π_ι_assoc, Z₂.ho.π_ι, commp, ← reassoc_of commi], },
    exact ⟨φ, φK, φQ, φH, commi, commp, commf', commg', commπ, by rw [φH_eq_φH', commι]⟩,
  end, }

/-- The homology functor `short_complex_with_homology C ⥤ C`. -/
@[simps]
def functor_H : short_complex_with_homology C ⥤ C :=
{ obj := λ Z, Z.ho.H,
  map := λ Z₁ Z₂ ψ, ψ.φH, }

variable {C}

/-- A morphism in `φ : short_complex C` between objects that are equipped with
`homology_full_data` uniquely lifts as morphism in `short_complex_with_homology`. -/
@[simp]
def forget_preimage {S₁ S₂ : short_complex C} (φ : S₁ ⟶ S₂)
  (H₁ : S₁.homology_full_data) (H₂ : S₂.homology_full_data) :
  mk S₁ H₁ ⟶ mk S₂ H₂ :=
(short_complex_with_homology.forget C).preimage φ

lemma forget_preimage_id {S : short_complex C} (H : S.homology_full_data) :
  forget_preimage (𝟙 S) H H = 𝟙 _ :=
by simpa only [forget_preimage] using preimage_id

lemma forget_preimage_comp {S₁ S₂ S₃ : short_complex C} (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃)
  (H₁ : S₁.homology_full_data) (H₂ : S₂.homology_full_data) (H₃ : S₃.homology_full_data) :
  forget_preimage (φ ≫ φ') H₁ H₃ = forget_preimage φ H₁ H₂ ≫ forget_preimage φ' H₂ H₃ :=
(short_complex_with_homology.forget C).map_injective
  (by simp only [forget_preimage, functor.image_preimage, functor.map_comp])

@[simps]
def map (F : C ⥤ D) [has_zero_morphisms D] [F.preserves_zero_morphisms]
  [Z.ho.is_preserved_by F] :
  short_complex_with_homology D :=
{ S := Z.S.map F,
  ho := Z.ho.map F, }

variables {Z₁ Z₂ Z₃}

@[simps]
def hom.map (F : C ⥤ D) [has_zero_morphisms D] [F.preserves_zero_morphisms]
  (ψ : Z₁ ⟶ Z₂) [Z₁.ho.is_preserved_by F] [Z₂.ho.is_preserved_by F] :
  Z₁.map F ⟶ Z₂.map F :=
{ φ := F.map_short_complex.map ψ.φ,
  φK := F.map ψ.φK,
  φQ := F.map ψ.φQ,
  φH := F.map ψ.φH,
  commi := by { dsimp, simp only [← F.map_comp, hom.commi], },
  commp := by { dsimp, simp only [← F.map_comp, hom.commp], },
  commf' := begin
    dsimp only [map],
    simp only [homology_full_data.map_f', F.map_short_complex_map_τ₁, ← F.map_comp, hom.commf'],
  end,
  commg' := begin
    dsimp only [map],
    simp only [homology_full_data.map_g', F.map_short_complex_map_τ₃, ← F.map_comp, hom.commg'],
  end,
  commπ := by { dsimp, simp only [← F.map_comp, hom.commπ], },
  commι := by { dsimp, simp only [← F.map_comp, hom.commι], }, }

lemma hom.map_id (F : C ⥤ D) [has_zero_morphisms D] [F.preserves_zero_morphisms]
  (Z : short_complex_with_homology C) [Z.ho.is_preserved_by F] : hom.map F (𝟙 Z) = 𝟙 _ :=
by tidy

lemma hom.map_comp (F : C ⥤ D) [has_zero_morphisms D] [F.preserves_zero_morphisms]
  (ψ : Z₁ ⟶ Z₂) (ψ' : Z₂ ⟶ Z₃) [Z₁.ho.is_preserved_by F] [Z₂.ho.is_preserved_by F]
  [Z₃.ho.is_preserved_by F] : hom.map F (ψ ≫ ψ') = hom.map F ψ ≫ hom.map F ψ' :=
by tidy

-- TODO op_equiv : (short_complex_with_homology C)ᵒᵖ ≌ short_complex_with_homology Cᵒᵖ
end short_complex_with_homology

namespace short_complex

variables {C} (S : short_complex C) {S₁ S₂ S₃ : short_complex C}

section
variables [has_homology S] [has_homology S₁] [has_homology S₂] [has_homology S₃]

/-- The map in homology induced by a morphism of short complexes which have homology. -/
def homology_map (φ : S₁ ⟶ S₂) : S₁.homology ⟶ S₂.homology :=
(short_complex_with_homology.forget_preimage φ S₁.some_homology_full_data
    S₂.some_homology_full_data).φH

@[simp]
lemma homology_map_id : homology_map (𝟙 S) = 𝟙 _ :=
short_complex_with_homology.hom.congr_φH
  (short_complex_with_homology.forget_preimage_id _)

@[simp]
lemma homology_map_comp (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) :
  homology_map (φ ≫ φ') = homology_map φ ≫ homology_map φ' :=
short_complex_with_homology.hom.congr_φH
  (short_complex_with_homology.forget_preimage_comp φ φ' _ _ _)

@[simps]
def homology_map_iso (e : S₁ ≅ S₂) : S₁.homology ≅ S₂.homology :=
{ hom := homology_map e.hom,
  inv := homology_map e.inv,
  hom_inv_id' := by rw [← homology_map_comp, e.hom_inv_id, homology_map_id],
  inv_hom_id' := by rw [← homology_map_comp, e.inv_hom_id, homology_map_id], }

end

namespace homology_full_data

variable {S}

/-- Two `homology_full_data S` correspond to isomorphic objects in
the category `short_complex_with_homology`. -/
def uniq (H₁ H₂ : homology_full_data S) :
  short_complex_with_homology.mk S H₁ ≅ short_complex_with_homology.mk S H₂ :=
(short_complex_with_homology.forget C).preimage_iso (iso.refl _)

@[simps]
def uniq_H (H₁ H₂ : homology_full_data S) : H₁.H ≅ H₂.H :=
(short_complex_with_homology.functor_H C).map_iso (uniq H₁ H₂)

@[simp]
lemma uniq_refl (H : homology_full_data S) :
  uniq H H = iso.refl _ :=
begin
  ext1,
  apply (short_complex_with_homology.forget C).map_injective,
  dsimp only [uniq],
  simp only [functor.preimage_iso_hom, iso.refl_hom, preimage_id],
end

@[simp]
lemma uniq_trans (H₁ H₂ H₃ : homology_full_data S) :
  uniq H₁ H₂ ≪≫ uniq H₂ H₃ = uniq H₁ H₃ :=
begin
  ext1,
  apply (short_complex_with_homology.forget C).map_injective,
  dsimp only [uniq],
  simp only [functor.preimage_iso_hom, iso.trans_hom, functor.map_comp, functor.image_preimage,
    iso.refl_hom, comp_id],
end

lemma uniq_symm (H₁ H₂ : homology_full_data S) :
  (uniq H₁ H₂).symm = uniq H₂ H₁ :=
begin
  ext1,
  simpa only [← cancel_mono (uniq H₁ H₂).hom, iso.symm_hom, iso.inv_hom_id, uniq_refl]
    using congr_arg iso.hom (uniq_trans H₂ H₁ H₂).symm,
end

/-- The canonical isomorphism `S.homology ≅ h.H` for `h : homology_full_data S`. -/
def iso_H [has_homology S] (h : homology_full_data S) : S.homology ≅ h.H :=
uniq_H _ _

variable (S)

@[simp]
lemma iso_H_eq_iso_refl [has_homology S] :
  S.some_homology_full_data.iso_H = iso.refl _ :=
begin
  ext1,
  dsimp only [iso_H],
  simpa only [uniq_H_hom, uniq_refl, functor.map_iso_refl, iso.refl_hom],
end

end homology_full_data

/-- When `φ : S₁ ⟶ S₂` is a morphism of short complexes that are equipped with
`H₁ : homology_full_data S₁`, `H₂ : homology_full_data S₂`, this is the datum
of a morphism in `short_complex_with_homology C` betwen the objects corresponding
to `H₁` and `H₂`. This datum allows the computation of the map in homology
induced by `φ`, see `homology_map_full_data.map_eq`. -/
@[ext, nolint has_nonempty_instance]
structure homology_map_full_data
  (φ : S₁ ⟶ S₂) (H₁ : homology_full_data S₁) (H₂ : homology_full_data S₂) :=
(ψ : short_complex_with_homology.mk S₁ H₁ ⟶ short_complex_with_homology.mk S₂ H₂)
(hψ : short_complex_with_homology.hom.φ ψ = φ . obviously)

namespace homology_map_full_data

attribute [simp] hψ

variables (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) (H₁ : homology_full_data S₁) (H₂ : homology_full_data S₂)
  (H₃ : homology_full_data S₃)

@[simps, protected]
def some : homology_map_full_data φ H₁ H₂ :=
{ ψ := short_complex_with_homology.forget_preimage φ H₁ H₂, }

instance : unique (homology_map_full_data φ H₁ H₂) :=
⟨⟨some _ _ _⟩, λ h, begin
  ext1,
  apply (short_complex_with_homology.forget C).map_injective,
  simp only [short_complex_with_homology.forget_map, hψ],
end⟩

variables {φ φ'} {H₁ H₂ H₃}

@[simps]
def comp (m : homology_map_full_data φ H₁ H₂) (m' : homology_map_full_data φ' H₂ H₃) :
  homology_map_full_data (φ ≫ φ') H₁ H₃ :=
{ ψ := m.ψ ≫ m'.ψ }

lemma congr_φH (m : homology_map_full_data φ H₁ H₂) {φ' : S₁ ⟶ S₂}
  (m' : homology_map_full_data φ' H₁ H₂) (h : φ = φ') :
  m.ψ.φH = m'.ψ.φH :=
by { subst h, rw subsingleton.elim m m', }

lemma map_eq [has_homology S₁] [has_homology S₂] (m : homology_map_full_data φ H₁ H₂) :
  homology_map φ = H₁.iso_H.hom ≫ m.ψ.φH ≫ H₂.iso_H.inv :=
begin
  let m₁ : homology_map_full_data (𝟙 S₁) S₁.some_homology_full_data H₁ :=
  { ψ := (S₁.some_homology_full_data.uniq H₁).hom, },
  let m₃ : homology_map_full_data (𝟙 S₂) H₂ S₂.some_homology_full_data :=
  { ψ := (S₂.some_homology_full_data.uniq H₂).inv, },
  exact congr_φH (some _ _ _) (m₁.comp (m.comp m₃)) (by rw [id_comp, comp_id]),
end

@[reassoc]
lemma map_comm_iso_H [has_homology S₁] [has_homology S₂] (m : homology_map_full_data φ H₁ H₂) :
  homology_map φ ≫ H₂.iso_H.hom = H₁.iso_H.hom ≫ m.ψ.φH :=
by simp only [m.map_eq, assoc, iso.inv_hom_id, comp_id]

lemma ψ_φH_eq [has_homology S₁] [has_homology S₂] (m : homology_map_full_data φ H₁ H₂) :
  m.ψ.φH = H₁.iso_H.inv ≫ homology_map φ ≫ H₂.iso_H.hom :=
by rw [m.map_comm_iso_H, iso.inv_hom_id_assoc]

@[simps]
def of_epi_of_is_iso_of_mono (f : S₁ ⟶ S₂) (h : homology_full_data S₁)
  [epi f.τ₁] [is_iso f.τ₂] [mono f.τ₃] :
  homology_map_full_data f h (h.of_epi_of_is_iso_of_mono f) :=
{ ψ :=
  { φ := f,
    φK := 𝟙 _,
    φQ := 𝟙 _,
    φH := 𝟙 _,
    commi := by { dsimp, simp only [id_comp], },
    commf' := by { dsimp, simpa only [comp_id] using (h.of_epi_of_is_iso_of_mono_τ₁_f' f).symm, },
    commp := by { dsimp, simp only [comp_id, is_iso.hom_inv_id_assoc], },
    commg' := by { dsimp, simpa only [id_comp] using (h.of_epi_of_is_iso_of_mono_g' f).symm, },
    commπ := by { dsimp, simp only [comp_id, id_comp], },
    commι := by { dsimp, simp only [comp_id, id_comp], }, }, }

end homology_map_full_data

lemma is_iso_homology_map_of_epi_of_is_iso_of_mono (f : S₁ ⟶ S₂)
  [has_homology S₁] [has_homology S₂]
  [epi f.τ₁] [is_iso f.τ₂] [mono f.τ₃] :
  is_iso (homology_map f) :=
begin
  rw (homology_map_full_data.of_epi_of_is_iso_of_mono f S₁.some_homology_full_data).map_eq,
  dsimp only [homology_map_full_data.of_epi_of_is_iso_of_mono],
  apply_instance,
end

variable (C)

/-- We shall say that a category with homology is a category for which
all short complexes have homology. -/
abbreviation _root_.category_with_homology := ∀ (S : short_complex C), has_homology S

/-- Assuming that all short complexes have homology, this is the homology functor. -/
@[simps]
def homology_functor [category_with_homology C] :
  short_complex C ⥤ C :=
{ obj := λ S, S.homology,
  map := λ S₁ S₂, homology_map, }

variable {C}

def exact : Prop :=
(∃ (h : homology_full_data S), is_zero h.H)

lemma exact_iff [has_homology S] : S.exact ↔ is_zero S.homology :=
begin
  split,
  { rintro ⟨h, h₀⟩,
    exact is_zero.of_iso h₀ (homology_full_data.uniq_H _ _), },
  { exact λ h, ⟨_, h⟩, },
end

lemma exact_iff_homology_iso_zero [has_homology S] [has_zero_object C] :
  S.exact ↔ nonempty (S.homology ≅ 0) :=
begin
  rw exact_iff,
  split,
  { exact λ h, nonempty.intro (is_zero.iso_zero h), },
  { exact λ h, is_zero.of_iso (is_zero_zero C) h.some, },
end

lemma exact_iff_of_iso (e : S₁ ≅ S₂) [has_homology S₁] [has_homology S₂] :
  S₁.exact ↔ S₂.exact :=
begin
-- the assumptions `has_homology` could be removed
  simp only [exact_iff],
  split,
  { exact λ h, is_zero.of_iso h (homology_map_iso e.symm), },
  { exact λ h, is_zero.of_iso h (homology_map_iso e), },
end

/-- If `S : short_complex C`, a candidate computation of the homology of `S` can
be given by the datum of two objects `K` and `H`, where `H` is a part of
a kernel fork of the morphism `S.g : S.X₂ ⟶ S.X₃`, and `H` is a part of a
cokernel cofork of a morphism `f' : S.X₁ ⟶ K` compatible with `f`. This data
shall be an `homology_data S` when the fork and cofork are limit. -/
@[nolint has_nonempty_instance]
structure homology_pre_data :=
(K H : C)
(i : K ⟶ S.X₂)
(f' : S.X₁ ⟶ K)
(π : K ⟶ H)
(f'_i : f' ≫ i = S.f)
(hi₀ : i ≫ S.g = 0)
(hπ₀ : f' ≫ π = 0)

namespace homology_pre_data

attribute [simp, reassoc] f'_i hi₀ hπ₀

variable {S}

@[simps]
def fork (h : homology_pre_data S) : kernel_fork S.g := kernel_fork.of_ι h.i h.hi₀

@[simps]
def cofork (h : homology_pre_data S) : cokernel_cofork h.f' := cokernel_cofork.of_π h.π h.hπ₀

@[simps]
def map (h : homology_pre_data S) (F : C ⥤ D) [has_zero_morphisms D]
  [F.preserves_zero_morphisms] : homology_pre_data (S.map F) :=
{ K := F.obj h.K,
  H := F.obj h.H,
  i := F.map h.i,
  f' := F.map h.f',
  π := F.map h.π,
  f'_i := by simp only [← F.map_comp, h.f'_i, map_f],
  hi₀ := by simp only [map_g, ← F.map_comp, h.hi₀, F.map_zero],
  hπ₀ := by simp only [← F.map_comp, h.hπ₀, F.map_zero], }

end homology_pre_data

/-- If `S : short_complex C`, `h : homology_data S` is a notion that is weaker
than `homology_full_data S`. It consists only of the data of a kernel `h.H` of `S.g`,
and a cokernel `h.K` of the morphism `S.f' : S.X₁ ⟶ h.H` induced by `S.f`. When
`[has_homology S]` holds, it is sufficent in order to compute the homology of `S`. -/
@[nolint has_nonempty_instance]
structure homology_data extends homology_pre_data S :=
(fork_is_limit : is_limit to_homology_pre_data.fork)
(cofork_is_colimit : is_colimit to_homology_pre_data.cofork)

namespace homology_data

variable {S}

instance (h : homology_data S) : mono h.i :=
⟨λ Y l₁ l₂, fork.is_limit.hom_ext h.fork_is_limit⟩

instance (h : homology_data S) : epi h.π :=
⟨λ Y l₁ l₂, cofork.is_colimit.hom_ext h.cofork_is_colimit⟩

@[simps]
def of_full_data (h : homology_full_data S) : homology_data S :=
{ K := h.K,
  H := h.H,
  i := h.i,
  f' := h.f',
  π := h.π,
  f'_i := h.f'_i,
  hi₀ := h.hi₀,
  hπ₀ := h.hπ₀,
  fork_is_limit := h.hi,
  cofork_is_colimit := h.hπ, }

@[simps]
def map (h : homology_data S) (F : C ⥤ D) [has_zero_morphisms D] [F.preserves_zero_morphisms]
  [preserves_limit (parallel_pair S.g 0) F] [preserves_colimit (parallel_pair h.f' 0) F] :
  homology_data (S.map F) :=
{ to_homology_pre_data := h.to_homology_pre_data.map F,
  fork_is_limit := begin
    equiv_rw (is_limit.postcompose_inv_equiv
      (category_theory.limits.parallel_pair.comp_nat_iso F S.g) _).symm,
    exact is_limit.of_iso_limit (is_limit_of_preserves F h.fork_is_limit)
      (cones.ext (iso.refl _) (by { rintro (_|_), tidy, })),
  end,
  cofork_is_colimit := begin
    equiv_rw (is_colimit.precompose_hom_equiv
      (category_theory.limits.parallel_pair.comp_nat_iso F h.f') _).symm,
    exact is_colimit.of_iso_colimit (is_colimit_of_preserves F h.cofork_is_colimit)
      (cocones.ext (iso.refl _) (by { rintro (_|_), tidy, })),
  end, }

end homology_data

end short_complex

/-- In order to allow a convenient way to computation of the homology of
short complexes, and to compute maps in homology, the category
`short_complex_with_homology' C` is introduced. The datum are
similar, but weaker than that of `short_complex_with_homology C`.
An object in this category consists of an object `S : short_complex C`
such that `[has_homology S]` and equipped with `ho : S.homology_data`. -/
@[nolint has_nonempty_instance]
structure short_complex_with_homology' :=
(S : short_complex C)
[hS : S.has_homology]
(ho : S.homology_data)

namespace short_complex_with_homology'

open short_complex

variables {C} (Z Z₁ Z₂ Z₃ : short_complex_with_homology' C)
/-- A morphism in `short_complex_with_homology' C` consists of a
morphism of short complexes and morphisms on the `K`, `H` fields
of the given `homology_data`, which satisfies the obvious
compatibilities. -/

@[ext]
structure hom :=
(φ : Z₁.S ⟶ Z₂.S)
(φK : Z₁.ho.K ⟶ Z₂.ho.K)
(φH : Z₁.ho.H ⟶ Z₂.ho.H)
(commi : Z₁.ho.i ≫ short_complex.hom.τ₂ φ = φK ≫ Z₂.ho.i)
(commf' : Z₁.ho.f' ≫ φK = φ.τ₁ ≫ Z₂.ho.f')
(commπ : Z₁.ho.π ≫ φH = φK ≫ Z₂.ho.π)

namespace hom

attribute [reassoc] commi commf' commπ

/-- The identity morphisms in `short_complex_with_homology' C`. -/
@[simps]
def id : hom Z Z :=
⟨𝟙 _, 𝟙 _, 𝟙 _, by simp, by simp, by simp⟩

instance : inhabited (hom Z Z) := ⟨hom.id Z⟩

variables {Z₁ Z₂ Z₃}

/-- The composition of morphisms in `short_complex_with_homology' C`. -/
@[simps]
def comp (ψ : hom Z₁ Z₂) (ψ' : hom Z₂ Z₃) : hom Z₁ Z₃ :=
⟨ψ.φ ≫ ψ'.φ, ψ.φK ≫ ψ'.φK, ψ.φH ≫ ψ'.φH,
  by simp only [comp_τ₂, assoc, hom.commi_assoc, hom.commi],
  by simp only [comp_τ₁, assoc, hom.commf'_assoc, hom.commf'],
  by simp only [assoc, hom.commπ_assoc, hom.commπ]⟩

lemma congr_φ {ψ ψ' : hom Z₁ Z₂} (h : ψ = ψ') : ψ.φ = ψ'.φ := by rw h
lemma congr_φK {ψ ψ' : hom Z₁ Z₂} (h : ψ = ψ') : ψ.φK = ψ'.φK := by rw h
lemma congr_φH {ψ ψ' : hom Z₁ Z₂} (h : ψ = ψ') : ψ.φH = ψ'.φH := by rw h

end hom

@[simps]
instance : category (short_complex_with_homology' C) :=
{ hom := hom,
  id := hom.id,
  comp := λ Z₁ Z₂ Z₃, hom.comp, }

/-- The zero morphisms in `short_complex_with_homology' C` -/
@[simps]
def hom.zero : Z₁ ⟶ Z₂ :=
⟨0, 0, 0, by simp, by simp, by simp⟩

@[simps]
instance : has_zero (Z₁ ⟶ Z₂) := ⟨hom.zero _ _⟩

instance : has_zero_morphisms (short_complex_with_homology' C) := { }

variable (C)

/-- The obvious functor `short_complex_with_homology' C ⥤ short_complex C` which
forgets the `homology_data`. -/
@[simps]
def forget : short_complex_with_homology' C ⥤ short_complex C :=
{ obj := λ Z, Z.S,
  map := λ Z₁ Z₂ ψ, ψ.φ, }

instance : faithful (forget C) :=
⟨λ Z₁ Z₂ ψ ψ' (h : ψ.φ = ψ'.φ), begin
  have hK : ψ.φK = ψ'.φK := by simp only [← cancel_mono Z₂.ho.i, ← hom.commi, h],
  have hH : ψ.φH = ψ'.φH := by simp only [← cancel_epi Z₁.ho.π, hom.commπ, hK],
  ext1,
  exacts [h, hK, hH],
end⟩

instance : full (forget C) :=
{ preimage := λ Z₁ Z₂ (φ : Z₁.S ⟶ Z₂.S), begin
    have hK : (Z₁.ho.i ≫ φ.τ₂) ≫ Z₂.S.g = 0,
    { rw [assoc, φ.comm₂₃, Z₁.ho.hi₀_assoc, zero_comp], },
    let φK := Z₂.ho.fork_is_limit.lift (kernel_fork.of_ι (Z₁.ho.i ≫ φ.τ₂) hK),
    have commi : Z₁.ho.i ≫ φ.τ₂ = φK ≫ Z₂.ho.i := (kernel_fork.is_limit.lift' _ _ hK).2.symm,
    have commf' : Z₁.ho.f' ≫ φK = φ.τ₁ ≫ Z₂.ho.f',
    { rw [← cancel_mono (Z₂.ho.i), assoc, ← commi, Z₁.ho.f'_i_assoc, assoc, Z₂.ho.f'_i,
        φ.comm₁₂], },
    have eqH : Z₁.ho.f' ≫ φK ≫ Z₂.ho.π = 0,
    { simp only [reassoc_of commf',homology_pre_data.hπ₀, comp_zero], },
    let φH := Z₁.ho.cofork_is_colimit.desc (cokernel_cofork.of_π (φK ≫ Z₂.ho.π) eqH),
    have commπ : Z₁.ho.π ≫ φH = φK ≫ Z₂.ho.π :=
      (cokernel_cofork.is_colimit.desc' Z₁.ho.cofork_is_colimit _ eqH).2,
    exact ⟨φ, φK, φH, commi, commf', commπ⟩,
  end, }

/-- The homology functor `short_complex_with_homology' C ⥤ C`. -/
@[simps]
def functor_H : short_complex_with_homology' C ⥤ C :=
{ obj := λ Z, Z.ho.H,
  map := λ Z₁ Z₂ ψ, ψ.φH, }

variable {C}

/-- A morphism in `φ : short_complex C` between objects that have homology and
are equipped with `homology_data` uniquely lifts as morphism in `short_complex_with_homology'`. -/
@[simp]
def forget_preimage {S₁ S₂ : short_complex C} [has_homology S₁] [has_homology S₂]
  (φ : S₁ ⟶ S₂) (H₁ : S₁.homology_data) (H₂ : S₂.homology_data) :
  mk S₁ H₁ ⟶ mk S₂ H₂ :=
(short_complex_with_homology'.forget C).preimage φ

lemma forget_preimage_id {S : short_complex C} [has_homology S] (H : S.homology_data) :
  forget_preimage (𝟙 S) H H = 𝟙 _ :=
by simpa only [forget_preimage] using preimage_id

lemma forget_preimage_comp {S₁ S₂ S₃ : short_complex C} [has_homology S₁]
  [has_homology S₂] [has_homology S₃] (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃)
  (H₁ : S₁.homology_data) (H₂ : S₂.homology_data) (H₃ : S₃.homology_data) :
  forget_preimage (φ ≫ φ') H₁ H₃ = forget_preimage φ H₁ H₂ ≫ forget_preimage φ' H₂ H₃ :=
(short_complex_with_homology'.forget C).map_injective
  (by simp only [forget_preimage, functor.image_preimage, functor.map_comp])

end short_complex_with_homology'

namespace short_complex

namespace homology_data

variables {S : short_complex C} [has_homology S] {C}

/-- Two `homology_data S` correspond to isomorphic objects in
the category `short_complex_with_homology`. -/
def uniq (H₁ H₂ : homology_data S) :
  short_complex_with_homology'.mk S H₁ ≅ short_complex_with_homology'.mk S H₂ :=
(short_complex_with_homology'.forget C).preimage_iso (iso.refl _)

@[simps]
def uniq_H (H₁ H₂ : homology_data S) : H₁.H ≅ H₂.H :=
(short_complex_with_homology'.functor_H C).map_iso (uniq H₁ H₂)

@[simp]
lemma uniq_refl (H : homology_data S) :
  uniq H H = iso.refl _ :=
begin
  ext1,
  apply (short_complex_with_homology'.forget C).map_injective,
  dsimp only [uniq],
  simp only [functor.preimage_iso_hom, iso.refl_hom, preimage_id],
end

@[simp]
lemma uniq_trans (H₁ H₂ H₃ : homology_data S) :
  uniq H₁ H₂ ≪≫ uniq H₂ H₃ = uniq H₁ H₃ :=
begin
  ext1,
  apply (short_complex_with_homology'.forget C).map_injective,
  dsimp only [uniq],
  simp only [functor.preimage_iso_hom, iso.trans_hom, functor.map_comp, functor.image_preimage,
    iso.refl_hom, comp_id],
end

lemma uniq_symm (H₁ H₂ : homology_data S) :
  (uniq H₁ H₂).symm = uniq H₂ H₁ :=
begin
  ext1,
  simpa only [← cancel_mono (uniq H₁ H₂).hom, iso.symm_hom, iso.inv_hom_id, uniq_refl]
    using congr_arg iso.hom (uniq_trans H₂ H₁ H₂).symm,
end

/-- The canonical isomorphism `S.homology ≅ h.H` for `h : homology_data S`. -/
def iso_H (h : homology_data S) : S.homology ≅ h.H :=
uniq_H (homology_data.of_full_data S.some_homology_full_data) h

end homology_data

end short_complex

namespace short_complex_with_homology

@[simps]
def forget' : short_complex_with_homology C ⥤
  short_complex_with_homology' C :=
{ obj := λ Z, ⟨Z.S, short_complex.homology_data.of_full_data Z.ho⟩,
  map := λ Z₁ Z₂ ψ, ⟨ψ.φ, ψ.φK, ψ.φH, ψ.commi, ψ.commf', ψ.commπ⟩, }

end short_complex_with_homology

namespace category_theory

namespace functor

variables {C} [has_zero_morphisms D] (F : C ⥤ D)
  [preserves_zero_morphisms F] (S : short_complex C)

class preserves_homology_of :=
(condition' [] : ∀ (h : S.homology_full_data), h.is_preserved_by F)

/- TODO : show that it suffices that one of these is sufficient, or more
generally that there is an iff associated to an iso in `short_complex_with_homology`.

TODO: do an alternate weaker version assuming only the kernel/cokernel that
are part of `homology_data` (not full) are preserved. -/

def preserves_homology_of.condition (h : S.homology_full_data)
  [F.preserves_homology_of S] :
  h.is_preserved_by F := preserves_homology_of.condition' F h

@[priority 100]
instance preserves_homology_of_of_preserves_homology [F.preserves_homology] :
  F.preserves_homology_of S := ⟨λ h, infer_instance⟩

def homology_iso [S.has_homology] [(F.map_short_complex.obj S).has_homology]
  [F.preserves_homology_of S] :
  (F.map_short_complex.obj S).homology ≅ F.obj S.homology :=
begin
  letI := preserves_homology_of.condition F S,
  exact (S.some_homology_full_data.map F).iso_H,
end

variable {S}

lemma homology_iso_naturality
  [S.has_homology] [(F.map_short_complex.obj S).has_homology] [F.preserves_homology_of S]
  {S' : short_complex C}
  [S'.has_homology] [(F.map_short_complex.obj S').has_homology] [F.preserves_homology_of S']
  (f : S ⟶ S') :
  short_complex.homology_map (F.map_short_complex.map f) ≫ (F.homology_iso S').hom =
    (F.homology_iso S).hom ≫ F.map (short_complex.homology_map f) :=
begin
  let Z := short_complex_with_homology.mk _ S.some_homology_full_data,
  let Z' := short_complex_with_homology.mk _ S'.some_homology_full_data,
  letI := preserves_homology_of.condition F S Z.ho,
  letI := preserves_homology_of.condition F S' Z'.ho,
  let α : Z ⟶ Z' := (short_complex_with_homology.forget_preimage f _ _),
  let α' : short_complex.homology_map_full_data f _ _ := ⟨α⟩,
  let β' : short_complex.homology_map_full_data (F.map_short_complex.map f) _ _ :=
    ⟨short_complex_with_homology.hom.map F α⟩,
  dsimp only [homology_iso],
  simp only [α'.map_eq, β'.map_eq, F.map_comp, short_complex_with_homology.hom.map_φH,
    short_complex.homology_full_data.iso_H_eq_iso_refl, iso.refl_hom, map_id,
    iso.refl_inv, id_comp, assoc, iso.inv_hom_id],
  erw F.map_id,
  refl,
end

@[simps]
def homology_nat_iso [category_with_homology C] [category_with_homology D] [F.preserves_homology] :
  F.map_short_complex ⋙ short_complex.homology_functor D ≅
    short_complex.homology_functor C ⋙ F :=
nat_iso.of_components (λ S, F.homology_iso S) (λ S₁ S₂ f, homology_iso_naturality F f)

end functor

end category_theory
