import category_theory.limits.preserves.shapes.zero
import category_theory.abelian.homology

noncomputable theory

open category_theory category_theory.category category_theory.limits
  category_theory.preadditive
open_locale zero_object

variables (C : Type*) [category C]

structure short_complex [has_zero_morphisms C] :=
{X₁ X₂ X₃ : C}
(f : X₁ ⟶ X₂)
(g : X₂ ⟶ X₃)
(zero : f ≫ g = 0)

variable {C}

namespace short_complex

section

variable [has_zero_morphisms C]

instance [has_zero_object C] : inhabited (short_complex C) :=
⟨short_complex.mk (0 : 0 ⟶ 0) (0 : 0 ⟶ 0) comp_zero⟩

attribute [simp, reassoc] zero

@[ext]
structure hom (S₁ S₂ : short_complex C) :=
(τ₁ : S₁.X₁ ⟶ S₂.X₁)
(τ₂ : S₁.X₂ ⟶ S₂.X₂)
(τ₃ : S₁.X₃ ⟶ S₂.X₃)
(comm₁₂ : τ₁ ≫ S₂.f = S₁.f ≫ τ₂)
(comm₂₃ : τ₂ ≫ S₂.g = S₁.g ≫ τ₃)

attribute [reassoc] hom.comm₁₂ hom.comm₂₃

variables (S : short_complex C) {S₁ S₂ S₃ : short_complex C}

@[simps]
def hom.id : hom S S := ⟨𝟙 _, 𝟙 _, 𝟙 _, by simp, by simp⟩

instance : inhabited (hom S S) := ⟨hom.id S⟩

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

variables (S₁ S₂)

@[simps]
def hom.zero : S₁ ⟶ S₂ :=
⟨0, 0, 0, by simp, by simp⟩

end

variables [preadditive C] {S₁ S₂ : short_complex C}

@[simps]
def hom.neg (φ : S₁ ⟶ S₂) : S₁ ⟶ S₂ :=
⟨-φ.τ₁, -φ.τ₂, -φ.τ₃,
    by simp only [neg_comp, comp_neg, neg_inj, hom.comm₁₂],
    by simp only [neg_comp, comp_neg, neg_inj, hom.comm₂₃]⟩

@[simps]
def hom.add (φ φ' : S₁ ⟶ S₂) : S₁ ⟶ S₂ :=
⟨φ.τ₁ + φ'.τ₁, φ.τ₂ + φ'.τ₂, φ.τ₃ + φ'.τ₃,
    by simp only [add_comp, comp_add, hom.comm₁₂],
    by simp only [add_comp, comp_add, hom.comm₂₃]⟩

@[simps]
instance : add_comm_group (S₁ ⟶ S₂) :=
{ add := hom.add,
  zero := hom.zero S₁ S₂,
  neg := hom.neg,
  add_assoc := λ φ φ' φ'', by { ext; apply add_assoc, },
  zero_add := λ φ, by { ext; apply zero_add, },
  add_zero := λ φ, by { ext; apply add_zero, },
  add_left_neg := λ φ, by { ext; apply add_left_neg, },
  add_comm := λ φ φ', by { ext; apply add_comm, }, }

instance : preadditive (short_complex C) := { }

variable (S : short_complex C)

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

def f' : S.X₁ ⟶ h.K := h.hi.lift (kernel_fork.of_ι _ S.zero)

def g' : h.Q ⟶ S.X₃ := h.hp.desc (cokernel_cofork.of_π _ S.zero)

@[simp, reassoc]
lemma f'_i : h.f' ≫ h.i = S.f := (kernel_fork.is_limit.lift' _ _ _).2

@[simp, reassoc]
lemma f'_π : h.f' ≫ h.π = 0 := h.hπ₀

@[simp, reassoc]
lemma ι_g' : h.ι ≫ h.g' = 0 := h.hι₀

@[simp, reassoc]
lemma p_g' : h.p ≫ h.g' = S.g := (cokernel_cofork.is_colimit.desc' h.hp _ _).2

@[simp]
def hπ' : is_colimit (cokernel_cofork.of_π h.π h.f'_π) := h.hπ

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

class has_homology : Prop :=
(cond [] : nonempty (homology_full_data S))

def some_homology_full_data [has_homology S] :
  homology_full_data S := (has_homology.cond S).some

def homology [has_homology S] : C := S.some_homology_full_data.H

end short_complex

section preadditive

variables [preadditive C] (C)

@[ext]
structure short_complex_with_homology' :=
(S : short_complex C)
(ho : S.homology_full_data)

namespace short_complex_with_homology'

open short_complex

variables {C} (Z Z₁ Z₂ Z₃ : short_complex_with_homology' C)

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

@[simps]
def id : hom Z Z :=
⟨𝟙 _, 𝟙 _, 𝟙 _, 𝟙 _, by simp, by simp, by simp, by simp, by simp, by simp⟩

instance : inhabited (hom Z Z) := ⟨hom.id Z⟩

variables {Z₁ Z₂ Z₃}

@[simps]
def comp (ψ : hom Z₁ Z₂) (ψ' : hom Z₂ Z₃) : hom Z₁ Z₃ :=
⟨ψ.φ ≫ ψ'.φ, ψ.φK ≫ ψ'.φK, ψ.φQ ≫ ψ'.φQ, ψ.φH ≫ ψ'.φH,
  by simp only [comp_τ₂, assoc, hom.commi_assoc, hom.commi],
  by simp only [comp_τ₂, assoc, hom.commp_assoc, hom.commp],
  by simp only [assoc, comp_τ₁, hom.commf'_assoc, hom.commf', comp_τ₁],
  by simp only [comp_τ₃, assoc, hom.commg'_assoc, hom.commg'],
  by simp only [assoc, hom.commπ_assoc, hom.commπ],
  by simp only [assoc, hom.commι_assoc, hom.commι]⟩

lemma congr_φ {ψ ψ' : hom Z₁ Z₂} (h : ψ = ψ') : ψ.φ = ψ'.φ := by rw h
lemma congr_φK {ψ ψ' : hom Z₁ Z₂} (h : ψ = ψ') : ψ.φK = ψ'.φK := by rw h
lemma congr_φQ {ψ ψ' : hom Z₁ Z₂} (h : ψ = ψ') : ψ.φQ = ψ'.φQ := by rw h
lemma congr_φH {ψ ψ' : hom Z₁ Z₂} (h : ψ = ψ') : ψ.φH = ψ'.φH := by rw h

end hom

instance : category (short_complex_with_homology' C) :=
{ hom := hom,
  id := hom.id,
  comp := λ Z₁ Z₂ Z₃, hom.comp, }

variable (C)

@[simps]
def forget : short_complex_with_homology' C ⥤ short_complex C :=
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
  end,
  witness' := λ Z₁ Z₂ φ, rfl, }

variable {C}

@[simp]
def forget_preimage {S₁ S₂ : short_complex C} (φ : S₁ ⟶ S₂)
  (H₁ : S₁.homology_full_data) (H₂ : S₂.homology_full_data) :
  mk S₁ H₁ ⟶ mk S₂ H₂ :=
(short_complex_with_homology'.forget C).preimage φ

lemma forget_preimage_id {S : short_complex C} (H : S.homology_full_data) :
  forget_preimage (𝟙 S) H H = 𝟙 _ :=
by simpa only [forget_preimage] using preimage_id

lemma forget_preimage_comp {S₁ S₂ S₃ : short_complex C} (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃)
  (H₁ : S₁.homology_full_data) (H₂ : S₂.homology_full_data) (H₃ : S₃.homology_full_data) :
  forget_preimage (φ ≫ φ') H₁ H₃ = forget_preimage φ H₁ H₂ ≫ forget_preimage φ' H₂ H₃ :=
(short_complex_with_homology'.forget C).map_injective
  (by simp only [forget_preimage, functor.image_preimage, functor.map_comp])

end short_complex_with_homology'

end preadditive

namespace short_complex

section preadditive

variables [preadditive C] {C} (S : short_complex C) {S₁ S₂ S₃ : short_complex C}
  [has_homology S] [has_homology S₁] [has_homology S₂] [has_homology S₃]

def homology_map (φ : S₁ ⟶ S₂) : S₁.homology ⟶ S₂.homology :=
(short_complex_with_homology'.forget_preimage φ S₁.some_homology_full_data
    S₂.some_homology_full_data).φH

@[simp]
lemma homology_id : homology_map (𝟙 S) = 𝟙 _ :=
short_complex_with_homology'.hom.congr_φH
  (short_complex_with_homology'.forget_preimage_id _)

@[simp]
lemma homology_map_comp (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) :
  homology_map (φ ≫ φ') = homology_map φ ≫ homology_map φ' :=
short_complex_with_homology'.hom.congr_φH
  (short_complex_with_homology'.forget_preimage_comp φ φ' _ _ _)

@[simps]
def homology_functor [∀ (S : short_complex C), has_homology S] :
  short_complex C ⥤ C :=
{ obj := λ S, S.homology,
  map := λ S₁ S₂, homology_map, }

end preadditive

section abelian

-- change kernel.lift to get better definitional properties
abbreviation kernel.lift' {C : Type*} [category C] [has_zero_morphisms C]
  {W X Y : C} (f : X ⟶ Y) [has_kernel f] (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f :=
(kernel_is_kernel f).lift (kernel_fork.of_ι k h)

@[simp, reassoc]
lemma kernel.lift'_ι {C : Type*} [category C] [has_zero_morphisms C]
  {W X Y : C} (f : X ⟶ Y) [has_kernel f] (k : W ⟶ X) (h : k ≫ f = 0) :
  kernel.lift' f k h ≫ kernel.ι f = k :=
(kernel_is_kernel f).fac (kernel_fork.of_ι k h) walking_parallel_pair.zero

abbreviation cokernel.desc' {C : Type*} [category C] [has_zero_morphisms C]
  {W X Y : C} (f : X ⟶ Y) [has_cokernel f] (k : Y ⟶ W) (h : f ≫ k = 0) : cokernel f ⟶ W :=
(cokernel_is_cokernel f).desc (cokernel_cofork.of_π k h)

@[simp, reassoc]
lemma cokernel.π_desc' {C : Type*} [category C] [has_zero_morphisms C]
  {W X Y : C} (f : X ⟶ Y) [has_cokernel f] (k : Y ⟶ W) (h : f ≫ k = 0) :
  cokernel.π f ≫ cokernel.desc' f k h = k :=
(cokernel_is_cokernel f).fac (cokernel_cofork.of_π k h) walking_parallel_pair.one

@[priority 100]
instance abelian_has_homology [abelian C] : ∀ (S : short_complex C), has_homology S :=
λ S, begin
  let K := kernel S.g,
  let Q := cokernel S.f,
  let f' : S.X₁ ⟶ K := kernel.lift' _ _ S.zero,
  let g' : Q ⟶ S.X₃ := cokernel.desc' _ _ S.zero,
  let H := cokernel f',
  let i : K ⟶ S.X₂ := kernel.ι S.g,
  let p : S.X₂ ⟶ Q := cokernel.π S.f,
  let π : K ⟶ H := cokernel.π f',
  let ι : H ⟶ Q := cokernel.desc' _ (i ≫ p)
      (by simp only [kernel.lift'_ι_assoc, cokernel.condition]),
  have π_ι : π ≫ ι = i ≫ p := cokernel.π_desc' _ _ _,
  have hi₀ : i ≫ S.g = 0 := kernel.condition _,
  have hp₀ : S.f ≫ p = 0 := cokernel.condition _,
  let hi : is_limit (kernel_fork.of_ι i hi₀) := kernel_is_kernel _,
  let hp : is_colimit (cokernel_cofork.of_π p hp₀) := cokernel_is_cokernel _,
  have hπ₀ : f' ≫ π = 0 := cokernel.condition _,
  have hι₀ : ι ≫ g' = 0,
  { simp only [← cancel_epi (cokernel.π (kernel.lift' S.g S.f S.zero)),
      cokernel.π_desc'_assoc, assoc, cokernel.π_desc', kernel.condition, comp_zero], },
  let hπ : is_colimit (cokernel_cofork.of_π π hπ₀) := cokernel_is_cokernel _,
  /- The rest of the proof is the verification of `hι`.

    The main idea is to construct an isomorphism `e : H ≅ kernel g'`. (By definition,
    `H` is the cokernel of `f'`.), which is a composition of various isomorphisms
    `H ≅ cokernel α`, `e₁ : cokernel α ≅ abelian.coimage (i ≫ p)`,
    the isomorphism `abelian.coimage_iso_image (i ≫ p)`,
    `e₂ : abelian.image (i ≫ p) ≅ kernel β`, and `kernel β ≅ kernel g'`.

    Here `α : B ⟶ K` is the canonical map from `B := abelian.image S.f`,
    i.e. `α` is the inclusion of cycles in boundaries). The isomorphism
    `H ≅ cokernel α` (which is `cokernel f' ≅ cokernel α`) is easily obtained
    from the factorisation `fac₁ : f' = f'' ≫ α` and the fact that `f''` is an epi).
    The isomorphism `e₁ : cokernel α ≅ abelian.coimage (i ≫ p)` follows from the
    definition of the coimage as a cokernel and the construction of an
    isomorphism `B ≅ kernel (i ≫ p)`.

    Similarly `β : Q ⟶ B'` is the canonical map to `B' := abelian.coimage S.g`, and
    all the arguments are dual. -/
  let B := abelian.image S.f,
  let B' := abelian.coimage S.g,
  let i' : B ⟶ S.X₂ := abelian.image.ι S.f,
  let p' : S.X₂ ⟶ B' := abelian.coimage.π S.g,
  let f'' : S.X₁ ⟶ B := abelian.factor_thru_image S.f,
  let g'' : B' ⟶ S.X₃ := abelian.factor_thru_coimage S.g,
  let α : B ⟶ K := kernel.lift' _ i'
    (by simp only [← cancel_epi f'', abelian.image.fac_assoc, zero, comp_zero]),
  let β : Q ⟶ B' := cokernel.desc' _ p'
    (by simp only [← cancel_mono g'', assoc, cokernel.π_desc, zero, zero_comp]),
  have fac₁ : f' = f'' ≫ α,
  { simp only [← cancel_mono i, assoc, abelian.image.fac, kernel.lift'_ι], },
  have fac₂ : β ≫ g'' = g',
  { simp only [← cancel_epi p, cokernel.π_desc', cokernel.π_desc, cokernel.π_desc'_assoc], },
  haveI : mono (α ≫ i) := by { rw [show α ≫ i = i', by simp], apply_instance, },
  haveI : epi (p ≫ β) := by  { rw [show p ≫ β = p', by simp], apply_instance, },
  haveI : mono α := mono_of_mono α i,
  haveI : epi β := epi_of_epi p β,
  let hB : is_limit (kernel_fork.of_ι α (show α ≫ i ≫ p = 0, by simp)) :=
    kernel_fork.is_limit.of_ι _ _
      (λ A k hk, kernel.lift' _ (k ≫ i) (by rw [assoc, hk]))
      (λ A k hk, by simp only [← cancel_mono i, assoc, kernel.lift'_ι])
      (λ A k hk b hb, by simp only [← cancel_mono α, ← cancel_mono i, hb, assoc, kernel.lift'_ι]),
  let hB' : is_colimit (cokernel_cofork.of_π β (show (i ≫ p) ≫ β = 0, by simp)) :=
    cokernel_cofork.is_colimit.of_π _ _
      (λ A k hk, cokernel.desc' _ (p ≫ k) (by rw [← assoc, hk]))
      (λ A k hk, by simp only [← cancel_epi p, cokernel.π_desc'_assoc, cokernel.π_desc'])
      (λ A k hk b hb, by simp only [← cancel_epi β, ← cancel_epi p, hb,
          cokernel.π_desc'_assoc, cokernel.π_desc']),
  let eB : B ≅ kernel (i ≫ p) :=
    is_limit.cone_point_unique_up_to_iso hB (kernel_is_kernel (i ≫ p)),
  let eB' : cokernel (i ≫ p) ≅ B' :=
    is_colimit.cocone_point_unique_up_to_iso (cokernel_is_cokernel (i ≫ p)) hB',
  have fac₃ : eB.hom ≫ kernel.ι (i ≫ p) = α :=
    is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_parallel_pair.zero,
  have fac₄ : cokernel.π (i ≫ p) ≫ eB'.hom = β :=
    is_colimit.comp_cocone_point_unique_up_to_iso_hom
      (cokernel_is_cokernel _) _ walking_parallel_pair.one,
  let e₁ : cokernel α ≅ abelian.coimage (i ≫ p) :=
    cokernel_iso_of_eq fac₃.symm ≪≫ cokernel_epi_comp _ _,
  let e₂ : abelian.image (i ≫ p) ≅ kernel β :=
    (kernel_comp_mono _ _).symm ≪≫ kernel_iso_of_eq fac₄,
  let e : H ≅ kernel g' := cokernel_iso_of_eq fac₁ ≪≫ cokernel_epi_comp _ _ ≪≫ e₁ ≪≫
    abelian.coimage_iso_image (i ≫ p) ≪≫ e₂ ≪≫
    (kernel_comp_mono _ _ ).symm ≪≫ kernel_iso_of_eq fac₂,
  have he : e.hom ≫ kernel.ι _ = ι,
  { ext,
    dsimp,
    simp only [lift_comp_kernel_iso_of_eq_hom, cokernel_iso_of_eq_hom_comp_desc_assoc, assoc,
      kernel.lift_ι, cokernel.π_desc_assoc, abelian.coimage_image_factorisation,
      cokernel.π_desc'], },
  let hι : is_limit (kernel_fork.of_ι ι hι₀) := is_limit.of_iso_limit (kernel_is_kernel _)
    (by { symmetry, exact fork.ext e he, }),
  exact ⟨nonempty.intro ⟨K, Q, H, i, p, π, ι, π_ι, hi₀, hp₀, hi, hp, hπ₀, hι₀, hπ, hι⟩⟩,
end

example : ℕ := 42

instance [abelian C] (S : short_complex C) : inhabited (S.homology_full_data) :=
⟨(has_homology.cond S).some⟩

end abelian

end short_complex

namespace short_complex_with_homology'

instance [abelian C] : inhabited (short_complex_with_homology' C) := ⟨mk default default⟩

end short_complex_with_homology'
