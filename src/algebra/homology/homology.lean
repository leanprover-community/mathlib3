/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology.image_to_kernel
import algebra.homology.homological_complex
import category_theory.graded_object
import algebra.homology.short_complex.preserves_homology
import algebra.homology.exact

/-!
# The homology of a complex

Given `C : homological_complex V c`, we have `C.cycles i` and `C.boundaries i`,
both defined as subobjects of `C.X i`.

We show these are functorial with respect to chain maps,
as `C.cycles_map f i` and `C.boundaries_map f i`.

As a consequence we construct `homology_functor i : homological_complex V c ⥤ V`,
computing the `i`-th homology.
-/

universes v u

open category_theory category_theory.limits category_theory.category

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [has_zero_morphisms V]
  {W : Type*} [category W] [has_zero_morphisms W]
variables {c : complex_shape ι} (C : homological_complex V c)

open_locale classical zero_object
noncomputable theory


namespace complex_shape

variable (c)

lemma not_rel_of_not_rel_next {i : ι} (hi : ¬c.rel i (c.next i)) : ¬c.rel i i :=
begin
  intro hi',
  rw c.next_eq' hi' at hi,
  exact hi hi',
end

lemma not_rel_of_not_prev_rel {i : ι} (hi : ¬c.rel (c.prev i) i) : ¬c.rel i i :=
begin
  intro hi',
  rw c.prev_eq' hi' at hi,
  exact hi hi',
end

end complex_shape

namespace homological_complex

/-section cycles
variables [has_kernels V]

/-- The cycles at index `i`, as a subobject. -/
abbreviation cycles (i : ι) : subobject (C.X i) :=
kernel_subobject (C.d_from i)

lemma cycles_eq_kernel_subobject {i j : ι} (r : c.rel i j) :
  C.cycles i = kernel_subobject (C.d i j) :=
C.kernel_from_eq_kernel r

/--
The underlying object of `C.cycles i` is isomorphic to `kernel (C.d i j)`,
for any `j` such that `rel i j`.
-/
def cycles_iso_kernel {i j : ι} (r : c.rel i j) :
  (C.cycles i : V) ≅ kernel (C.d i j) :=
subobject.iso_of_eq _ _ (C.cycles_eq_kernel_subobject r) ≪≫
  kernel_subobject_iso (C.d i j)

lemma cycles_eq_top {i} (h : ¬c.rel i (c.next i)) : C.cycles i = ⊤ :=
begin
  rw eq_top_iff,
  apply le_kernel_subobject,
  rw [C.d_from_eq_zero h, comp_zero],
end

end cycles

section boundaries
variables [has_images V]

/-- The boundaries at index `i`, as a subobject. -/
abbreviation boundaries (C : homological_complex V c) (j : ι) : subobject (C.X j) :=
image_subobject (C.d_to j)

lemma boundaries_eq_image_subobject [has_equalizers V] {i j : ι} (r : c.rel i j) :
  C.boundaries j = image_subobject (C.d i j) :=
C.image_to_eq_image r

/--
The underlying object of `C.boundaries j` is isomorphic to `image (C.d i j)`,
for any `i` such that `rel i j`.
-/
def boundaries_iso_image [has_equalizers V] {i j : ι} (r : c.rel i j) :
  (C.boundaries j : V) ≅ image (C.d i j) :=
subobject.iso_of_eq _ _ (C.boundaries_eq_image_subobject r) ≪≫
  image_subobject_iso (C.d i j)

lemma boundaries_eq_bot [has_zero_object V] {j} (h : ¬c.rel (c.prev j) j) :
  C.boundaries j = ⊥ :=
begin
  rw eq_bot_iff,
  refine image_subobject_le _ 0 _,
  rw [C.d_to_eq_zero h, zero_comp],
end

end boundaries

section
variables [has_kernels V] [has_images V]

lemma boundaries_le_cycles (C : homological_complex V c) (i : ι) :
  C.boundaries i ≤ C.cycles i :=
image_le_kernel _ _ (C.d_to_comp_d_from i)

/--
The canonical map from `boundaries i` to `cycles i`.
-/
abbreviation boundaries_to_cycles (C : homological_complex V c) (i : ι) :
  (C.boundaries i : V) ⟶ (C.cycles i : V) :=
image_to_kernel _ _ (C.d_to_comp_d_from i)

/-- Prefer `boundaries_to_cycles`. -/
@[simp] lemma image_to_kernel_as_boundaries_to_cycles (C : homological_complex V c) (i : ι) (h) :
  (C.boundaries i).of_le (C.cycles i) h = C.boundaries_to_cycles i :=
rfl-/

--variables [has_cokernels V]

/--
The homology of a complex at index `i`.
-/

variables (V c)

@[simps]
def short_complex_functor (i : ι) : homological_complex V c ⥤ short_complex V :=
{ obj := λ C, short_complex.mk (C.d_to i) (C.d_from i) (C.d_to_comp_d_from i),
  map := λ C₁ C₂ φ, ⟨φ.f _, φ.f _, φ.f _, by simp, by simp⟩, }

@[simps]
def short_complex_functor' (i j k : ι)  :
  homological_complex V c ⥤ short_complex V :=
{ obj := λ C, short_complex.mk (C.d i j) (C.d j k) (C.d_comp_d i j k),
  map := λ C₁ C₂ φ, ⟨φ.f _, φ.f _, φ.f _, by simp, by simp⟩, }

variables {V c}

abbreviation sc (C : homological_complex V c) (i j k : ι) := (short_complex_functor' V c i j k).obj C
abbreviation sc' (C : homological_complex V c) (i : ι) :=
(short_complex_functor' V c (c.prev i) i (c.next i)).obj C

abbreviation has_homology (C : homological_complex V c) (i : ι) :=
((short_complex_functor V c i).obj C).has_homology

abbreviation homology_data (C : homological_complex V c) (i : ι) :=
((short_complex_functor V c i).obj C).homology_data

abbreviation left_homology_data (C : homological_complex V c) (i : ι) :=
((short_complex_functor V c i).obj C).left_homology_data

abbreviation right_homology_data (C : homological_complex V c) (i : ι) :=
((short_complex_functor V c i).obj C).right_homology_data

abbreviation homology_map_data {C₁ C₂ : homological_complex V c} (φ : C₁ ⟶ C₂) (i : ι)
  (h₁ : C₁.homology_data i) (h₂ : C₂.homology_data i) :=
short_complex.homology_map_data ((short_complex_functor V c i).map φ) h₁ h₂

instance has_homology_sc'_of_has_homology
  (C : homological_complex V c) (i : ι) [h : C.has_homology i] :
  (C.sc' i).has_homology := h

lemma has_homology.iff (C : homological_complex V c) (i : ι) :
  C.has_homology i ↔
    (short_complex.mk (C.d_to i) (C.d_from i) (C.d_to_comp_d_from i)).has_homology :=
by refl

abbreviation homology (C : homological_complex V c) (i : ι) [C.has_homology i] : V :=
((short_complex_functor V c i).obj C).homology

abbreviation _root_.homology_map {C D : homological_complex V c}
  (f : C ⟶ D) (i : ι) [C.has_homology i] [D.has_homology i] :
  C.homology i ⟶ D.homology i :=
short_complex.homology_map ((short_complex_functor V c i).map f)

@[simp]
lemma _root_.homology_map_id (C : homological_complex V c) (i : ι) [C.has_homology i] :
  homology_map (𝟙 C) i = 𝟙 _ := short_complex.homology_map_id _

@[simp]
lemma _root_.homology_map_comp {C D E : homological_complex V c} (f : C ⟶ D) (g : D ⟶ E)
  (i : ι) [C.has_homology i] [D.has_homology i] [E.has_homology i]:
  homology_map (f ≫ g) i = homology_map f i ≫ homology_map g i :=
begin
  change short_complex.homology_map _ = _,
  rw functor.map_comp,
  apply short_complex.homology_map_comp,
end

variables (V c)

@[simps]
def _root_.homology_functor [category_with_homology V] (i : ι) : homological_complex V c ⥤ V :=
  short_complex_functor V c i ⋙ short_complex.homology_functor V

variables {V c}

lemma _root_.homology_functor_obj' [category_with_homology V] (C : homological_complex V c) (i : ι) :
  (homology_functor V c i).obj C = C.homology i := rfl

lemma _root_.homology_functor_map' [category_with_homology V] {C D : homological_complex V c}
  (f : C ⟶ D) (i : ι) : (homology_functor V c i).map f = homology_map f i := rfl

variables (V c)

def short_complex_functor_nat_iso {i j k : ι} (hij : c.rel i j) (hjk : c.rel j k) :
  short_complex_functor V c j ≅ short_complex_functor' V c i j k :=
nat_iso.of_components (λ C, short_complex.mk_iso (C.X_prev_iso hij) (iso.refl _)
  (C.X_next_iso hjk) (by { dsimp, rw [comp_id, C.d_to_eq hij], })
  (by { dsimp, rw [id_comp, d_from_comp_X_next_iso], }))
  (λ C₁ C₂ φ, begin
    ext,
    { obtain rfl := c.prev_eq' hij,
      dsimp [X_prev_iso],
      rw [comp_id, id_comp], },
    { dsimp, simp only [comp_id, id_comp], },
    { obtain rfl := c.next_eq' hjk,
      dsimp [X_next_iso],
      rw [comp_id, id_comp], },
  end)

variables {V c}

@[simp]
def homology_data_mk (C : homological_complex V c)
  {i j k : ι} (hij : c.rel i j) (hjk : c.rel j k) (h : (C.sc i j k).homology_data) :
  C.homology_data j :=
short_complex.homology_data.of_iso ((short_complex_functor_nat_iso V c hij hjk).app C).symm h

lemma X_next_iso_self_naturality {C₁ C₂ : homological_complex V c} (φ : C₁ ⟶ C₂)
  (j : ι) (hj : ¬c.rel j (c.next j)) :
  φ.f (c.next j) ≫ (C₂.X_next_iso_self hj).hom = (C₁.X_next_iso_self hj).hom ≫ φ.f j :=
begin
  suffices : ∀ (j k : ι) (eq : j = k),
    φ.f k ≫ (eq_to_iso (show C₂.X k = C₂.X j, by rw eq)).hom = (eq_to_iso (by rw eq)).hom ≫ φ.f j,
  { apply this,
    dsimp [complex_shape.next],
    rw dif_neg,
    rintro ⟨k, hk⟩,
    apply hj,
    simpa only [c.next_eq' hk] using hk, },
  rintros j k rfl,
  simp only [eq_to_iso_refl, iso.refl_hom, comp_id, id_comp],
end

lemma X_prev_iso_self_naturality {C₁ C₂ : homological_complex V c} (φ : C₁ ⟶ C₂)
  (i : ι) (hi : ¬c.rel (c.prev i) i) :
  φ.f (c.prev i) ≫ (C₂.X_prev_iso_self hi).hom = (C₁.X_prev_iso_self hi).hom ≫ φ.f i :=
begin
  suffices : ∀ (j k : ι) (eq : j = k),
    φ.f k ≫ (eq_to_iso (show C₂.X k = C₂.X j, by rw eq)).hom = (eq_to_iso (by rw eq)).hom ≫ φ.f j,
  { apply this,
    dsimp [complex_shape.prev],
    rw dif_neg,
    rintro ⟨k, hk⟩,
    apply hi,
    simpa only [c.prev_eq' hk] using hk, },
  rintros j k rfl,
  simp only [eq_to_iso_refl, iso.refl_hom, comp_id, id_comp],
end

variables (V c)

@[simps]
def short_complex_functor_nat_iso₁₂ {i j : ι} (hij : c.rel i j) (hj : ¬c.rel j (c.next j)) :
  short_complex_functor V c j ≅ short_complex_functor' V c i j j :=
nat_iso.of_components (λ C, short_complex.mk_iso (C.X_prev_iso hij) (iso.refl _) (C.X_next_iso_self hj)
  (by { dsimp, simp only [comp_id, C.d_to_eq hij], })
  (by { dsimp, simp only [comp_zero, d_from_comp_X_next_iso_self, id_comp,
    C.shape j j (c.not_rel_of_not_rel_next hj)], }))
  (λ C₁ C₂ φ, begin
    ext,
    { obtain rfl := c.prev_eq' hij,
      dsimp [X_prev_iso],
      rw [comp_id, id_comp], },
    { dsimp, simp only [comp_id, id_comp], },
    { apply X_next_iso_self_naturality, },
  end)

@[simps]
def short_complex_functor_nat_iso₂₃ {i j : ι} (hij : c.rel i j) (hi : ¬c.rel (c.prev i) i) :
  short_complex_functor V c i ≅ short_complex_functor' V c i i j :=
nat_iso.of_components (λ C, short_complex.mk_iso (C.X_prev_iso_self hi) (iso.refl _) (C.X_next_iso hij)
  (by { dsimp, simp only [comp_zero, comp_id, C.d_to_eq_zero hi,
      C.shape i i (c.not_rel_of_not_prev_rel hi)], })
  (by { dsimp, simp only [id_comp, d_from_comp_X_next_iso]}))
  (λ C₁ C₂ φ, begin
    ext,
    { apply X_prev_iso_self_naturality, },
    { dsimp, simp only [comp_id, id_comp], },
    { obtain rfl := c.next_eq' hij,
      dsimp [X_next_iso],
      rw [comp_id, id_comp], },
  end)

variables {V c}

@[simp]
def homology_data_of_cokernel'
  (C : homological_complex V c) {i j : ι} (hij : c.rel i j)
  (hj : ¬c.rel j (c.next j)) (cc : cokernel_cofork (C.d i j)) (hcc : is_colimit cc) :
  C.homology_data j :=
begin
  refine short_complex.homology_data.of_colimit_cokernel_cofork _ (C.d_from_eq_zero hj)
    (cokernel_cofork.of_π cc.π _) _,
  { dsimp,
    simp only [C.d_to_eq hij, assoc, cc.condition, comp_zero], },
  { have h := c.prev_eq' hij,
    subst h,
    exact is_colimit.of_iso_colimit hcc (cofork.ext (iso.refl _) (by tidy)), },
end

@[simp]
def homology_data_of_cokernel
  (C : homological_complex V c) {i j : ι} (hij : c.rel i j)
  (hj : ¬c.rel j (c.next j)) [has_cokernel (C.d i j)] :
  C.homology_data j :=
C.homology_data_of_cokernel' hij hj _ (cokernel_is_cokernel (C.d i j))

def homology_map_data_of_cokernel'
  {C₁ C₂ : homological_complex V c} (φ : C₁ ⟶ C₂) {i j : ι} (hij : c.rel i j)
  (hj : ¬c.rel j (c.next j)) (cc₁ : cokernel_cofork (C₁.d i j)) (hcc₁ : is_colimit cc₁)
  (cc₂ : cokernel_cofork (C₂.d i j)) (hcc₂ : is_colimit cc₂) (f : cc₁.X ⟶ cc₂.X)
  (comm : φ.f j ≫ cc₂.π = cc₁.π ≫ f):
  homology_map_data φ j (C₁.homology_data_of_cokernel' hij hj cc₁ hcc₁)
    (C₂.homology_data_of_cokernel' hij hj cc₂ hcc₂) :=
short_complex.homology_map_data.of_colimit_cokernel_coforks _ _ _ _ _ _ _ _ comm

def homology_map_data_of_cokernel
  {C₁ C₂ : homological_complex V c} (φ : C₁ ⟶ C₂) {i j : ι} (hij : c.rel i j)
  (hj : ¬c.rel j (c.next j)) [has_cokernel (C₁.d i j)] [has_cokernel (C₂.d i j)] :
  homology_map_data φ j (C₁.homology_data_of_cokernel hij hj)
    (C₂.homology_data_of_cokernel hij hj) :=
short_complex.homology_map_data.of_colimit_cokernel_coforks _ _ _ _ _ _ _
  (cokernel.map _ _ _ _ (φ.comm i j).symm) (by simp)

@[simps]
def homology_iso_cokernel' (C : homological_complex V c) {i j : ι} (hij : c.rel i j)
  (hj : ¬c.rel j (c.next j)) [C.has_homology j] (cc : cokernel_cofork (C.d i j)) (hcc : is_colimit cc) :
  C.homology j ≅ cc.X :=
(C.homology_data_of_cokernel' hij hj cc hcc).homology_iso

def homology_iso_cokernel (C : homological_complex V c) {i j : ι} (hij : c.rel i j)
  (hj : ¬c.rel j (c.next j)) [C.has_homology j] [has_cokernel (C.d i j)] :
  C.homology j ≅ cokernel (C.d i j) :=
(C.homology_data_of_cokernel hij hj).homology_iso

@[simp]
def homology_data_of_kernel'
  (C : homological_complex V c) {i j : ι} (hij : c.rel i j)
  (hi : ¬c.rel (c.prev i) i) (kf : kernel_fork (C.d i j)) (hkf : is_limit kf) :
  C.homology_data i :=
begin
  refine short_complex.homology_data.of_limit_kernel_fork _ (C.d_to_eq_zero hi)
    (kernel_fork.of_ι kf.ι _) _,
  { dsimp,
    simp only [C.d_from_eq hij, kf.condition_assoc, zero_comp], },
  { have h := c.next_eq' hij,
    subst h,
    exact is_limit.of_iso_limit hkf (fork.ext (iso.refl _) (by tidy)), },
end

@[simp]
def homology_data_of_kernel
  (C : homological_complex V c) {i j : ι} (hij : c.rel i j)
  (hi : ¬c.rel (c.prev i) i) [has_kernel (C.d i j)] :
  C.homology_data i :=
C.homology_data_of_kernel' hij hi _ (kernel_is_kernel (C.d i j))

def homology_map_data_of_kernel'
  {C₁ C₂ : homological_complex V c} (φ : C₁ ⟶ C₂) {i j : ι} (hij : c.rel i j)
  (hi : ¬c.rel (c.prev i) i) (kf₁ : kernel_fork (C₁.d i j)) (hkf₁ : is_limit kf₁)
  (kf₂ : kernel_fork (C₂.d i j)) (hkf₂ : is_limit kf₂) (f : kf₁.X ⟶ kf₂.X)
  (comm : kf₁.ι ≫ φ.f i = f ≫ kf₂.ι):
  homology_map_data φ i (C₁.homology_data_of_kernel' hij hi kf₁ hkf₁)
    (C₂.homology_data_of_kernel' hij hi kf₂ hkf₂) :=
short_complex.homology_map_data.of_limit_kernel_forks _ _ _ _ _ _ _ _ comm

def homology_map_data_of_kernel
  {C₁ C₂ : homological_complex V c} (φ : C₁ ⟶ C₂) {i j : ι} (hij : c.rel i j)
  (hi : ¬c.rel (c.prev i) i) [has_kernel (C₁.d i j)] [has_kernel (C₂.d i j)] :
  homology_map_data φ i (C₁.homology_data_of_kernel hij hi)
    (C₂.homology_data_of_kernel hij hi) :=
short_complex.homology_map_data.of_limit_kernel_forks _ _ _ _ _ _ _
  (kernel.map _ _ _ _ (φ.comm i j).symm) (by simp)

@[simp]
def homology_iso_kernel' (C : homological_complex V c) {i j : ι} (hij : c.rel i j)
  (hi : ¬c.rel (c.prev i) i) [C.has_homology i] (kc : kernel_fork (C.d i j)) (hkc : is_limit kc) :
  C.homology i ≅ kc.X :=
(C.homology_data_of_kernel' hij hi kc hkc).homology_iso

@[simp]
def homology_iso_kernel (C : homological_complex V c) {i j : ι} (hij : c.rel i j)
  (hi : ¬c.rel (c.prev i) i) [C.has_homology i] [has_kernel (C.d i j)] :
  C.homology i ≅ kernel (C.d i j) :=
(C.homology_data_of_kernel hij hi).homology_iso

end homological_complex

def chain_complex.homology_zero_iso' (C : chain_complex V ℕ) [C.has_homology 0]
  (c : cokernel_cofork (C.d 1 0)) (hc : is_colimit c) :
  C.homology 0 ≅ c.X :=
C.homology_iso_cokernel' rfl (by simp) c hc

def chain_complex.homology_zero_iso (C : chain_complex V ℕ) [C.has_homology 0]
  [has_cokernel (C.d 1 0)] :
  C.homology 0 ≅ cokernel (C.d 1 0) :=
C.homology_iso_cokernel rfl (by simp)

lemma chain_complex.homology_map_zero' {C D : chain_complex V ℕ} (f : C ⟶ D)
  [C.has_homology 0] [D.has_homology 0] (c : cokernel_cofork (C.d 1 0)) (hc : is_colimit c)
  (d : cokernel_cofork (D.d 1 0)) (hd : is_colimit d) (f₀ : c.X ⟶ d.X)
  (comm : f.f 0 ≫ d.π = c.π ≫ f₀) :
  homology_map f 0 = (C.homology_zero_iso' c hc).hom ≫ f₀ ≫ (D.homology_zero_iso' d hd).inv :=
(homological_complex.homology_map_data_of_cokernel' f rfl (by simp) c hc d hd f₀ comm).homology_map_eq

lemma chain_complex.homology_map_zero {C D : chain_complex V ℕ} (f : C ⟶ D)
  [C.has_homology 0] [D.has_homology 0] [has_cokernel (C.d 1 0)] [has_cokernel (D.d 1 0)] :
  homology_map f 0 =
    C.homology_zero_iso.hom ≫ cokernel.map _ _ _ _ (f.comm 1 0).symm ≫ D.homology_zero_iso.inv :=
(homological_complex.homology_map_data_of_cokernel f rfl (by simp)).homology_map_eq

def cochain_complex.homology_zero_iso' (C : cochain_complex V ℕ) [C.has_homology 0]
  (c : kernel_fork (C.d 0 1)) (hc : is_limit c) :
  C.homology 0 ≅ c.X :=
C.homology_iso_kernel' rfl (by simp) c hc

def cochain_complex.homology_zero_iso (C : cochain_complex V ℕ) [C.has_homology 0]
  [has_kernel (C.d 0 1)] :
  C.homology 0 ≅ kernel (C.d 0 1) :=
C.homology_iso_kernel rfl (by simp)

lemma cochain_complex.homology_map_zero' {C D : cochain_complex V ℕ} (f : C ⟶ D)
  [C.has_homology 0] [D.has_homology 0] (c : kernel_fork (C.d 0 1)) (hc : is_limit c)
  (d : kernel_fork (D.d 0 1)) (hd : is_limit d) (f₀ : c.X ⟶ d.X)
  (comm : c.ι ≫ f.f 0 = f₀ ≫ d.ι) :
  homology_map f 0 = (C.homology_zero_iso' c hc).hom ≫ f₀ ≫ (D.homology_zero_iso' d hd).inv :=
(homological_complex.homology_map_data_of_kernel' f rfl (by simp) c hc d hd f₀ comm).homology_map_eq

lemma cochain_complex.homology_map_zero {C D : cochain_complex V ℕ} (f : C ⟶ D)
  [C.has_homology 0] [D.has_homology 0] [has_kernel (C.d 0 1)] [has_kernel (D.d 0 1)] :
  homology_map f 0 = C.homology_zero_iso.hom ≫
    kernel.map _ _ _ _ (f.comm 0 1).symm ≫ D.homology_zero_iso.inv :=
(homological_complex.homology_map_data_of_kernel f rfl (by simp)).homology_map_eq

/-- The `n + 1`th homology of a chain complex (as kernel of 'the differential from `Cₙ₊₁`' modulo
the image of 'the differential to `Cₙ₊₁`') is isomorphic to the kernel of `d : Cₙ₊₁ → Cₙ` modulo
the image of `d : Cₙ₊₂ → Cₙ₊₁`. -/
def chain_complex.homology_succ_iso
  (C : chain_complex V ℕ) (n : ℕ) [C.has_homology (n+1)] [(C.sc (n+2) (n+1) n).has_homology] :
  C.homology (n + 1) ≅ (C.sc (n+2) (n+1) n).homology :=
short_complex.homology_map_iso
  (((homological_complex.short_complex_functor_nat_iso V (complex_shape.down ℕ) rfl rfl).app C))

def cochain_complex.homology_succ_iso
  (C : cochain_complex V ℕ) (n : ℕ) [C.has_homology (n+1)] [(C.sc n (n+1) (n+2)).has_homology]:
  C.homology (n + 1) ≅ (C.sc n (n+1) (n+2)).homology :=
short_complex.homology_map_iso
  (((homological_complex.short_complex_functor_nat_iso V (complex_shape.up ℕ) rfl rfl).app C))

open homological_complex

/-
/-! Computing the cycles is functorial. -/
section
variables [has_kernels V]
variables {C₁ C₂ C₃ : homological_complex V c} (f : C₁ ⟶ C₂)

/--
The morphism between cycles induced by a chain map.
-/
abbreviation cycles_map (f : C₁ ⟶ C₂) (i : ι) : (C₁.cycles i : V) ⟶ (C₂.cycles i : V) :=
subobject.factor_thru _ ((C₁.cycles i).arrow ≫ f.f i) (kernel_subobject_factors _ _ (by simp))

@[simp, reassoc, elementwise]
lemma cycles_map_arrow (f : C₁ ⟶ C₂) (i : ι) :
  (cycles_map f i) ≫ (C₂.cycles i).arrow = (C₁.cycles i).arrow ≫ f.f i :=
by { simp, }

@[simp] lemma cycles_map_id (i : ι) : cycles_map (𝟙 C₁) i = 𝟙 _ :=
by { dunfold cycles_map, simp, }

@[simp] lemma cycles_map_comp (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
  cycles_map (f ≫ g) i = cycles_map f i ≫ cycles_map g i :=
by { dunfold cycles_map, simp [subobject.factor_thru_right], }

variables (V c)

/-- Cycles as a functor. -/
@[simps]
def cycles_functor (i : ι) : homological_complex V c ⥤ V :=
{ obj := λ C, C.cycles i,
  map := λ C₁ C₂ f, cycles_map f i, }

end

/-! Computing the boundaries is functorial. -/
section
variables [has_images V] [has_image_maps V]
variables {C₁ C₂ C₃ : homological_complex V c} (f : C₁ ⟶ C₂)

/--
The morphism between boundaries induced by a chain map.
-/
abbreviation boundaries_map (f : C₁ ⟶ C₂) (i : ι) : (C₁.boundaries i : V) ⟶ (C₂.boundaries i : V) :=
image_subobject_map (f.sq_to i)

variables (V c)

/-- Boundaries as a functor. -/
@[simps]
def boundaries_functor (i : ι) : homological_complex V c ⥤ V :=
{ obj := λ C, C.boundaries i,
  map := λ C₁ C₂ f, image_subobject_map (f.sq_to i), }

end

section

/-! The `boundaries_to_cycles` morphisms are natural. -/
variables [has_equalizers V] [has_images V] [has_image_maps V]
variables {C₁ C₂ : homological_complex V c} (f : C₁ ⟶ C₂)

@[simp, reassoc]
lemma boundaries_to_cycles_naturality (i : ι) :
  boundaries_map f i ≫ C₂.boundaries_to_cycles i = C₁.boundaries_to_cycles i ≫ cycles_map f i :=
by { ext, simp, }

variables (V c)

/-- The natural transformation from the boundaries functor to the cycles functor. -/
@[simps] def boundaries_to_cycles_nat_trans (i : ι) :
  boundaries_functor V c i ⟶ cycles_functor V c i :=
{ app := λ C, C.boundaries_to_cycles i,
  naturality' := λ C₁ C₂ f, boundaries_to_cycles_naturality f i, }

/-- The `i`-th homology, as a functor to `V`. -/
@[simps]
def homology_functor [has_cokernels V] (i : ι) :
  homological_complex V c ⥤ V :=
-- It would be nice if we could just write
-- `cokernel (boundaries_to_cycles_nat_trans V c i)`
-- here, but universe implementation details get in the way...
{ obj := λ C, C.homology i,
  map := λ C₁ C₂ f, _root_.homology.map _ _ (f.sq_to i) (f.sq_from i) rfl,
  map_id' :=
  begin
    intros, ext1,
    simp only [homology.π_map, kernel_subobject_map_id, hom.sq_from_id,
      category.id_comp, category.comp_id]
  end,
  map_comp' :=
  begin
    intros, ext1,
    simp only [hom.sq_from_comp, kernel_subobject_map_comp, homology.π_map_assoc,
      homology.π_map, category.assoc]
  end }-/

/-- The homology functor from `ι`-indexed complexes to `ι`-graded objects in `V`. -/
@[simps] def graded_homology_functor [category_with_homology V] :
  homological_complex V c ⥤ graded_object ι V :=
{ obj := λ C i, C.homology i,
  map := λ C C' f i, (homology_functor V c i).map f, }

namespace cochain_complex

instance preserves_left_homology_zero_of_preserves_finite_limits (F : V ⥤ W)
  [F.preserves_zero_morphisms] [preserves_finite_limits F] (C : cochain_complex V ℕ) :
  F.preserves_left_homology_of (C.sc' 0) :=
short_complex.preserves_left_homology_of_zero_left F _ (by simp)

instance preserves_left_homology_zero_of_preserves_finite_limits' (F : V ⥤ W)
  [F.preserves_zero_morphisms] [preserves_finite_limits F] (C : cochain_complex V ℕ) :
  F.preserves_left_homology_of ((homological_complex.short_complex_functor _ _ 0).obj C) :=
by { change F.preserves_left_homology_of (C.sc' 0), apply_instance, }

instance preserves_right_homology_zero_of_preserves_finite_limits (F : V ⥤ W)
  [F.preserves_zero_morphisms] [preserves_finite_limits F] (C : cochain_complex V ℕ) :
  F.preserves_right_homology_of (C.sc' 0) :=
short_complex.preserves_right_homology_of_zero_left F _ (by simp)

instance preserves_right_homology_zero_of_preserves_finite_limits' (F : V ⥤ W)
  [F.preserves_zero_morphisms] [preserves_finite_limits F] (C : cochain_complex V ℕ) :
  F.preserves_right_homology_of ((homological_complex.short_complex_functor _ _ 0).obj C) :=
by { change F.preserves_right_homology_of (C.sc' 0), apply_instance, }

end cochain_complex

namespace chain_complex

instance preserves_left_homology_zero_of_preserves_finite_colimits (F : V ⥤ W)
  [F.preserves_zero_morphisms] [preserves_finite_colimits F] (C : chain_complex V ℕ) :
  F.preserves_left_homology_of (C.sc' 0) :=
short_complex.preserves_left_homology_of_zero_right F _ (by simp)

instance preserves_left_homology_zero_of_preserves_finite_colimits' (F : V ⥤ W)
  [F.preserves_zero_morphisms] [preserves_finite_colimits F] (C : chain_complex V ℕ) :
  F.preserves_left_homology_of ((homological_complex.short_complex_functor _ _ 0).obj C) :=
by { change F.preserves_left_homology_of (C.sc' 0), apply_instance, }

instance preserves_right_homology_zero_of_preserves_finite_colimits (F : V ⥤ W)
  [F.preserves_zero_morphisms] [preserves_finite_colimits F] (C : chain_complex V ℕ) :
  F.preserves_right_homology_of (C.sc' 0) :=
short_complex.preserves_right_homology_of_zero_right F _ (by simp)

instance preserves_right_homology_zero_of_preserves_finite_colimits' (F : V ⥤ W)
  [F.preserves_zero_morphisms] [preserves_finite_colimits F] (C : chain_complex V ℕ) :
  F.preserves_right_homology_of ((homological_complex.short_complex_functor _ _ 0).obj C) :=
by { change F.preserves_right_homology_of (C.sc' 0), apply_instance, }

end chain_complex
