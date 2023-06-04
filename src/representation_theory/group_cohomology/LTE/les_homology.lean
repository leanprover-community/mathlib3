import data.matrix.notation

import .snake_lemma2
import .short_exact_sequence

noncomputable theory

open category_theory
open category_theory.limits

universes v u

lemma preadditive.exact_of_iso_of_exact' {D : Type*} [category D] [abelian D]
  {A₁ B₁ C₁ A₂ B₂ C₂ : D}
  (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁) (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂)
  (α : A₁ ≅ A₂) (β : B₁ ≅ B₂) (γ : C₁ ≅ C₂) (hsq₁ : α.hom ≫ f₂ = f₁ ≫ β.hom)
  (hsq₂ : β.hom ≫ g₂ = g₁ ≫ γ.hom)
  (h : exact f₁ g₁) :
  exact f₂ g₂ :=
preadditive.exact_of_iso_of_exact f₁ g₁ f₂ g₂ (arrow.iso_mk α β hsq₁) (arrow.iso_mk β γ hsq₂) rfl h

namespace homological_complex

variables {C : Type u} [category.{v} C] [abelian C]
variables {ι : Type*} {c : complex_shape ι}

def mod_boundaries (A : homological_complex C c) (j : ι) : C :=
cokernel ((A.boundaries j).arrow)

def mod_boundaries_map {A B : homological_complex C c} (f : A ⟶ B) (j : ι) :
  A.mod_boundaries j ⟶ B.mod_boundaries j :=
cokernel.map _ _ (boundaries_map f j) (f.f j) $ by { rw image_subobject_map_arrow, refl }

@[simps]
def mod_boundaries_functor (j : ι) : homological_complex C c ⥤ C :=
{ obj := λ A, A.mod_boundaries j,
  map := λ A B f, mod_boundaries_map f j,
  map_id' := λ A,
  begin
    delta mod_boundaries mod_boundaries_map cokernel.map, ext,
    show cokernel.π (A.boundaries j).arrow ≫ _ = cokernel.π (A.boundaries j).arrow ≫ _,
    simp only [cokernel.π_desc, category.id_comp, id_f, category.comp_id],
  end,
  map_comp' := λ X Y Z f g,
  begin
    delta mod_boundaries mod_boundaries_map cokernel.map, ext,
    show cokernel.π (X.boundaries j).arrow ≫ _ = cokernel.π (X.boundaries j).arrow ≫ _,
    simp only [cokernel.π_desc, cokernel.π_desc_assoc, comp_f, category.assoc],
  end }
.

-- generalize to chain complexes over other shapes
@[simps]
def homology_to_mod_boundaries (i : ι) :
  homology_functor C c i ⟶ mod_boundaries_functor i :=
{ app := λ A, cokernel.map _ _ (𝟙 _) ((A.cycles i).arrow)
    (by { simp only [category.id_comp, image_to_kernel_arrow], }),
  naturality' := λ A B f,
  begin
    ext,
    simp only [homology_functor_map, mod_boundaries_functor_map, homology.π_map_assoc],
    delta mod_boundaries_map homology.π cokernel.map cycles,
    sorry /-simp only [cokernel.π_desc, cokernel.π_desc_assoc, comp_f, category.assoc,
      kernel_subobject_map_arrow_assoc, hom.sq_from_left],-/
  end }
.

variables (A : homological_complex C c) (i j : ι) (hij : c.rel i j)

def delta_to_boundaries : A.X i ⟶ (A.boundaries j) :=
(X_prev_iso A hij).inv ≫ factor_thru_image_subobject _

instance delta_to_boundaries_epi : epi (delta_to_boundaries A i j hij) :=
epi_comp _ _

@[ext] lemma boundaries.ext' {X : C} (f g : (boundaries A j : C) ⟶ X)
  (h : factor_thru_image_subobject _ ≫ f = factor_thru_image_subobject _ ≫ g) : f = g :=
by rwa cancel_epi (factor_thru_image_subobject (A.d_to j)) at h

@[simp, reassoc] lemma delta_to_boundaries_comp_arrow :
  (delta_to_boundaries A i j hij) ≫ (boundaries A j).arrow = A.d i j :=
by rw [delta_to_boundaries, category.assoc, image_subobject_arrow_comp, X_prev_iso_comp_d_to]

@[simp, reassoc] lemma boundaries_arrow_comp_delta_to_boundaries :
  (boundaries _ i).arrow ≫ delta_to_boundaries A i j hij = 0 :=
begin
  ext,
  simp only [image_subobject_arrow_comp_assoc, category.assoc,
    delta_to_boundaries_comp_arrow, comp_zero, zero_comp,
    ← d_from_comp_X_next_iso A hij, reassoc_of (d_to_comp_d_from A)],
end

def delta_to_cycles : A.X i ⟶ (A.cycles j) :=
delta_to_boundaries _ i j hij ≫ boundaries_to_cycles _ _

@[simp, reassoc] lemma delta_to_cycles_comp_arrow :
  (delta_to_cycles A i j hij) ≫ (cycles A j).arrow = A.d i j :=
by rw [delta_to_cycles, category.assoc, image_to_kernel_arrow, delta_to_boundaries_comp_arrow]

@[simp, reassoc] lemma boundaries_arrow_comp_delta_to_cycles :
  (boundaries _ _).arrow ≫ delta_to_cycles A i j hij = 0 :=
by rw [delta_to_cycles, ← category.assoc, boundaries_arrow_comp_delta_to_boundaries, zero_comp]

@[simps]
def mod_boundaries_to_cycles : mod_boundaries_functor i ⟶ cycles_functor C c j :=
{ app := λ A, cokernel.desc _ (delta_to_cycles _ i j hij)
   (boundaries_arrow_comp_delta_to_cycles _ i j hij),
  naturality' := λ A B f,
  begin
    ext, show cokernel.π _ ≫ _ = cokernel.π _ ≫ _,
    simp only [homology_functor_map, mod_boundaries_functor_map, homology.π_map_assoc],
    delta mod_boundaries_map homology.π cokernel.map,
    simp only [category.assoc, cycles_functor_map, cycles_map_arrow, hom.comm,
      cokernel.π_desc_assoc, delta_to_cycles_comp_arrow_assoc, delta_to_cycles_comp_arrow]
  end }
.

@[simps]
def cycles_to_homology : cycles_functor C c i ⟶ homology_functor C c i :=
{ app := λ A, cokernel.π _,
  naturality' := λ A B f,
  begin
    simp only [cycles_functor_map, homology_functor_map],
    delta homology.map,
    rw cokernel.π_desc, refl,
  end }

open_locale zero_object

lemma _root_.option.eq_none_or_eq_some {α : Type*} : ∀ (o : option α), o = none ∨ ∃ a, o = some a
| option.none     := or.inl rfl
| (option.some a) := or.inr ⟨a, rfl⟩

lemma exact_next {A₁ A₂ A₃ : homological_complex C c} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃)
  (i j : ι) (hij : c.rel i j) (h : exact (f.f j) (g.f j)) :
  exact (f.next i) (g.next i) :=
begin
  refine preadditive.exact_of_iso_of_exact' (f.f j) (g.f j) _ _
    (X_next_iso A₁ hij).symm (X_next_iso A₂ hij).symm (X_next_iso A₃ hij).symm _ _ h;
  simp only [hom.next_eq _ hij, iso.symm_hom, iso.inv_hom_id_assoc],
end

lemma exact_next' {A₁ A₂ A₃ : homological_complex C c} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (i : ι)
  (h : ∀ n, exact (f.f n) (g.f n)) : exact (f.next i) (g.next i) :=
h _

lemma exact_prev {A₁ A₂ A₃ : homological_complex C c} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃)
  (i j : ι) (hij : c.rel i j) (h : exact (f.f i) (g.f i)) :
  exact (f.prev j) (g.prev j) :=
begin
  refine preadditive.exact_of_iso_of_exact' (f.f i) (g.f i) _ _
    (X_prev_iso A₁ hij).symm (X_prev_iso A₂ hij).symm (X_prev_iso A₃ hij).symm _ _ h;
  simp only [hom.prev_eq _ hij, iso.symm_hom, iso.inv_hom_id_assoc],
end

lemma exact_prev' {A₁ A₂ A₃ : homological_complex C c} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (j : ι)
  (h : ∀ n, exact (f.f n) (g.f n)) : exact (f.prev j) (g.prev j) :=
h _

lemma mono_next {A₁ A₂ : homological_complex C c} (f : A₁ ⟶ A₂)
  (i j : ι) (hij : c.rel i j) [mono (f.f j)] :
  mono (f.next i) :=
begin
  rw hom.next_eq _ hij,
  apply_with mono_comp { instances := ff },
  { apply_instance },
  { apply mono_comp }
end

instance mono_next' {A₁ A₂ : homological_complex C c} (f : A₁ ⟶ A₂)
  (i : ι) [∀ n, mono (f.f n)] :
  mono (f.next i) :=
by apply_assumption

lemma epi_prev {A₁ A₂ : homological_complex C c} (f : A₁ ⟶ A₂)
  (i j : ι) (hij : c.rel i j) [epi (f.f i)] :
  epi (f.prev j) :=
begin
  rw hom.prev_eq _ hij,
  apply_with epi_comp { instances := ff },
  { apply_instance },
  { apply epi_comp }
end

instance epi_prev' {A₁ A₂ : homological_complex C c} (f : A₁ ⟶ A₂)
  (j : ι) [∀ n, epi (f.f n)] :
  epi (f.prev j) :=
by apply_assumption

instance {A B : homological_complex C c} (f : A ⟶ B) [∀ n, epi (f.f n)] (i : ι) :
  epi (boundaries_map f i) :=
begin
  let sq := hom.sq_to f i,
  haveI : epi sq.left := by { dsimp, apply_instance, },
  apply_with (epi_of_epi (factor_thru_image_subobject _)) { instances := ff },
  suffices : factor_thru_image_subobject (A.d_to i) ≫
      boundaries_map f i =
    sq.left ≫ factor_thru_image_subobject (B.d_to i),
  { rw this, apply epi_comp, },
  ext,
  simp only [category.assoc, image_subobject_map_arrow, hom.sq_to_right,
    image_subobject_arrow_comp_assoc, hom.sq_to_left, image_subobject_arrow_comp, hom.comm_to],
end

lemma exact_kernel_subobject_arrow (A B : C) (f : A ⟶ B) : exact (kernel_subobject f).arrow f :=
by { rw [← kernel_subobject_arrow, exact_iso_comp], exact exact_kernel_ι }

lemma exact_cycles_arrow (A : homological_complex C c) (i : ι) :
  exact (cycles A i).arrow (d_from A i) :=
exact_kernel_subobject_arrow _ _ _

lemma exact_cycles_map {A₁ A₂ A₃ : homological_complex C c} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃)
  (hfg : ∀ n, short_exact (f.f n) (g.f n)) (j : ι) :
  exact (cycles_map f j) (cycles_map g j) :=
begin
  have sq₁ :  d_from A₁ j ≫ f.next j = f.f j ≫ d_from A₂ j := (hom.comm_from _ _).symm,
  have sq₂ :  d_from A₂ j ≫ g.next j = g.f j ≫ d_from A₃ j := (hom.comm_from _ _).symm,
  suffices S : snake
    ↑(cycles A₁ j) ↑(cycles A₂ j) ↑(cycles A₃ j)
    (A₁.X j) (A₂.X j) (A₃.X j)
    _ _ _
    _ _ _
    (cycles_map f j) (cycles_map g j)
    (cycles _ j).arrow (cycles _ j).arrow (cycles _ j).arrow
    (f.f j) (g.f j)
    (A₁.d_from j) (A₂.d_from j) (A₃.d_from j)
    (f.next j) (g.next j)
    (cokernel.π $ A₁.d_from j) (cokernel.π $ A₂.d_from j) (cokernel.π $ A₃.d_from j)
    (cokernel.map _ _ _ _ sq₁) (cokernel.map _ _ _ _ sq₂),
  { exact S.six_term_exact_seq.pair },
  have hfg_epi := λ j, (hfg j).epi,
  have hfg_mono := λ j, (hfg j).mono,
  resetI,
  fsplit,
  { exact (hfg j).exact },
  { exact exact_next' _ _ _ (λ i, (hfg i).exact), },
  { refine (exact_cycles_arrow _ _).cons (abelian.exact_cokernel _).exact_seq, },
  { refine (exact_cycles_arrow _ _).cons (abelian.exact_cokernel _).exact_seq, },
  { refine (exact_cycles_arrow _ _).cons (abelian.exact_cokernel _).exact_seq, },
  { rw cycles_map_arrow, },
  { rw cycles_map_arrow, },
  { exact sq₁ },
  { exact sq₂ },
  { apply cokernel.π_desc, },
  { apply cokernel.π_desc, },
end

variables {A₁ A₂ A₃ : homological_complex C c} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃)
variables (hfg : ∀ n, short_exact (f.f n) (g.f n))

lemma mono_cycles_map (hfg : ∀ n, short_exact (f.f n) (g.f n)) (i : ι) :
  mono (cycles_map f i) :=
begin
  apply_with (mono_of_mono _ (subobject.arrow _)) { instances := ff },
  rw cycles_map_arrow,
  haveI : mono (f.f i) := (hfg i).mono,
  apply mono_comp,
end

@[simp] lemma image_subobject_arrow {X : C} (S : subobject X) :
  image_subobject (S.arrow) = S :=
begin
  delta image_subobject,
  ext,
  swap,
  { exact limits.image_mono_iso_source _ },
  { simp }
end

@[simp] lemma kernel_subobject_cokernel.π {X : C} (S : subobject X) :
  kernel_subobject (cokernel.π S.arrow) = S :=
begin
  delta kernel_subobject,
  ext,
  swap,
  { exact (abelian.image_iso_image _).trans (limits.image_mono_iso_source _) },
  { simp }
end

lemma exact.congr {X₁ X₂ Y Z₁ Z₂ : C} (f₁ : X₁ ⟶ Y) (g₁ : Y ⟶ Z₁) (f₂ : X₂ ⟶ Y) (g₂ : Y ⟶ Z₂)
  (h : exact f₁ g₁) (him : image_subobject f₁ = image_subobject f₂)
  (hker : kernel_subobject g₁ = kernel_subobject g₂) :
  exact f₂ g₂ :=
by rwa [abelian.exact_iff_image_eq_kernel, ← him, ← hker, ← abelian.exact_iff_image_eq_kernel]

lemma exact_column :
exact_seq C [(kernel.ι (A.d_to j)), (A.d_to j), (cokernel.π (A.boundaries j).arrow)] :=
exact_kernel_ι.cons $
(exact.congr (boundaries A j).arrow _ _ _ (abelian.exact_cokernel _) (image_subobject_arrow _) rfl).exact_seq

lemma exact_mod_boundaries_map (hfg : ∀ n, short_exact (f.f n) (g.f n)) (j : ι) :
  exact (mod_boundaries_map f j) (mod_boundaries_map g j) :=
begin
  have sq1 : A₁.d_to j ≫ f.f j = f.prev j ≫ A₂.d_to j := (f.comm_to _).symm,
  have sq2 : A₂.d_to j ≫ g.f j = g.prev j ≫ A₃.d_to j := (g.comm_to _).symm,
  suffices S : snake
    -- the objects
         (kernel _)           (kernel _)           (kernel _)
        (A₁.X_prev j)         (A₂.X_prev j)         (A₃.X_prev j)
          (A₁.X j)             (A₂.X j)             (A₃.X j)
    (mod_boundaries _ j) (mod_boundaries _ j) (mod_boundaries _ j)
    -- the morphisms
    (kernel.map _ _ _ _ sq1) (kernel.map _ _ _ _ sq2)
    (kernel.ι $ A₁.d_to j) (kernel.ι $ A₂.d_to j) (kernel.ι $ A₃.d_to j)
    (f.prev j) (g.prev j)
    (A₁.d_to j) (A₂.d_to j) (A₃.d_to j)
    (f.f j) (g.f j)
    (cokernel.π _) (cokernel.π _) (cokernel.π _)
    (mod_boundaries_map f j) (mod_boundaries_map g j),
  { exact (S.six_term_exact_seq.drop 3).pair },
  have hfg_epi := λ n, (hfg n).epi,
  have hfg_mono := λ n, (hfg n).mono,
  resetI,
  fsplit,
  { exact exact_prev' _ _ _ (λ n, (hfg n).exact) },
  { exact (hfg j).exact },
  { apply exact_column },
  { apply exact_column },
  { apply exact_column },
  { simp },
  { simp },
  { exact sq1 },
  { exact sq2 },
  { simp [mod_boundaries_map] },
  { simp [mod_boundaries_map] }
end

lemma epi_mod_boundaries_map (hfg : ∀ n, short_exact (f.f n) (g.f n)) (i : ι) :
  epi (mod_boundaries_map g i) :=
begin
  apply_with (epi_of_epi (cokernel.π _)) { instances := ff },
  haveI : epi (g.f i) := (hfg i).epi,
  have : cokernel.π _ ≫ mod_boundaries_map g i = g.f i ≫ cokernel.π _ := cokernel.π_desc _ _ _,
  rw this,
  apply epi_comp,
end

lemma mono_homology_to_mod_boundaries :
  mono ((homology_to_mod_boundaries i).app A) :=
cokernel.map_mono_of_epi_of_mono
  (boundaries A i) (cycles A i)
  (boundaries A i) (A.X i)
  _ _ _ _ _

variables {C}

@[simp] lemma image_subobject_comp_eq_of_epi {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [epi f] :
  image_subobject (f ≫ g) = image_subobject g :=
begin
  delta image_subobject,
  haveI : is_iso (image.pre_comp f g) := is_iso_of_mono_of_epi _,
  ext, swap,
  { exact as_iso (image.pre_comp f g) },
  { simp only [as_iso_hom, image.pre_comp_ι], },
end

@[simp] lemma kernel_subobject_comp_eq_of_mono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [mono g] :
  kernel_subobject (f ≫ g) = kernel_subobject f :=
begin
  delta kernel_subobject,
  ext, swap,
  { exact kernel_comp_mono f g },
  { simp only [kernel_comp_mono_hom, kernel.lift_ι] },
end

lemma exact_cycles_arrow_delta_to_cycles :
  exact (A.cycles i).arrow (delta_to_cycles A i j hij) :=
begin
  rw [category_theory.abelian.exact_iff_image_eq_kernel],
  dsimp [delta_to_cycles, delta_to_boundaries],
  simp only [image_subobject_arrow, kernel_subobject_comp_eq_of_mono],
  delta cycles,
  let g : ↑(A.boundaries j) ⟶ X_next A i := (A.boundaries j).arrow ≫ (X_next_iso _ hij).inv,
  haveI : mono g := mono_comp _ _,
  suffices aux : delta_to_boundaries _ i j hij ≫ g = d_from A i,
  { simp_rw [← aux, kernel_subobject_comp_eq_of_mono], refl, },
  simp only [delta_to_boundaries_comp_arrow_assoc, iso.comp_inv_eq, d_from_comp_X_next_iso],
end

lemma exact_homology_to_mod_boundaries_to_cycles :
  exact ((homology_to_mod_boundaries i).app A) ((mod_boundaries_to_cycles i j hij).app A) :=
begin
  let φ : homology A i ⟶ mod_boundaries A i :=
    limits.cokernel.desc _ ((kernel_subobject _).arrow ≫ (cokernel.π _)) (by simp),
  suffices S : snake
    (0:C) 0 0
    (A.boundaries i) (boundaries A i) 0
    (A.cycles i) (A.X i) (A.cycles j)
    (homology A i) (mod_boundaries A i) (A.cycles j)
    0 0
    0 0 0
    (𝟙 _) 0
    (boundaries_to_cycles _ _) (A.boundaries i).arrow 0
    (A.cycles i).arrow (delta_to_cycles _ i j hij)
    (homology.π _ _ _) (cokernel.π _) (𝟙 _)
    φ ((mod_boundaries_to_cycles i j hij).app A),
  { exact (S.six_term_exact_seq.drop 3).pair },
  letI : exact (cycles A i).arrow (delta_to_cycles A i j hij) :=
    exact_cycles_arrow_delta_to_cycles _ i j hij,
  letI : epi (homology.π (d_to A i) (d_from A i) (A.d_to_comp_d_from i)) := coequalizer.π_epi,
  fsplit,
  { rw ← epi_iff_exact_zero_right, apply_instance },
  { apply exact_cycles_arrow_delta_to_cycles },
  { exact (category_theory.exact_zero_mono _).cons (abelian.exact_cokernel _).exact_seq, },
  { exact (category_theory.exact_zero_mono _).cons (abelian.exact_cokernel _).exact_seq, },
  { exact (category_theory.exact_zero_mono _).cons (exact_zero_left_of_mono _).exact_seq, },
  { simp only [zero_comp] },
  { simp only [zero_comp] },
  { simp only [image_to_kernel_arrow, category.id_comp] },
  { simp only [boundaries_arrow_comp_delta_to_cycles, zero_comp], },
  { dsimp [homology.π], simp only [cokernel.π_desc] },
  { simp only [mod_boundaries_to_cycles_app, cokernel.π_desc, category.comp_id] },
end

lemma exact_mod_boundaries_to_cycles_to_homology :
  exact ((mod_boundaries_to_cycles i j hij).app A) ((cycles_to_homology j).app A)  :=
begin
  refine exact.congr (boundaries_to_cycles _ _) _ _ _ _ _ rfl,
  { exact abelian.exact_cokernel _, },
  { simp only [mod_boundaries_to_cycles_app],
    delta delta_to_cycles,
    rw [← image_subobject_comp_eq_of_epi (cokernel.π _)],
    simp only [cokernel.π_desc, image_subobject_comp_eq_of_epi], }
end

lemma epi_cycles_to_homology : epi ((cycles_to_homology j).app A) :=
coequalizer.π_epi

lemma exact_seq_column :
  exact_seq C
    [((homology_to_mod_boundaries i).app A₁),
     ((mod_boundaries_to_cycles i j hij).app A₁),
     ((cycles_to_homology j).app A₁)] :=
(exact_homology_to_mod_boundaries_to_cycles _ _ _ _).cons
  (exact_mod_boundaries_to_cycles_to_homology _ _ _ _).exact_seq

lemma snake (hfg : ∀ n, short_exact (f.f n) (g.f n)) (i j : ι) (hij : c.rel i j) :
  snake
  -- the objects
     (A₁.homology i)       (A₂.homology i)       (A₃.homology i)
  (A₁.mod_boundaries i) (A₂.mod_boundaries i) (A₃.mod_boundaries i)
      (A₁.cycles j)         (A₂.cycles j)         (A₃.cycles j)
     (A₁.homology j)       (A₂.homology j)       (A₃.homology j)
  -- the morphisms
  ((homology_functor _ _ i).map f) ((homology_functor _ _ i).map g)
  ((homology_to_mod_boundaries i).app A₁)
  ((homology_to_mod_boundaries i).app A₂)
  ((homology_to_mod_boundaries i).app A₃)
  ((mod_boundaries_functor i).map f) ((mod_boundaries_functor i).map g)
  ((mod_boundaries_to_cycles i j hij).app A₁)
  ((mod_boundaries_to_cycles i j hij).app A₂)
  ((mod_boundaries_to_cycles i j hij).app A₃)
  ((cycles_functor _ _ j).map f) ((cycles_functor _ _ j).map g)
  ((cycles_to_homology j).app A₁)
  ((cycles_to_homology j).app A₂)
  ((cycles_to_homology j).app A₃)
  ((homology_functor _ _ j).map f) ((homology_functor _ _ j).map g) :=
{ row_exact₁ := exact_mod_boundaries_map f g hfg _,
  row_exact₂ := exact_cycles_map f g hfg _,
  row_epi := epi_mod_boundaries_map f g hfg _,
  row_mono := mono_cycles_map f g hfg _,
  col_exact_a := exact_seq_column _ _ _,
  col_exact_b := exact_seq_column _ _ _,
  col_exact_c := exact_seq_column _ _ _,
  col_mono_a := mono_homology_to_mod_boundaries _ _,
  col_mono_b := mono_homology_to_mod_boundaries _ _,
  col_mono_c := mono_homology_to_mod_boundaries _ _,
  col_epi_a := epi_cycles_to_homology _ _,
  col_epi_b := epi_cycles_to_homology _ _,
  col_epi_c := epi_cycles_to_homology _ _,
  sq_a₀ := ((homology_to_mod_boundaries _).naturality _).symm,
  sq_b₀ := ((homology_to_mod_boundaries _).naturality _).symm,
  sq_a₁ := ((mod_boundaries_to_cycles _ _ _).naturality _).symm,
  sq_b₁ := ((mod_boundaries_to_cycles _ _ _).naturality _).symm,
  sq_a₂ := ((cycles_to_homology _).naturality _).symm,
  sq_b₂ := ((cycles_to_homology _).naturality _).symm }

def δ (hfg : ∀ n, short_exact (f.f n) (g.f n)) (i j : ι) (hij : c.rel i j) :
  homology A₃ i ⟶ homology A₁ j :=
(snake f g hfg i j hij).δ

lemma six_term_exact_seq (hfg : ∀ n, short_exact (f.f n) (g.f n)) (i j : ι) (hij : c.rel i j) :
  exact_seq C [
    (homology_functor _ _ i).map f, -- Hⁱ(A₁) ⟶ Hⁱ(A₂)
    (homology_functor _ _ i).map g, -- Hⁱ(A₂) ⟶ Hⁱ(A₃)
    δ f g hfg i j hij,              -- Hⁱ(A₃) ⟶ Hʲ(A₁)
    (homology_functor _ _ j).map f, -- Hʲ(A₁) ⟶ Hʲ(A₂)
    (homology_functor _ _ j).map g  -- Hʲ(A₁) ⟶ Hʲ(A₃)
  ] :=
(snake f g hfg i j hij).six_term_exact_seq

end homological_complex
