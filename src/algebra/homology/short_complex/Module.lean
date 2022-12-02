import algebra.category.Module.abelian
import algebra.category.Module.subobject
import algebra.homology.short_complex.homology
import algebra.homology.short_complex.preadditive
import algebra.homology.short_complex.abelian
import linear_algebra.quotient

noncomputable theory

open category_theory category_theory.category Module category_theory.limits

universes v u
variables {R : Type v} [ring R]

instance : category_with_homology (Module.{u} R) := infer_instance

lemma Module.is_zero_iff (M : Module R) : is_zero M ↔ ∀ (x : M), x = 0 :=
begin
  rw is_zero.iff_id_eq_zero,
  split,
  { intros h x,
    change (𝟙 M : M → M) x = 0,
    simp only [h, linear_map.zero_apply], },
  { intro h,
    ext x,
    exact h x, },
end

namespace category_theory

namespace short_complex

variables (S : short_complex (Module R))

lemma Module_image_le_kernel : linear_map.range S.f ≤ linear_map.ker S.g :=
begin
  rintros x₂ ⟨x₁, h⟩,
  simp only [linear_map.mem_ker, ← h, ← comp_apply, S.zero, linear_map.zero_apply],
end

def Module_f' : S.X₁ ⟶ of R (linear_map.ker S.g) :=
linear_map.cod_restrict (linear_map.ker S.g) S.f
  (λ x, S.Module_image_le_kernel (by simp))

def Module_homology := of R ((linear_map.ker S.g) ⧸ linear_map.range S.Module_f')

def Module_homology_π' : of R (linear_map.ker S.g) ⟶ S.Module_homology :=
(linear_map.range S.Module_f').mkq

@[simp, reassoc, elementwise]
lemma Module_f'_comp_homology_π' : S.Module_f' ≫ S.Module_homology_π' = 0 :=
begin
  ext,
  dsimp [Module_f', Module_homology_π'],
  simp only [submodule.quotient.mk_eq_zero, linear_map.mem_range, exists_apply_eq_apply],
end

namespace Module_left_homology_data

def i : Module.of R (linear_map.ker S.g) ⟶ S.X₂ := Module.as_hom S.g.ker.subtype

lemma wi : i S ≫ S.g = 0 := by { ext x₂, exact x₂.2, }

def hi : is_limit (kernel_fork.of_ι (i S) (wi S)) := kernel_is_limit S.g

lemma f'_eq_Module_f' : (hi S).lift (kernel_fork.of_ι S.f S.zero) = S.Module_f' := rfl

lemma wπ : (hi S).lift (kernel_fork.of_ι S.f S.zero) ≫ S.Module_homology_π' = 0 :=
by simp only [f'_eq_Module_f', Module_f'_comp_homology_π']

def hπ : is_colimit (cokernel_cofork.of_π _ (wπ S)) :=
is_colimit.of_iso_colimit (Module.cokernel_is_colimit S.Module_f')
  (cofork.ext (iso.refl _) (by tidy))

end Module_left_homology_data

@[simps]
def Module_left_homology_data : S.left_homology_data :=
{ K := Module.of R (linear_map.ker S.g),
  H := Module.of R S.Module_homology,
  i := Module_left_homology_data.i S,
  π := S.Module_homology_π',
  wi := Module_left_homology_data.wi S,
  hi := Module_left_homology_data.hi S,
  wπ := Module_left_homology_data.wπ S,
  hπ := Module_left_homology_data.hπ S, }

@[simp]
lemma Module_left_homology_data_f' :
  S.Module_left_homology_data.f' = S.Module_f' := rfl

def Module_homology_iso : S.homology ≅ S.Module_homology :=
S.Module_left_homology_data.homology_iso

lemma Module_bijective_homology_iso_inv :
  function.bijective S.Module_homology_iso.inv :=
concrete_category.bijective_of_is_iso ((forget (Module R)).map S.Module_homology_iso.inv)

lemma Module_bijective_homology_iso_hom :
  function.bijective S.Module_homology_iso.hom :=
concrete_category.bijective_of_is_iso ((forget (Module R)).map S.Module_homology_iso.hom)

def Module_homology_π : of R (linear_map.ker S.g) ⟶ S.homology :=
S.Module_homology_π' ≫ S.Module_homology_iso.inv

@[simp, reassoc, elementwise]
lemma Module_homology_π'_comp_homology_iso_inv :
  S.Module_homology_π' ≫ S.Module_homology_iso.inv = S.Module_homology_π := rfl

@[simp, reassoc, elementwise]
lemma Module_f'_comp_homology_π : S.Module_f' ≫ S.Module_homology_π = 0 :=
begin
  ext,
  dsimp only [Module_homology_π],
  rw [Module_f'_comp_homology_π'_assoc, zero_comp],
end

lemma Module_surjective_homology_π' : function.surjective S.Module_homology_π' :=
(linear_map.range (Module_f' S)).mkq_surjective

lemma Module_surjective_homology_π : function.surjective S.Module_homology_π  :=
function.surjective.comp S.Module_bijective_homology_iso_inv.2
  S.Module_surjective_homology_π'

lemma Module_ker_homology_π'_eq_range_f' :
  linear_map.ker S.Module_homology_π' = linear_map.range S.Module_f' :=
(linear_map.range S.Module_f').ker_mkq

lemma Module_homology_π'_eq_zero_iff (z : linear_map.ker S.g) :
  S.Module_homology_π' z = 0 ↔ z.1 ∈ (linear_map.range S.f) :=
begin
  change z ∈ linear_map.ker S.Module_homology_π' ↔ _,
  rw Module_ker_homology_π'_eq_range_f',
  split,
  { rintro ⟨x₁, hx₁⟩,
    rw ← hx₁,
    exact ⟨x₁, rfl⟩, },
  { rintro ⟨x₁, hx₁⟩,
    exact ⟨x₁, by { ext, exact hx₁, }⟩, },
end

lemma Module_ker_homology_π_eq_ker_homology_π' :
  linear_map.ker S.Module_homology_π = linear_map.ker S.Module_homology_π' :=
begin
  dsimp only [Module_homology_π],
  ext x₂,
  split,
  { intro hx₂,
    apply S.Module_bijective_homology_iso_inv.1,
    simpa only [map_zero S.Module_homology_iso.inv] using hx₂, },
  { intro hx₂,
    simp only [linear_map.mem_ker] at hx₂ ⊢,
    rw [comp_apply, hx₂, map_zero S.Module_homology_iso.inv], },
end

lemma Module_homology_π_eq_zero_iff (z : linear_map.ker S.g) :
  S.Module_homology_π z = 0 ↔ z.1 ∈ (linear_map.range S.f) :=
begin
  change z ∈ linear_map.ker S.Module_homology_π ↔ _,
  rw S.Module_ker_homology_π_eq_ker_homology_π',
  exact S.Module_homology_π'_eq_zero_iff z,
end

lemma Module_homology_ext_iff (z z' : linear_map.ker S.g) :
  S.Module_homology_π z = S.Module_homology_π z' ↔ ∃ (x₁ : S.X₁), z.1 = z'.1 + S.f x₁ :=
begin
  split,
  { intro h,
    have eq : S.Module_homology_π (z - z') = 0,
    { simp only [map_sub, h, sub_self], },
    rw S.Module_homology_π_eq_zero_iff at eq,
    obtain ⟨x₁, hx₁⟩ := eq,
    use x₁,
    simp only [hx₁, subtype.val_eq_coe, add_subgroup_class.coe_sub, add_sub_cancel'_right], },
  { rintro ⟨x₁, hx₁⟩,
    rw [show z = z' + S.Module_f' x₁, by { ext, exact hx₁, }],
    simp only [map_add, Module_f'_comp_homology_π_apply, linear_map.zero_apply, add_zero], },
end

--@[ext]
lemma Module_homology_ext (z z' : linear_map.ker S.g)
  (h : ∃ (x₁ : S.X₁), z.1 = z'.1 + S.f x₁) :
    S.Module_homology_π z = S.Module_homology_π z' :=
by simp only [S.Module_homology_ext_iff, h]

variable (S)

lemma Module_element_homology_is_zero_iff' (z : S.Module_homology) :
  z = 0 ↔ ∃ (x₁ : S.X₁), z = S.Module_homology_π' (S.Module_f' x₁) :=
begin
  split,
  { rintro rfl,
    exact ⟨0, by simp only [map_zero]⟩, },
  { rintro ⟨x₁, hx₁⟩,
    simp only [hx₁],
    simp only [Module_homology_π', submodule.mkq_apply, submodule.quotient.mk_eq_zero,
      linear_map.mem_range, exists_apply_eq_apply], },
end

lemma Module_element_homology_is_zero_iff (z : S.homology) :
  z = 0 ↔ ∃ (x₁ : S.X₁), z = S.Module_homology_π (S.Module_f' x₁) :=
by simp only [Module_f'_comp_homology_π_apply, linear_map.zero_apply, exists_const]

lemma Module_exact_iff : S.exact ↔
  ∀ (x₂ : S.X₂) (hx₂ : S.g x₂ = 0), ∃ (x₁ : S.X₁), S.f x₁ = x₂ :=
begin
  rw [S.Module_left_homology_data.exact_iff, Module.is_zero_iff],
  split,
  { intros h x₂ hx₂,
    have eq : S.Module_homology_π' ⟨x₂, hx₂⟩ = 0 := h _,
    rw Module_homology_π'_eq_zero_iff at eq,
    obtain ⟨x₁, hx₁⟩ := eq,
    exact ⟨x₁, hx₁⟩, },
  { intros h γ,
    obtain ⟨⟨x₂, hx₂⟩, rfl⟩ := S.Module_surjective_homology_π' γ,
    obtain ⟨x₁, rfl⟩ := h x₂ hx₂,
    simp only [S.Module_homology_π'_eq_zero_iff, linear_map.mem_range, exists_apply_eq_apply], },
end

variables {S}

lemma Module_map_from_homology_ext {A : Module R} (f f' : S.homology ⟶ A)
  (eq : ∀ (x₂ : linear_map.ker S.g), f (S.Module_homology_π x₂) = f' (S.Module_homology_π x₂)) :
  f = f' :=
begin
  ext,
  obtain ⟨x₂, rfl⟩ := S.Module_surjective_homology_π x,
  exact eq x₂,
end

variables {S₁ S₂ : short_complex (Module.{u} R)} (φ φ' : S₁ ⟶ S₂)

@[simps]
def Module_map_ker : of R (linear_map.ker S₁.g) ⟶ of R (linear_map.ker S₂.g) :=
linear_map.cod_restrict (linear_map.ker S₂.g) (φ.τ₂.comp (linear_map.ker S₁.g).subtype)
  (begin
    rintro ⟨x₁, hx₁⟩,
    dsimp,
    rw linear_map.mem_ker at hx₁,
    rw [linear_map.mem_ker, ← comp_apply, φ.comm₂₃, comp_apply, hx₁, map_zero φ.τ₃],
  end)

@[simps]
def Module_map_homology : S₁.Module_homology ⟶ S₂.Module_homology :=
submodule.liftq _ (Module_map_ker φ ≫ S₂.Module_homology_π')
begin
  rintros _ ⟨x₁, rfl⟩,
  simp only [linear_map.mem_ker, Module.coe_comp, function.comp_app,
    Module_homology_π'_eq_zero_iff],
  refine ⟨φ.τ₁ x₁, _⟩,
  dsimp [Module_f'],
  simp only [← comp_apply, φ.comm₁₂],
end

@[simps]
def Module_left_homology_map_data : left_homology_map_data φ S₁.Module_left_homology_data
  S₂.Module_left_homology_data :=
{ φK := Module_map_ker φ,
  φH := Module_map_homology φ,
  commi' := rfl,
  commf'' := begin
    simp only [Module_left_homology_data_f'],
    ext x₁,
    dsimp [Module_f'],
    simp only [← comp_apply, φ.comm₁₂],
  end,
  commπ' := by { ext x₁, rcases x₁ with ⟨x₁, hx₁⟩, refl, }, }

@[simp, reassoc, elementwise]
lemma Module_homology_π_comp_homology_map :
  S₁.Module_homology_π ≫ homology_map φ = Module_map_ker φ ≫ S₂.Module_homology_π :=
begin
  dsimp only [Module_homology_π],
  rw (Module_left_homology_map_data φ).homology_map_eq,
  have eq := (Module_left_homology_map_data φ).commπ,
  dsimp only [Module_left_homology_map_data, Module_left_homology_data_π,
    Module_homology_iso] at ⊢ eq,
  simp only [← reassoc_of eq, assoc, iso.inv_hom_id_assoc],
end

example (h : homotopy φ φ') : homology_map φ = homology_map φ' :=
begin
  apply Module_map_from_homology_ext,
  rintro ⟨x₂, hx₂⟩,
  simp only [linear_map.mem_ker] at hx₂,
  simp only [Module_homology_π_comp_homology_map_apply],
  apply Module_homology_ext,
  refine ⟨h.h₁ x₂, _⟩,
  dsimp,
  simp only [h.comm₂, linear_map.add_apply, Module.coe_comp,
    function.comp_app, hx₂, h.h₂.map_zero],
  abel,
end

end short_complex

end category_theory
