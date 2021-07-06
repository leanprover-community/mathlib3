import category_theory.abelian.ext
import algebra.category.Module.projective
import category_theory.concrete_category.basic
import data.zmod.basic
.

namespace Ext_zmod2
noncomputable theory

open category_theory Module category_theory.limits opposite

def ℤ2 : Module ℤ := of ℤ (zmod 2)

def X : ℕ → Module ℤ
| 0 := of ℤ ℤ
| 1 := of ℤ ℤ
| _ := 0

def d : Π (i j : ℕ), X i ⟶ X j
| 1 0 := linear_map.lsmul ℤ ℤ 2
| _ _ := 0

def complex : chain_complex (Module ℤ) ℕ :=
{ X := X,
  d := d,
  shape' := λ i j h, by { cases i, refl, cases i, cases j, exact (h rfl).elim, refl, refl },
  d_comp_d' := by { rintros i j k ⟨rfl : j = i + 1⟩ ⟨rfl : k = j + 1⟩, dsimp [d], rw zero_comp } }

def f : Π i, complex.X i ⟶ ((chain_complex.single₀ (Module ℤ)).obj ℤ2).X i
| 0 := (@int.cast_add_hom (zmod 2) _ _).to_int_linear_map
| _ := 0

def π : complex ⟶ (chain_complex.single₀ (Module ℤ)).obj ℤ2 :=
{ f := f,
  comm' :=
  begin
    rintros i ⟨j⟩ ⟨rfl : j = i + 1⟩, swap, { simp [f], },
    dsimp [complex, d, f],
    ext,
    simp only [mul_one, algebra.id.smul_eq_mul, fin.coe_zero, int.cast_bit0,
      add_monoid_hom.coe_to_int_linear_map, int.cast_one, function.comp_app, int.coe_cast_add_hom,
      linear_map.lsmul_apply, category_theory.coe_comp, linear_map.zero_apply],
    refl,
  end }
.

-- TODO: generalize
lemma projective_zero : projective (0 : Module ℤ) :=
{ factors := λ A B f g hg,
  begin
    refine ⟨0, _⟩,
    ext ⟨⟩,
    simp only [zero_comp, linear_map.zero_apply],
    exact f.map_zero.symm
  end }

lemma projective_int : projective (of ℤ ℤ) :=
{ factors := λ A B f g hg,
  begin
    obtain ⟨a, ha⟩ : ∃ a, g a = f (1 : ℤ), sorry,
    refine ⟨(linear_map.lsmul ℤ A).flip a, _⟩,
    ext,
    simp only [ha, function.comp_app, one_smul, linear_map.lsmul_apply, category_theory.coe_comp,
      linear_map.flip_apply],
  end }

lemma exact₀ : exact (complex.d 1 0) (π.f 0) :=
sorry

def P : ProjectiveResolution ℤ2 :=
{ complex := complex,
  π := π,
  projective :=
  begin
    intro n,
    cases n, apply projective_int,
    cases n, apply projective_int,
    apply projective_zero
  end,
  -- there is redundancy in `exact₀`: `π` already asserts that they compose to `0`.
  exact₀ := exact₀,
  exact := λ n,
  begin
    suffices : mono (complex.d (n + 1) n),
    { exactI exact_zero_left_of_mono _ },
    dsimp [complex], cases n; dsimp [d], swap, { sorry },
    apply concrete_category.mono_of_injective,
    intros m n h, simp only [algebra.id.smul_eq_mul, linear_map.lsmul_apply] at h,
    apply @mul_left_cancel' ℤ _ _ _ _ two_ne_zero h,
  end,
  epi :=
  begin
    apply concrete_category.epi_of_surjective,
    apply zmod.int_cast_surjective
  end }
.

-- def Ext_1_Z2_Z2 : ((Ext ℤ (Module ℤ) 1).obj (op $ ℤ2)).obj ℤ2 ≅ _ :=
-- functor.left_derived_obj_iso _ 1 P
.



end Ext_zmod2
