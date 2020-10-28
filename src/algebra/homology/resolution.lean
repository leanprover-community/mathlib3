/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.homology.chain_complex
import algebra.homology.exact
import algebra.homology.homology
import category_theory.abelian.projective

open category_theory category_theory.limits homological_complex

universes v u

variables {V : Type u} [category.{v} V] [abelian.{v} V] {b : ℤ}

namespace algebra.homology
local attribute [instance] has_zero_object.has_zero

/-- Todo: This is the case iff exact
    Todo: Move -/
def exact_at (C : homological_complex V b) (i : ℤ) := exact (C.d i) (C.d (i + b))

lemma single_exact (n : ℤ) (M : V) (i : ℤ) : exact_at (single n M) i :=
begin
  unfold exact_at,
  simp,
end

structure resolution (M : V) :=
(C : chain_complex V)
(exact : ∀ i, exact_at C i)
(iso_at : C.X (-1) ≅ M)
(bounded : bounded_below_by C (-1))

/-noncomputable
def resolution.cons (M : V) (E : Π i : ℕ, V) (d : Π i j : ℕ, E i ⟶ E j) (ε : E 0 ⟶ M) [epi ε]
  (hd : ∀ i, exact (d (i + 2) (i + 1)) (d (i + 1) i)) (hdε : exact (d 1 0) ε) : resolution M :=
{ C :=
  { X := --λ i, if i ≥ 0 then E (int.to_nat i) else if i = -1 then M else 0,
    λ i, match i with
    | (i : ℕ) := E i
    | -1 := M
    | _ := 0
    end,
    d := --λ i, if i ≥ 0 then d (int.to_nat (i + 1)) else 0,
    λ i, match i with
    | 0 := ε
    | (n + 1 : ℕ) := d (n + 1) ((n + 1) - 1)
    end,
    d_squared' := _ },
  exact := _,
  iso_at := _,
  bounded := _ }-/

structure projective_resolution (M : V) extends resolution M :=
(projective : ∀ i ≥ 0, projective (C.X i))

section enough_projectives
variables [enough_projectives V] (M : V)

section
variables (V)

structure my_arrow :=
(right left : V)
(hom : left ⟶ right)

end

noncomputable def next_step {left right : V} (hom : left ⟶ right) : my_arrow V :=
⟨left, _, projective.d hom⟩

noncomputable def ch : ℕ → my_arrow V
| 0 := ⟨_, _, projective.d (projective.π M)⟩
| (n + 1) := next_step (ch n).hom

#print ch._main

noncomputable def P : ℕ → V :=
λ n, (ch M n).left

noncomputable def d : Π n, P M (n + 1) ⟶ P M n :=
begin
  intro n,
  let := (ch M (n + 1)).hom,
  convert this,
  cases n; refl,
end

end enough_projectives

-- PROJECT
/-theorem nonempty_projective_resolution [enough_projectives V] (M : V) :
  nonempty (projective_resolution M) :=
sorry-/

open_locale classical
noncomputable theory

def projective_dimension (M : V) : with_top ℕ :=
if h : ∃ (n : ℕ) (E : projective_resolution M), length E.C = n then nat.find h else ⊤

section projective
variables (M : V) (h : projective M)

def cplx : chain_complex V :=
@homological_complex.glue _ _ _ _ 1
  (homological_complex.single 0 M)
  (homological_complex.single (-1) M)
  ((single_at_eq_n 0 M _ (by omega)).hom ≫ (single_at_eq_n (-1) M _ (by omega)).inv)
  (by simp) (by simp)

--                 0       -1
-- 0 ----> 0 --1--> M --0-> M --(-1)--> 0 ----> 0

lemma cplx_exact_one : exact_at (cplx M) 1 :=
begin
  unfold exact_at,
  dsimp only [←sub_eq_add_neg, cplx],
  rw [glue_d_n_sub_one, glue_d_n_sub_one_lt _ _ (sub_one_lt _)],
  simp only [zero_comp, single_d, comp_zero, category.assoc],
  rw ←abelian.mono_iff_exact_zero_left,
  apply mono_comp _ _,
  { apply_instance },
  apply mono_comp _ _,
  { apply_instance },
  exact mono_comp _ _
end

lemma chain_complex.eq_to_hom {C : chain_complex V} {n m : ℤ} (h : n = m) :
  C.d n = eq_to_hom (by rw h) ≫ C.d m ≫ eq_to_hom (by rw h) :=
by { subst h, simp }

lemma cplx_exact_zero : exact_at (cplx M) 0 :=
begin
  unfold exact_at,
  dsimp only [←sub_eq_add_neg, cplx],
  rw chain_complex.eq_to_hom (show (0 : ℤ) = 1 - 1, by omega),
  rw [glue_d_n_sub_one],
  rw glue_d_lt_n_sub_one _ _,
  tactic.swap,
  { omega },
  simp only [zero_comp, single_d, comp_zero, category.id_comp, eq_to_hom_refl, category.comp_id,
    category.assoc],
  rw ←abelian.epi_iff_exact_zero_right,
  apply epi_comp _ _,
  { apply_instance },
  apply epi_comp _ _,
  { apply_instance },
  exact epi_comp _ _
end

lemma exact_zero_zero_left {C : V} : exact (0 : 0 ⟶ 0) (0 : 0 ⟶ C) :=
begin
  rw ←abelian.epi_iff_exact_zero_right,
  apply_instance,
end

lemma exact_zero_zero_right {A : V} : exact (0 : A ⟶ 0) (0 : 0 ⟶ 0) :=
begin
  rw ←abelian.mono_iff_exact_zero_left,
  apply_instance
end

lemma cplx_exact_one_lt {i : ℤ} (h : 1 < i) : exact_at (cplx M) i :=
begin
  unfold exact_at,
  dsimp only [←sub_eq_add_neg, cplx],
  rw [glue_d_n_sub_one_lt, glue_d_n_sub_one_lt],
  simp,

end

/-lemma cplx_exact (i) : exact_at (cplx M) i :=
begin
  unfold exact_at,
  by_cases h : i = 1,
  {}
end-/

end projective

/-lemma projective_dimension_eq_zero_iff_projective (M : V) :
  projective_dimension M = 0 ↔ projective M :=
begin
  sorry,
end-/

end algebra.homology
