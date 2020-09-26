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

/-lemma cplx_exact (i) : exact_at (cplx M) i :=
begin
  unfold exact_at,

end-/

end projective

/-lemma projective_dimension_eq_zero_iff_projective (M : V) :
  projective_dimension M = 0 ↔ projective M :=
begin
  sorry,
end-/

end algebra.homology
