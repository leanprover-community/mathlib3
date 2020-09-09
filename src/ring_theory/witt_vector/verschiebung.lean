/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.witt_vector.basic


/-! ## The Verschiebung operator -/

namespace witt_vector

variables {p : ℕ} {R S : Type*} [hp : fact p.prime] [comm_ring R] [comm_ring S]
local notation `𝕎` := witt_vector p -- type as `\bbW`

local attribute [semireducible] witt_vector
local attribute [instance] mv_polynomial.invertible_rat_coe_nat

def verschiebung_fun : 𝕎 R → 𝕎 R
| x 0     := 0
| x (n+1) := x n

include hp

/-- verschiebung is a natural transformation -/
@[simp] lemma map_verschiebung_fun (f : R →+* S) (x : 𝕎 R) :
  map f (verschiebung_fun x) = verschiebung_fun (map f x) :=
by { ext ⟨-, -⟩, exact f.map_zero, refl }

@[simp] lemma ghost_component_zero_verschiebung_fun (x : 𝕎 R) :
  ghost_component 0 (verschiebung_fun x) = 0 :=
by simp only [ghost_component, aeval_witt_polynomial, verschiebung_fun,
    pow_one, finset.sum_singleton, finset.range_one, nat.pow_zero, mul_zero]

@[simp] lemma ghost_component_verschiebung_fun (x : 𝕎 R) (n : ℕ) :
  ghost_component (n + 1) (verschiebung_fun x) = p * ghost_component n x :=
begin
  simp only [ghost_component, aeval_witt_polynomial],
  rw [finset.sum_range_succ', verschiebung_fun, zero_pow (nat.pow_pos hp.pos _), mul_zero, add_zero,
      finset.mul_sum, finset.sum_congr rfl],
  rintro i -,
  rw [pow_succ, mul_assoc, verschiebung_fun, nat.succ_sub_succ],
end

lemma verschiebung_add_aux₁ (x y : 𝕎 (mv_polynomial R ℚ)) :
  verschiebung_fun (x + y) = verschiebung_fun x + verschiebung_fun y :=
begin
  apply (ghost_map.bijective_of_invertible p (mv_polynomial R ℚ)).1,
  ext1 n,
  rw ring_hom.map_add,
  simp only [pi.add_apply],
  cases n,
  { simp only [add_zero, ghost_component_zero_verschiebung_fun, ghost_map_apply], },
  { simp only [ghost_map_apply, ghost_component_verschiebung_fun, ghost_component_add, mul_add], }
end

lemma vershiebung_add_aux₂ (x y : 𝕎 (mv_polynomial R ℤ)) :
  verschiebung_fun (x + y) = verschiebung_fun x + verschiebung_fun y :=
begin
  refine map_injective (mv_polynomial.map (int.cast_ring_hom ℚ))
    (mv_polynomial.coe_int_rat_map_injective _) _,
  simp only [verschiebung_add_aux₁, ring_hom.map_add, map_verschiebung_fun],
end

variables {R}

noncomputable
def verschiebung : 𝕎 R →+ 𝕎 R :=
{ to_fun := verschiebung_fun,
  map_zero' :=
  begin
    ext ⟨⟩,
    { rw zero_coeff, refl },
    { calc coeff n (0 : 𝕎 R) = 0             : by rw zero_coeff
                            ... = coeff (n+1) 0 : by rw zero_coeff, }
  end,
  map_add' :=
  begin
    intros x y,
    rcases map_surjective _ (counit_surjective R) x with ⟨x, rfl⟩,
    rcases map_surjective _ (counit_surjective R) y with ⟨y, rfl⟩,
    rw [← ring_hom.map_add],
    iterate 3 { rw [← map_verschiebung_fun] },
    rw [vershiebung_add_aux₂, ring_hom.map_add],
  end }

@[simp] lemma verschiebung_coeff_zero (x : 𝕎 R) :
  (verschiebung x).coeff 0 = 0 := rfl

@[simp] lemma verschiebung_coeff_add_one (x : 𝕎 R) (n : ℕ) :
  (verschiebung x).coeff (n + 1) = x.coeff n := rfl

@[simp] lemma verschiebung_coeff_succ (x : 𝕎 R) (n : ℕ) :
  (verschiebung x).coeff n.succ = x.coeff n := rfl

/-- Verschiebung is a natural transformation. -/
@[simp] lemma map_verschiebung (f : R →+* S) (x : 𝕎 R) :
  map f (verschiebung x) = verschiebung (map f x) :=
map_verschiebung_fun _ _

@[simp] lemma ghost_component_zero_verschiebung (x : 𝕎 R) :
  ghost_component 0 (verschiebung x) = 0 :=
ghost_component_zero_verschiebung_fun _

@[simp] lemma ghost_component_verschiebung (x : 𝕎 R) (n : ℕ) :
  ghost_component (n + 1) (verschiebung x) = p * ghost_component n x :=
ghost_component_verschiebung_fun _ _

end witt_vector
