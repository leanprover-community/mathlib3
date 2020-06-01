/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import analysis.normed_space.basic

/-!
# Extended norm

In this file we define structure `enorm k V` representing an extended norm (i.e., a norm that can
take the value `∞`) on a vector space `V` over a normed field `k`. We do not use `class` for
an `enorm` because the same space can have more than one extended norm. For example, the space of
measurable functions `f : α → ℝ` has a family of `L_p` extended norms.

We prove some basic inequalities, then define

* `emetric_space` structure on `V` corresponding to `e : enorm k V`;
* the subspace of vectors with finite norm;
* a `normed_space` structure on this space.

The last definition is an instance because the type involves `e`.

## Implementation notes

We do not define extended normed groups. They can be added to the chain once someone will need them.

## Tags

normed space, extended norm
-/

open_locale classical

/-- Extended norm on a vector space. -/
structure enorm (k : Type*) (V : Type*) [normed_field k] [add_comm_group V] [vector_space k V] :=
(to_fun : V → ennreal)
(eq_zero' : ∀ x, to_fun x = 0 → x = 0)
(map_add_le' : ∀ x y : V, to_fun (x + y) ≤ to_fun x + to_fun y)
(map_smul_le' : ∀ (c : k) (x : V), to_fun (c • x) ≤ nnnorm c * to_fun x)

namespace enorm

variables {k : Type*} {V : Type*} [normed_field k] [add_comm_group V] [vector_space k V]
  (e : enorm k V)

instance : has_coe_to_fun (enorm k V) := ⟨_, enorm.to_fun⟩

/-- The `enorm` sending each non-zero vector to infinity. -/
noncomputable instance : inhabited (enorm k V) :=
⟨{ to_fun := λ x, if x = 0 then 0 else ⊤,
   eq_zero' := λ x, by { split_ifs; simp [*] },
   map_add_le' := λ x y,
     begin
       split_ifs with hxy hx hy hy hx hy hy; try { simp [*] },
       simpa [hx, hy] using hxy
     end,
   map_smul_le' := λ c x,
     begin
       split_ifs with hcx hx hx; simp only [smul_eq_zero, not_or_distrib] at hcx,
       { simp only [mul_zero, le_refl] },
       { have : c = 0, by tauto,
         simp [this] },
       { tauto },
       { simp [hcx.1] }
     end }⟩

@[simp] lemma map_smul (c : k) (x : V) : e (c • x) = nnnorm c * e x :=
le_antisymm (e.map_smul_le' c x) $
begin
  by_cases hc : c = 0, { simp [hc] },
  calc (nnnorm c : ennreal) * e x = nnnorm c * e (c⁻¹ • c • x) : by rw [inv_smul_smul' hc]
  ... ≤ nnnorm c * (nnnorm (c⁻¹) * e (c • x)) : _
  ... = e (c • x) : _,
  { exact ennreal.mul_le_mul (le_refl _) (e.map_smul_le' _ _) },
  { rw [← mul_assoc, normed_field.nnnorm_inv, ennreal.coe_inv,
     ennreal.mul_inv_cancel _ ennreal.coe_ne_top, one_mul]; simp [hc] }
end

@[simp] lemma map_zero : e 0 = 0 :=
by { rw [← zero_smul k (0:V), e.map_smul], norm_num }

@[simp] lemma eq_zero_iff {x : V} : e x = 0 ↔ x = 0 :=
⟨e.eq_zero' x, λ h, h.symm ▸ e.map_zero⟩

@[simp] lemma map_neg (x : V) : e (-x) = e x :=
calc e (-x) = nnnorm (-1:k) * e x : by rw [← map_smul, neg_one_smul]
        ... = e x                 : by simp

lemma map_sub_rev (x y : V) : e (x - y) = e (y - x) :=
by rw [← neg_sub, e.map_neg]

lemma map_add_le (x y : V) : e (x + y) ≤ e x + e y := e.map_add_le' x y

lemma map_sub_le (x y : V) : e (x - y) ≤ e x + e y :=
calc e (x - y) ≤ e x + e (-y) : e.map_add_le x (-y)
           ... = e x + e y    : by rw [e.map_neg]

/-- Structure of an `emetric_space` defined by an extended norm. -/
def emetric_space : emetric_space V :=
{ edist := λ x y, e (x - y),
  edist_self := λ x, by simp,
  eq_of_edist_eq_zero := λ x y, by simp [sub_eq_zero],
  edist_comm := e.map_sub_rev,
  edist_triangle := λ x y z,
    calc e (x - z) = e ((x - y) + (y - z)) : by rw [sub_add_sub_cancel]
               ... ≤ e (x - y) + e (y - z) : e.map_add_le (x - y) (y - z) }

/-- The subspace of vectors with finite enorm. -/
def finite_subspace : subspace k V :=
{ carrier := {x | e x < ⊤},
  zero    := by simp,
  add     := λ x y hx hy, lt_of_le_of_lt (e.map_add_le x y) (ennreal.add_lt_top.2 ⟨hx, hy⟩),
  smul    := λ c x hx,
    calc e (c • x) = nnnorm c * e x : e.map_smul c x
               ... < ⊤              : ennreal.mul_lt_top ennreal.coe_lt_top hx }

/-- Metric space structure on `e.finite_subspace`. We use `emetric_space.to_metric_space_of_dist`
to ensure that this definition agrees with `e.emetric_space`. -/
instance : metric_space e.finite_subspace :=
begin
  letI := e.emetric_space,
  refine emetric_space.to_metric_space_of_dist _ (λ x y, _) (λ x y, rfl),
  change e (x - y) ≠ ⊤,
  rw [← ennreal.lt_top_iff_ne_top],
  exact lt_of_le_of_lt (e.map_sub_le x y) (ennreal.add_lt_top.2 ⟨x.2, y.2⟩)
end

lemma finite_dist_eq (x y : e.finite_subspace) : dist x y = (e (x - y)).to_real := rfl

lemma finite_edist_eq (x y : e.finite_subspace) : edist x y = e (x - y) := rfl

/-- Normed group instance on `e.finite_subspace`. -/
instance : normed_group e.finite_subspace :=
{ norm := λ x, (e x).to_real,
  dist_eq := λ x y, rfl }

lemma finite_norm_eq (x : e.finite_subspace) : ∥x∥ = (e x).to_real := rfl

/-- Normed space instance on `e.finite_subspace`. -/
instance : normed_space k e.finite_subspace :=
{ norm_smul_le := λ c x, le_of_eq $
    by simp [finite_norm_eq, ← ennreal.to_real_mul_to_real] }

end enorm
