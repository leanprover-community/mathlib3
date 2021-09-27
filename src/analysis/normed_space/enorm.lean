/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import analysis.normed_space.basic

/-!
# Extended norm

In this file we define a structure `enorm 𝕜 V` representing an extended norm (i.e., a norm that can
take the value `∞`) on a vector space `V` over a normed field `𝕜`. We do not use `class` for
an `enorm` because the same space can have more than one extended norm. For example, the space of
measurable functions `f : α → ℝ` has a family of `L_p` extended norms.

We prove some basic inequalities, then define

* `emetric_space` structure on `V` corresponding to `e : enorm 𝕜 V`;
* the subspace of vectors with finite norm, called `e.finite_subspace`;
* a `normed_space` structure on this space.

The last definition is an instance because the type involves `e`.

## Implementation notes

We do not define extended normed groups. They can be added to the chain once someone will need them.

## Tags

normed space, extended norm
-/

local attribute [instance, priority 1001] classical.prop_decidable
open_locale ennreal

/-- Extended norm on a vector space. As in the case of normed spaces, we require only
`∥c • x∥ ≤ ∥c∥ * ∥x∥` in the definition, then prove an equality in `map_smul`. -/
structure enorm (𝕜 : Type*) (V : Type*) [normed_field 𝕜] [add_comm_group V] [module 𝕜 V] :=
(to_fun : V → ℝ≥0∞)
(eq_zero' : ∀ x, to_fun x = 0 → x = 0)
(map_add_le' : ∀ x y : V, to_fun (x + y) ≤ to_fun x + to_fun y)
(map_smul_le' : ∀ (c : 𝕜) (x : V), to_fun (c • x) ≤ nnnorm c * to_fun x)

namespace enorm

variables {𝕜 : Type*} {V : Type*} [normed_field 𝕜] [add_comm_group V] [module 𝕜 V]
  (e : enorm 𝕜 V)

instance : has_coe_to_fun (enorm 𝕜 V) := ⟨_, enorm.to_fun⟩

lemma coe_fn_injective : @function.injective (enorm 𝕜 V) (V → ℝ≥0∞) coe_fn :=
λ e₁ e₂ h, by cases e₁; cases e₂; congr; exact h

@[ext] lemma ext {e₁ e₂ : enorm 𝕜 V} (h : ∀ x, e₁ x = e₂ x) : e₁ = e₂ :=
coe_fn_injective $ funext h

lemma ext_iff {e₁ e₂ : enorm 𝕜 V} : e₁ = e₂ ↔ ∀ x, e₁ x = e₂ x :=
⟨λ h x, h ▸ rfl, ext⟩

@[simp, norm_cast] lemma coe_inj {e₁ e₂ : enorm 𝕜 V} : ⇑e₁ = e₂ ↔ e₁ = e₂ :=
coe_fn_injective.eq_iff

@[simp] lemma map_smul (c : 𝕜) (x : V) : e (c • x) = nnnorm c * e x :=
le_antisymm (e.map_smul_le' c x) $
begin
  by_cases hc : c = 0, { simp [hc] },
  calc (nnnorm c : ℝ≥0∞) * e x = nnnorm c * e (c⁻¹ • c • x) : by rw [inv_smul_smul' hc]
  ... ≤ nnnorm c * (nnnorm (c⁻¹) * e (c • x)) : _
  ... = e (c • x) : _,
  { exact ennreal.mul_le_mul (le_refl _) (e.map_smul_le' _ _) },
  { rw [← mul_assoc, normed_field.nnnorm_inv, ennreal.coe_inv,
     ennreal.mul_inv_cancel _ ennreal.coe_ne_top, one_mul]; simp [hc] }
end

@[simp] lemma map_zero : e 0 = 0 :=
by { rw [← zero_smul 𝕜 (0:V), e.map_smul], norm_num }

@[simp] lemma eq_zero_iff {x : V} : e x = 0 ↔ x = 0 :=
⟨e.eq_zero' x, λ h, h.symm ▸ e.map_zero⟩

@[simp] lemma map_neg (x : V) : e (-x) = e x :=
calc e (-x) = nnnorm (-1:𝕜) * e x : by rw [← map_smul, neg_one_smul]
        ... = e x                 : by simp

lemma map_sub_rev (x y : V) : e (x - y) = e (y - x) :=
by rw [← neg_sub, e.map_neg]

lemma map_add_le (x y : V) : e (x + y) ≤ e x + e y := e.map_add_le' x y

lemma map_sub_le (x y : V) : e (x - y) ≤ e x + e y :=
calc e (x - y) = e (x + -y)   : by rw sub_eq_add_neg
           ... ≤ e x + e (-y) : e.map_add_le x (-y)
           ... = e x + e y    : by rw [e.map_neg]

instance : partial_order (enorm 𝕜 V) :=
{ le := λ e₁ e₂, ∀ x, e₁ x ≤ e₂ x,
  le_refl := λ e x, le_refl _,
  le_trans := λ e₁ e₂ e₃ h₁₂ h₂₃ x, le_trans (h₁₂ x) (h₂₃ x),
  le_antisymm := λ e₁ e₂ h₁₂ h₂₁, ext $ λ x, le_antisymm (h₁₂ x) (h₂₁ x) }

/-- The `enorm` sending each non-zero vector to infinity. -/
noncomputable instance : has_top (enorm 𝕜 V) :=
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

noncomputable instance : inhabited (enorm 𝕜 V) := ⟨⊤⟩

lemma top_map {x : V} (hx : x ≠ 0) : (⊤ : enorm 𝕜 V) x = ⊤ := if_neg hx

noncomputable instance : semilattice_sup_top (enorm 𝕜 V) :=
{ le := (≤),
  lt := (<),
  top := ⊤,
  le_top := λ e x, if h : x = 0 then by simp [h] else by simp [top_map h],
  sup := λ e₁ e₂,
  { to_fun := λ x, max (e₁ x) (e₂ x),
    eq_zero' := λ x h, e₁.eq_zero_iff.1 (ennreal.max_eq_zero_iff.1 h).1,
    map_add_le' := λ x y, max_le
      (le_trans (e₁.map_add_le _ _) $ add_le_add (le_max_left _ _) (le_max_left _ _))
      (le_trans (e₂.map_add_le _ _) $ add_le_add (le_max_right _ _) (le_max_right _ _)),
    map_smul_le' := λ c x, le_of_eq $ by simp only [map_smul, ennreal.mul_max] },
  le_sup_left := λ e₁ e₂ x, le_max_left _ _,
  le_sup_right := λ e₁ e₂ x, le_max_right _ _,
  sup_le := λ e₁ e₂ e₃ h₁ h₂ x, max_le (h₁ x) (h₂ x),
  .. enorm.partial_order }

@[simp, norm_cast] lemma coe_max (e₁ e₂ : enorm 𝕜 V) : ⇑(e₁ ⊔ e₂) = λ x, max (e₁ x) (e₂ x) := rfl

@[norm_cast]
lemma max_map (e₁ e₂ : enorm 𝕜 V) (x : V) : (e₁ ⊔ e₂) x = max (e₁ x) (e₂ x) := rfl

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
def finite_subspace : subspace 𝕜 V :=
{ carrier   := {x | e x < ⊤},
  zero_mem' := by simp,
  add_mem'  := λ x y hx hy, lt_of_le_of_lt (e.map_add_le x y) (ennreal.add_lt_top.2 ⟨hx, hy⟩),
  smul_mem' := λ c x (hx : _ < _),
    calc e (c • x) = nnnorm c * e x : e.map_smul c x
               ... < ⊤              : ennreal.mul_lt_top ennreal.coe_ne_top hx.ne }

/-- Metric space structure on `e.finite_subspace`. We use `emetric_space.to_metric_space_of_dist`
to ensure that this definition agrees with `e.emetric_space`. -/
instance : metric_space e.finite_subspace :=
begin
  letI := e.emetric_space,
  refine emetric_space.to_metric_space_of_dist _ (λ x y, _) (λ x y, rfl),
  change e (x - y) ≠ ⊤,
  exact ne_top_of_le_ne_top (ennreal.add_lt_top.2 ⟨x.2, y.2⟩).ne (e.map_sub_le x y)
end

lemma finite_dist_eq (x y : e.finite_subspace) : dist x y = (e (x - y)).to_real := rfl

lemma finite_edist_eq (x y : e.finite_subspace) : edist x y = e (x - y) := rfl

/-- Normed group instance on `e.finite_subspace`. -/
instance : normed_group e.finite_subspace :=
{ norm := λ x, (e x).to_real,
  dist_eq := λ x y, rfl }

lemma finite_norm_eq (x : e.finite_subspace) : ∥x∥ = (e x).to_real := rfl

/-- Normed space instance on `e.finite_subspace`. -/
instance : normed_space 𝕜 e.finite_subspace :=
{ norm_smul_le := λ c x, le_of_eq $ by simp [finite_norm_eq, ennreal.to_real_mul] }

end enorm
