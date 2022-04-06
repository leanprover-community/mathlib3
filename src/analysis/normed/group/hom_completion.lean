/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/

import analysis.normed.group.hom
import analysis.normed.group.completion
/-!
# Completion of normed group homs

Given two (semi) normed groups `G` and `H` and a normed group hom `f : normed_group_hom G H`,
we build and study a normed group hom
`f.completion  : normed_group_hom (completion G) (completion H)` such that the diagram

```
                   f
     G       ----------->     H

     |                        |
     |                        |
     |                        |
     V                        V

completion G -----------> completion H
            f.completion
```

commutes. The map itself comes from the general theory of completion of uniform spaces, but here
we want a normed group hom, study its operator norm and kernel.

The vertical maps in the above diagrams are also normed group homs constructed in this file.

## Main definitions and results:

* `normed_group_hom.completion`: see the discussion above.
* `normed_group.to_compl : normed_group_hom G (completion G)`: the canonical map from `G` to its
  completion, as a normed group hom
* `normed_group_hom.completion_to_compl`: the above diagram indeed commutes.
* `normed_group_hom.norm_completion`: `∥f.completion∥ = ∥f∥`
* `normed_group_hom.ker_le_ker_completion`: the kernel of `f.completion` contains the image of the
  kernel of `f`.
* `normed_group_hom.ker_completion`: the kernel of `f.completion` is the closure of the image of the
  kernel of `f` under an assumption that `f` is quantitatively surjective onto its image.
* `normed_group_hom.extension` : if `H` is complete, the extension of `f : normed_group_hom G H`
  to a `normed_group_hom (completion G) H`.
-/

noncomputable theory

open set normed_group_hom uniform_space

section completion

variables {G : Type*} [semi_normed_group G]
variables {H : Type*} [semi_normed_group H]
variables {K : Type*} [semi_normed_group K]

/-- The normed group hom induced between completions. -/
def normed_group_hom.completion (f : normed_group_hom G H) :
  normed_group_hom (completion G) (completion H) :=
{ bound' := begin
    use ∥f∥,
    intro y,
    apply completion.induction_on y,
    { exact is_closed_le
            (continuous_norm.comp $ f.to_add_monoid_hom.continuous_completion f.continuous)
            (continuous_const.mul continuous_norm) },
    { intro x,
      change ∥f.to_add_monoid_hom.completion _ ↑x∥ ≤ ∥f∥ * ∥↑x∥,
      rw f.to_add_monoid_hom.completion_coe f.continuous,
      simp only [completion.norm_coe],
      exact f.le_op_norm x }
  end,
  ..f.to_add_monoid_hom.completion f.continuous }

lemma normed_group_hom.completion_def (f : normed_group_hom G H) (x : completion G) :
  f.completion x = completion.map f x := rfl

@[simp]
lemma normed_group_hom.completion_coe_to_fun (f : normed_group_hom G H) :
  (f.completion : completion G → completion H) = completion.map f :=
by { ext x, exact normed_group_hom.completion_def f x }

@[simp]
lemma normed_group_hom.completion_coe (f : normed_group_hom G H) (g : G) : f.completion g = f g :=
completion.map_coe f.uniform_continuous _

/-- Completion of normed group homs as a normed group hom. -/
@[simps] def normed_group_hom_completion_hom :
  normed_group_hom G H →+ normed_group_hom (completion G) (completion H) :=
{ to_fun := normed_group_hom.completion,
  map_zero' := begin
    apply to_add_monoid_hom_injective,
    exact add_monoid_hom.completion_zero
  end,
  map_add' := λ f g, begin
    apply to_add_monoid_hom_injective,
    exact f.to_add_monoid_hom.completion_add g.to_add_monoid_hom f.continuous g.continuous,
  end }

@[simp]
lemma normed_group_hom.completion_id :
  (normed_group_hom.id G).completion = normed_group_hom.id (completion G) :=
begin
  ext x,
  rw [normed_group_hom.completion_def, normed_group_hom.coe_id, completion.map_id],
  refl
end

lemma normed_group_hom.completion_comp (f : normed_group_hom G H) (g : normed_group_hom H K) :
  g.completion.comp f.completion = (g.comp f).completion :=
begin
  ext x,
  rw [normed_group_hom.coe_comp, normed_group_hom.completion_def,
    normed_group_hom.completion_coe_to_fun, normed_group_hom.completion_coe_to_fun,
    completion.map_comp (normed_group_hom.uniform_continuous _)
    (normed_group_hom.uniform_continuous _)],
  refl
end

lemma normed_group_hom.completion_neg (f : normed_group_hom G H) :
  (-f).completion = -f.completion :=
normed_group_hom_completion_hom.map_neg f

lemma normed_group_hom.completion_add (f g : normed_group_hom G H) :
  (f + g).completion = f.completion + g.completion :=
normed_group_hom_completion_hom.map_add f g

lemma normed_group_hom.completion_sub (f g : normed_group_hom G H) :
  (f - g).completion = f.completion - g.completion :=
normed_group_hom_completion_hom.map_sub f g

@[simp]
lemma normed_group_hom.zero_completion : (0 : normed_group_hom G H).completion = 0 :=
normed_group_hom_completion_hom.map_zero

/-- The map from a normed group to its completion, as a normed group hom. -/
def normed_group.to_compl : normed_group_hom G (completion G) :=
{ to_fun := coe,
  map_add' := completion.to_compl.map_add,
  bound' := ⟨1, by simp [le_refl]⟩ }

open normed_group

lemma normed_group.norm_to_compl (x : G) : ∥to_compl x∥ = ∥x∥ :=
completion.norm_coe x

lemma normed_group.dense_range_to_compl : dense_range (to_compl : G → completion G) :=
completion.dense_inducing_coe.dense

@[simp]
lemma normed_group_hom.completion_to_compl (f : normed_group_hom G H) :
  f.completion.comp to_compl = to_compl.comp f :=
begin
  ext x,
  change f.completion x = _,
  simpa
end

@[simp] lemma normed_group_hom.norm_completion (f : normed_group_hom G H) : ∥f.completion∥ = ∥f∥ :=
begin
  apply f.completion.op_norm_eq_of_bounds (norm_nonneg _),
  { intro x,
    apply completion.induction_on x,
    { apply is_closed_le,
      continuity },
    { intro g,
      simp [f.le_op_norm  g] } },
  { intros N N_nonneg hN,
    apply f.op_norm_le_bound N_nonneg,
    intro x,
    simpa using hN x },
end

lemma normed_group_hom.ker_le_ker_completion (f : normed_group_hom G H) :
  (to_compl.comp $ incl f.ker).range ≤ f.completion.ker  :=
begin
  intros a h,
  replace h : ∃ y : f.ker, to_compl (y : G) = a, by simpa using h,
  rcases h with ⟨⟨g, g_in : g ∈ f.ker⟩, rfl⟩,
  rw f.mem_ker at g_in,
  change f.completion (g : completion G) = 0,
  simp [normed_group_hom.mem_ker, f.completion_coe g, g_in, completion.coe_zero],
end

lemma normed_group_hom.ker_completion {f : normed_group_hom G H} {C : ℝ}
  (h : f.surjective_on_with f.range C) :
  (f.completion.ker : set $ completion G) = closure (to_compl.comp $ incl f.ker).range :=
begin
  rcases h.exists_pos with ⟨C', C'_pos, hC'⟩,
  apply le_antisymm,
  { intros hatg hatg_in,
    rw semi_normed_group.mem_closure_iff,
    intros ε ε_pos,
    have hCf : 0 ≤ C'*∥f∥ := (zero_le_mul_left C'_pos).mpr (norm_nonneg f),
    have ineq : 0 < 1 + C'*∥f∥, by linarith,
    set δ := ε/(1 + C'*∥f∥),
    have δ_pos : δ > 0, from div_pos ε_pos ineq,
    obtain ⟨_, ⟨g : G, rfl⟩, hg : ∥hatg - g∥ < δ⟩ :=
      semi_normed_group.mem_closure_iff.mp (completion.dense_inducing_coe.dense hatg) δ δ_pos,
    obtain ⟨g' : G, hgg' : f g' = f g, hfg : ∥g'∥ ≤ C' * ∥f g∥⟩ :=
      hC' (f g) (mem_range_self g),
    have mem_ker : g - g' ∈ f.ker,
      by rw [f.mem_ker, f.map_sub, sub_eq_zero.mpr hgg'.symm],
    have : ∥f g∥ ≤ ∥f∥*∥hatg - g∥,
    calc
      ∥f g∥ = ∥f.completion g∥ : by rw [f.completion_coe, completion.norm_coe]
        ... = ∥f.completion g - 0∥ : by rw [sub_zero _]
        ... = ∥f.completion g - (f.completion hatg)∥ : by rw [(f.completion.mem_ker _).mp hatg_in]
        ... = ∥f.completion (g - hatg)∥ : by rw [f.completion.map_sub]
        ... ≤ ∥f.completion∥ * ∥(g :completion G) - hatg∥ : f.completion.le_op_norm _
        ... = ∥f∥ * ∥hatg - g∥ : by rw [norm_sub_rev, f.norm_completion],
    have : ∥(g' : completion G)∥ ≤ C'*∥f∥*∥hatg - g∥,
    calc
    ∥(g' : completion G)∥ = ∥g'∥ : completion.norm_coe _
                      ... ≤ C' * ∥f g∥ : hfg
                      ... ≤ C' * ∥f∥ * ∥hatg - g∥ : by { rw mul_assoc,
                                                        exact (mul_le_mul_left C'_pos).mpr this },
    refine ⟨g - g', _, _⟩,
    { norm_cast,
      rw normed_group_hom.comp_range,
      apply add_subgroup.mem_map_of_mem,
      simp only [incl_range, mem_ker] },
    { calc ∥hatg - (g - g')∥ = ∥hatg - g + g'∥ : by abel
      ... ≤ ∥hatg - g∥ + ∥(g' : completion G)∥ : norm_add_le _ _
      ... < δ + C'*∥f∥*∥hatg - g∥ : by linarith
      ... ≤ δ + C'*∥f∥*δ : add_le_add_left (mul_le_mul_of_nonneg_left hg.le hCf) δ
      ... = (1 + C'*∥f∥)*δ : by ring
      ... = ε : mul_div_cancel' _ ineq.ne.symm } },
  { rw ← f.completion.is_closed_ker.closure_eq,
    exact closure_mono f.ker_le_ker_completion }
end

end completion

section extension

variables {G : Type*} [semi_normed_group G]
variables {H : Type*} [semi_normed_group H] [separated_space H] [complete_space H]

/-- If `H` is complete, the extension of `f : normed_group_hom G H` to a
`normed_group_hom (completion G) H`. -/
def normed_group_hom.extension (f : normed_group_hom G H) : normed_group_hom (completion G) H :=
{ bound' := begin
    refine ⟨∥f∥, λ v, completion.induction_on v (is_closed_le _ _) (λ a, _)⟩,
    { exact continuous.comp continuous_norm completion.continuous_extension },
    { exact continuous.mul continuous_const continuous_norm },
    { rw [completion.norm_coe, add_monoid_hom.to_fun_eq_coe, add_monoid_hom.extension_coe],
      exact le_op_norm f a }
  end,
  ..f.to_add_monoid_hom.extension f.continuous }

lemma normed_group_hom.extension_def (f : normed_group_hom G H) (v : G) :
  f.extension v = completion.extension f v := rfl

@[simp] lemma normed_group_hom.extension_coe (f : normed_group_hom G H) (v : G) :
  f.extension v = f v := add_monoid_hom.extension_coe _ f.continuous _

lemma normed_group_hom.extension_coe_to_fun (f : normed_group_hom G H) :
  (f.extension : (completion G) → H) = completion.extension f := rfl

lemma normed_group_hom.extension_unique (f : normed_group_hom G H)
  {g : normed_group_hom (completion G) H} (hg : ∀ v, f v = g v) : f.extension = g :=
begin
  ext v,
  rw [normed_group_hom.extension_coe_to_fun, completion.extension_unique f.uniform_continuous
    g.uniform_continuous (λ a, hg a)]
end

end extension
