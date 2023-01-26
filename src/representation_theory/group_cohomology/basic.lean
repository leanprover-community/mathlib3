/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import representation_theory.group_cohomology.resolution

/-!
# The group cohomology of a `k`-linear `G`-representation

This file defines group cohomology of `A : Rep k G` to be the cohomology of the complex
`0 → Fun(G⁰, A) → Fun(G¹, A) → Fun(G², A) → ...`, with differential `dⁿ` sending `f: Gⁿ → A` to
the function sending `(g₀, ..., gₙ) ↦ A.ρ(g₀)(f(g₁, ..., gₙ))`
`+ ∑ (-1)^i⬝f(g₀, ..., gᵢgᵢ₊₁, ..., gₙ) + (-1)ⁿ⁺¹⬝f(g₀, ..., gₙ₋₁)` (where the sum ranges from
`i = 0` to `i = n - 1`.)

We have `Fun(Gⁿ, A) ≅ Hom(k[Gⁿ⁺¹], A)` where the righthand side is representation morphisms. Thus
we show that our differential agrees with the differential induced by this isomorphism and the
differential in `Hom(P, A)`, where `P` is the standard resolution of `k` as a trivial
`k`-linear `G`-representation.

This gives us for free a proof that our `dⁿ` squares to zero. It also gives us an isomorphism
`Hⁿ(G, A) ≅ Extⁿ_{Rep k G}(k, A).`

## Main definitions

* `blah`

## Implementation notes

Group cohomology is typically stated for `G`-modules, or equivalently modules over the group ring
`ℤ[G].` However, `ℤ` can be generalized to any commutative ring `k`, which is what we use.
Moreover, we express `k[G]`-module structures on a module `k`-module `A` using the `Rep`
definition. We avoid using instances `module (monoid_algebra k G) A` so that we do not run into
possible scalar action diamonds.
-/

noncomputable theory

universes v u

variables {k G : Type u} [comm_ring k] {n : ℕ}

open_locale tensor_product
open category_theory
namespace group_cohomology

-- terrible name...
/-- The complex `Hom(P, A)`, where `P` is the standard resolution of `k` as a trivial `k`-linear
`G`-representation. -/
abbreviation hom_resolution (A : Rep k G) : cochain_complex (Module.{u} k) :=
homological_complex.unop
  ((((linear_yoneda k (Rep k G)).obj A).right_op.map_homological_complex _).obj
  (group_cohomology.resolution k G))

variables {A}

-- weird that simplifying the type of x made this not time out when i simp only in it in inhomog
lemma hom_resolution_d_apply (i j : ℕ) (x : (group_cohomology.resolution k G).X i ⟶ A) :
  A.hom_resolution.d i j x = (group_cohomology.resolution k G).d j i ≫ x :=
rfl

variables {k G n A}

/-- Sends `(g₀, ..., gₙ)` to `(g₀, ..., gⱼgⱼ₊₁, ..., gₙ)`. -/
def d_aux (j : ℕ) (g : fin (n + 1) → G) (k : fin n) : G :=
if (k : ℕ) < j then g (fin.cast_lt k (lt_trans k.2 $ lt_add_one _)) else
if (k : ℕ) = j then g (fin.cast_lt k (lt_trans k.2 $ lt_add_one _)) * g (fin.add_nat 1 k)
else g (fin.add_nat 1 k)

lemma d_aux_lt_apply {j : ℕ} (g : fin (n + 1) → G) {k : fin n} (h : (k : ℕ) < j) :
  d_aux j g k = g (fin.cast_lt k (lt_trans k.2 $ lt_add_one _)) := if_pos h

lemma d_aux_eq_apply {j : ℕ} (g : fin (n + 1) → G) {k : fin n} (h : (k : ℕ) = j) :
  d_aux j g k = g (fin.cast_lt k (lt_trans k.2 $ lt_add_one _)) * g (fin.add_nat 1 k) :=
begin
  have : ¬(k : ℕ) < j, by linarith,
  unfold d_aux,
  rw [if_neg this, if_pos h],
end

lemma d_aux_neg_apply {j : ℕ} (g : fin (n + 1) → G) {k : fin n}
  (h : ¬(k : ℕ) < j) (h' : ¬(k : ℕ) = j) :
  d_aux j g k = g (fin.add_nat 1 k) :=
begin
  unfold d_aux,
  rw [if_neg h, if_neg h'],
end

def d_to_fun (f : (fin n → G) → A) : (fin (n + 1) → G) → A :=
λ g, A.ρ (g 0) (f (λ i, g (fin.add_nat 1 i)))
  + (finset.range (n + 1)).sum (λ j, (-1 : k) ^ (j + 1) • f (d_aux j g))

lemma fin.coe_cast_succ (i : fin n) :
  i.cast_succ = (↑(↑i : ℕ)) :=
begin
  ext,
  rw fin.coe_coe_of_lt (lt_trans (fin.is_lt _) n.lt_succ_self),
  refl,
end

lemma d_eq_aux (f : (fin n → G) → A) (g : fin (n + 1) → G) (a : fin (n + 1)) :
  (-1 : k) ^ (a.succ : ℕ) • ((diagonal_hom_equiv A n).symm f).hom
  (finsupp.single (fin.partial_prod g ∘ a.succ.succ_above) 1)
  = (-1 : k) ^ ((a : ℕ) + 1) • f (d_aux (a : ℕ) g) :=
begin
  simp only [diagonal_hom_equiv_symm_apply, fin.coe_succ, function.comp_app,
    fin.succ_succ_above_zero, fin.partial_prod_zero, map_one, fin.coe_eq_cast_succ,
    fin.succ_succ_above_succ, linear_map.one_apply, fin.partial_prod_succ],
  congr,
  ext,
  by_cases (x : ℕ) < a,
  { rw [fin.succ_above_below, fin.succ_above_below, inv_mul_cancel_left, d_aux_lt_apply _ h],
    { refl },
    { assumption },
    { simp only [fin.lt_def, fin.val_eq_coe, fin.coe_cast_succ,
        fin.coe_succ, lt_trans h (nat.lt_succ_self _)] }},
  { by_cases hx : (x : ℕ) = a,
    { rw [d_aux_eq_apply _ hx, fin.succ_above_below, fin.succ_above_above, fin.cast_succ_fin_succ,
        fin.partial_prod_succ, mul_assoc, inv_mul_cancel_left, fin.add_nat_one],
      { refl },
      { simpa only [fin.le_iff_coe_le_coe, ←hx] },
      { simp only [fin.lt_iff_coe_lt_coe, fin.coe_cast_succ, fin.coe_succ, hx, nat.lt_succ_self] }},
    { rw [d_aux_neg_apply _ h hx, fin.succ_above_above, fin.succ_above_above,
        fin.partial_prod_succ, fin.cast_succ_fin_succ, fin.partial_prod_succ, inv_mul_cancel_left,
        fin.add_nat_one],
      { exact not_lt.1 h },
      { rw [fin.le_iff_coe_le_coe, fin.coe_succ],
        exact nat.succ_le_of_lt (lt_of_le_of_ne (not_lt.1 h) (ne.symm hx)) }}}
end

lemma d_eq (f : (fin n → G) → A) (g : fin (n + 1) → G) :
  ((diagonal_hom_equiv A n).to_Module_iso.inv ≫ (hom_resolution A).d n (n + 1)
    ≫ (diagonal_hom_equiv A (n + 1)).to_Module_iso.hom) f g = d_to_fun f g :=
begin
  simp only [linear_equiv.to_Module_iso_hom, linear_equiv.to_Module_iso_inv,
    hom_resolution_d_apply, Module.coe_comp, linear_equiv.coe_coe, function.comp_app],
  rw [finally_apply, Action.comp_hom, Module.coe_comp, function.comp_apply,
    group_cohomology.resolution.d_eq, group_cohomology.resolution.d_of, linear_map.map_sum],
  simp only [←finsupp.smul_single_one _ ((-1 : k) ^ _), map_smul],
  rw [d_to_fun, fin.sum_univ_succ, fin.coe_zero, pow_zero, one_smul, finally_symm_apply],
  congr' 1,
  { simp only [function.comp_apply, fin.zero_succ_above, fin.partial_prod_succ,
      fin.cast_succ_zero, fin.partial_prod_zero, one_mul, fin.coe_eq_cast_succ, mul_inv_rev,
      fin.add_nat_one],
    simp only [fin.cast_succ_fin_succ, fin.partial_prod_succ],
    congr,
    ext,
    simp only [←fin.coe_cast_succ, mul_assoc, inv_mul_cancel_left], },
  { refine @finset.sum_bij _ (fin (n + 1)) ℕ _ finset.univ (finset.range (n + 1))
 _ _ (λ i hi, i) (λ a ha, finset.mem_range.2 a.2) _ (λ a b ha hb hab, by ext; exact hab)
  (λ a ha, ⟨⟨a, finset.mem_range.1 ha⟩, finset.mem_univ _, rfl⟩),
    intros a ha,
    exact d_aux_eq _ _ _,
      }
end

lemma d_eq' (f : (fin n → G) → A) :
  ((finally A n).to_Module_iso.inv ≫
    (hom_resolution A).d n (n + 1)
    ≫ (finally A (n + 1)).to_Module_iso.hom) f = d_to_fun f :=
by ext; exact d_eq _ _

variables (A n)

def d : ((fin n → G) → A) →ₗ[k] (fin (n + 1) → G) → A :=
{ to_fun := d_to_fun,
  map_add' := λ f g,
  begin
    ext x,
    simp only [pi.add_apply, ←d_eq, map_add],
  end,
  map_smul' := λ r f,
  begin
    ext x,
    simpa only [pi.smul_apply, ←d_eq, map_smul],
  end }

lemma d_apply (x : (fin n → G) → A) : A.d n x = d_to_fun x :=
rfl

lemma d_eq'' : ((finally A n).to_Module_iso.inv ≫
  (hom_resolution A).d n (n + 1)
  ≫ (finally A (n + 1)).to_Module_iso.hom) = A.d n :=
by ext; exact d_eq _ _

@[simps] noncomputable def inhomog : cochain_complex (Module k) ℕ :=
cochain_complex.of (λ n, Module.of k ((fin n → G) → A))
(λ n, d A n) (λ n,
begin
  ext x y,
  simp only [Module.coe_comp, function.comp_app, d_apply, linear_map.zero_apply, pi.zero_apply],
  rw ←d_eq', rw ←d_eq',
  simp only [Module.coe_comp, function.comp_app, linear_equiv.to_Module_iso_hom,
    linear_equiv.to_Module_iso_inv, linear_equiv.coe_coe, linear_equiv.symm_apply_apply],
  have := linear_map.ext_iff.1 (A.hom_resolution.d_comp_d n (n + 1) (n + 2)),
  simp only [Module.coe_comp, function.comp_app] at this,
  rw this,
  simp only [linear_map.zero_apply, map_zero, pi.zero_apply],
end)

def inhomog_iso :
  A.inhomog ≅ A.hom_resolution :=
homological_complex.hom.iso_of_components
(λ i, (finally A i).to_Module_iso.symm) $
begin
  intros i j hij,
  dunfold inhomog,
  cases hij,
  erw cochain_complex.of_d,
  rw ←d_eq'',
  rw iso.symm_hom,
  rw iso.symm_hom,
  simp only [category.assoc],
  erw iso.hom_inv_id,
  rw category.comp_id,
  refl,
end

#exit

lemma inhomog_coh_iso :
  A.inhomog.homology n ≅ ((Ext k (Rep k G) n).obj
    (opposite.op $ Rep.of representation.trivial)).obj A :=
(homology_obj_iso_of_homotopy_equiv (homotopy_equiv.of_iso (inhomog_iso _)) _) ≪≫
(homological_complex.homological_complex.homology_unop_iso _)
≪≫ (group_cohomology.Ext_iso k G A n).symm
