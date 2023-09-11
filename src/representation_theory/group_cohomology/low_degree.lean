/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import representation_theory.group_cohomology.basic
import representation_theory.invariants

/-!
# The low-degree group cohomology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. The file `RepresentationTheory.GroupCohomology.Basic`
defines the group cohomology of `A : Rep k G` to be the cohomology of the complex
$$0 \to \mathrm{Fun}(G^0, A) \to \mathrm{Fun}(G^1, A) \to \mathrm{Fun}(G^2, A) \to \dots$$
with differential $d^n$ sending $f: G^n \to A$ to the function mapping $(g_0, \dots, g_n)$ to
$$\rho(g_0)(f(g_1, \dots, g_n))
+ \sum_{i = 0}^{n - 1} (-1)^{i + 1}\cdot f(g_0, \dots, g_ig_{i + 1}, \dots, g_n)$$
$$+ (-1)^{n + 1}\cdot f(g_0, \dots, g_{n - 1})$$ (where `ρ` is the representation attached to `A`).
We call this complex `groupCohomology.inhomogeneousCochains A`.

The first few objects of this complex can be expressed more nicely; in this file we show
that the beginning of `inhomogeneousCochains A` is isomorphic to
$$0 \to A \to \mathrm{Fun}(G, A) \to \mathrm{Fun}(G \times G, A)$$
$$ \to \mathrm{Fun}(G \times G \times G, A)$$
We use this identification to build API for cocycles and cohomology in degrees `n = 0, 1, 2`
which is easier to use than the definition for general `n`.

## Main definitions

## Implementation notes

## TODO

*

-/
universes v u
noncomputable theory
open category_theory category_theory.limits

variables {k G : Type u} [comm_ring k] [group G] (A : Rep k G)

namespace group_cohomology
open category_theory category_theory.limits representation

-- to be moved
@[simp] lemma inhomogeneous_cochains.d_def (n : ℕ) :
  (inhomogeneous_cochains A).d n (n + 1) = inhomogeneous_cochains.d n A :=
cochain_complex.of_d _ _ _ _

/-- The 0th object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `A` as a `k`-module. -/
def zero_cochains_iso : (inhomogeneous_cochains A).X 0 ≅ Module.of k A :=
(linear_equiv.fun_unique (fin 0 → G) k A).to_Module_iso

/-- The 1st object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `Fun(G, A)` as a `k`-module. -/
def one_cochains_iso : (inhomogeneous_cochains A).X 1 ≅ Module.of k (G → A) :=
(linear_equiv.fun_congr_left k A (equiv.fun_unique (fin 1) G).symm).to_Module_iso

/-- The 0th differential in the complex of inhomogeneous cochains of `A : Rep k G`, as a
`k`-linear map `A → Fun(G, A)`. It sends `(a, g) ↦ ρ_A(g)(a) - a.` -/
@[simps] def d_zero : A →ₗ[k] (G → A) :=
{ to_fun := λ m g, A.ρ g m - m,
  map_add' := λ x y, funext $ λ g, by simpa only [map_add, add_sub_add_comm],
  map_smul' := λ r x, funext $ λ g, by dsimp; rw [map_smul, smul_sub] }

/-- Let `C(G, A)` denote the complex of inhomogeneous cochains of `A : Rep k G`. This lemma
says `d_zero` gives a simpler expression for the 0th differential: that is, the following
square commutes:
```
  C⁰(G, A) ---d⁰---> C¹(G, A)
  |                    |
  |                    |
  |                    |
  v                    v
  A ---- d_zero ---> Fun(G, A)
```
where the vertical arrows are `zero_cochains_iso` and `one_cochains_iso` respectively.
-/
@[reassoc] lemma comp_d_zero_eq : (zero_cochains_iso A).hom ≫ Module.of_hom (d_zero A)
  = (inhomogeneous_cochains A).d 0 1 ≫ (one_cochains_iso A).hom :=
begin
  ext x y,
  simp only [Module.coe_comp, function.comp_app, inhomogeneous_cochains.d_def,
    inhomogeneous_cochains.d_apply, zero_cochains_iso, one_cochains_iso,
    linear_equiv.to_Module_iso_hom, linear_equiv.coe_coe, linear_equiv.fun_unique_apply,
    function.eval_apply, linear_equiv.fun_congr_left_apply, linear_map.fun_left_apply,
    Module.of_hom, d_zero_apply, fintype.univ_of_subsingleton],

  simp only [fin.coe_fin_one, pow_one, neg_smul,
    one_smul, finset.sum_singleton, sub_eq_add_neg],
  congr,
end

lemma d_zero_ker_eq_invariants : (d_zero A).ker = invariants A.ρ :=
begin
  ext,
  simpa only [linear_map.mem_ker, mem_invariants, ←@sub_eq_zero _ _ _ x, function.funext_iff],
end

/-- The 2nd object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `Fun(G × G, A)`. -/
def two_cochains_iso : (inhomogeneous_cochains A).X 2 ≅ Module.of k (G × G → A) :=
(linear_equiv.fun_congr_left k A $ (pi_fin_two_equiv (λ i, G)).symm).to_Module_iso

/-- The 1st differential in the complex of inhomogeneous cochains of `A : Rep k G`, as a
`k`-linear map `Fun(G, A) → Fun(G × G, A)`. It sends
`(f, (g₁, g₂)) ↦ ρ_A(g₁)(f(g₂)) - f(g₁g₂) + f(g₁).` -/
@[simps] def d_one : (G → A) →ₗ[k] (G × G → A) :=
{ to_fun := λ f g, A.ρ g.1 (f g.2) - f (g.1 * g.2) + f g.1,
  map_add' := λ x y, funext $ λ g, by dsimp; rw [map_add, add_add_add_comm, add_sub_add_comm],
  map_smul' := λ r x, funext $ λ g, by dsimp; rw [map_smul, smul_add, smul_sub], }

/-- Let `C(G, A)` denote the complex of inhomogeneous cochains of `A : Rep k G`. This lemma
says `d_one` gives a simpler expression for the 1st differential: that is, the following
square commutes:
```
  C¹(G, A) ---d¹-----> C²(G, A)
    |                      |
    |                      |
    |                      |
    v                      v
  Fun(G, A) -d_one-> Fun(G × G, A)
```
where the vertical arrows are `one_cochains_iso` and `two_cochains_iso` respectively.
-/
@[reassoc] lemma comp_d_one_eq : (one_cochains_iso A).hom ≫ Module.of_hom (d_one A)
  = (inhomogeneous_cochains A).d 1 2 ≫ (two_cochains_iso A).hom :=
begin
  ext x y,
  simp only [Module.coe_comp, function.comp_app, inhomogeneous_cochains.d_def,
    inhomogeneous_cochains.d_apply, two_cochains_iso, one_cochains_iso,
    linear_equiv.to_Module_iso_hom, linear_equiv.coe_coe, linear_equiv.fun_congr_left_apply,
    linear_map.fun_left_apply, Module.of_hom, d_one_apply],
  simp only [sub_eq_add_neg,
    add_assoc, fin.sum_univ_two, fin.coe_zero, pow_one, neg_smul, one_smul,
    fin.coe_one, neg_one_sq],
  congr,
  all_goals { ext i, rw subsingleton.elim i 0, refl },
end

lemma d_one_comp_d_zero : d_one A ∘ₗ d_zero A = 0 :=
by ext; simpa only [linear_map.coe_comp, function.comp_app, d_one_apply A, d_zero_apply A, map_sub,
  map_mul, linear_map.mul_apply, sub_sub_sub_cancel_left, sub_add_sub_cancel, sub_self]

/-- The 1-cocycles `Z¹(G, A)` of `A : Rep k G`, defined as the kernel of the map
`Fun(G, A) → Fun(G × G, A)` sending `(f, (g₁, g₂)) ↦ ρ_A(g₁)(f(g₂)) - f(g₁g₂) + f(g₁).` -/
def one_cocycles := (d_one A).ker

/-- The 1-coboundaries `B¹(G, A)` of `A : Rep k G`, defined as the image of the map
`A → Fun(G, A)` sending `(a, g) ↦ ρ_A(g)(a) - a.` -/
def one_coboundaries := ((d_zero A).cod_restrict (one_cocycles A) $
λ c, linear_map.ext_iff.1 (d_one_comp_d_zero.{u} A) c).range

variables {A}

lemma mem_one_cocycles_iff (f : G → A) :
  f ∈ one_cocycles A ↔ ∀ g : G × G, A.ρ g.1 (f g.2) - f (g.1 * g.2) + f g.1 = 0 :=
linear_map.mem_ker.trans function.funext_iff

lemma mem_one_cocycles_iff' (f : G → A) :
  f ∈ one_cocycles A ↔ ∀ g : G × G, f (g.1 * g.2) = A.ρ g.1 (f g.2) + f g.1 :=
by simp_rw [mem_one_cocycles_iff, sub_add_eq_add_sub, sub_eq_zero, eq_comm]

lemma one_cocycles_map_one (f : one_cocycles A) : (f : G → A) 1 = 0 :=
begin
  have := (mem_one_cocycles_iff (f : G → A)).1 f.2 (1, 1),
  simpa only [map_one, linear_map.one_apply, mul_one, sub_self, zero_add],
end

lemma one_cocycles_map_inv (f : one_cocycles A) (g : G) :
  A.ρ g ((f : G → A) g⁻¹) = -(f : G → A) g :=
begin
  rw [←add_eq_zero_iff_eq_neg, ←one_cocycles_map_one f, ←mul_inv_self g,
    (mem_one_cocycles_iff' (f : G → A)).1 f.2 (g, g⁻¹)],
end

lemma mem_one_coboundaries_of_mem_range (f : G → A) (h : f ∈ (d_zero A).range) :
  (⟨f, by rcases h with ⟨x, rfl⟩; exact linear_map.ext_iff.1
    (d_one_comp_d_zero.{u} A) x⟩ : one_cocycles A) ∈ one_coboundaries A :=
by rcases h with ⟨x, rfl⟩; exact ⟨x, rfl⟩

lemma mem_range_of_mem_one_coboundaries (f : one_coboundaries A) :
  (f : G → A) ∈ (d_zero A).range :=
by rcases f with ⟨f, x, rfl⟩; exact ⟨x, rfl⟩

variables (A)

lemma one_coboundaries_of_trivial_eq (H : ∀ g x, A.ρ g x = x) :
  one_coboundaries A = ⊥ :=
begin
  rw eq_bot_iff,
  rintros x ⟨y, rfl⟩,
  ext,
  show A.ρ x y - y = 0,
  rw [H, sub_self],
end

-- using predicate rather than Rep.of 1 because wanna coerce Z¹(G, A) to Fun(G, A).
/- When `A : Rep k G` is a trivial representation of `G`, `Z¹(G, A)` is isomorphic to the
group homs `G → A`. -/
def one_cocycles_of_trivial_equiv (H : ∀ g x, A.ρ g x = x) :
  one_cocycles A ≃ₗ[k] (additive G →+ A) :=
{ to_fun := λ f,
  { to_fun := (f : G → A),
    map_zero' :=
    begin
      have : A.ρ 1 ((f : G → A) 1) - (f : G → A) (1 * 1) + (f : G → A) 1 = 0 :=
        (mem_one_cocycles_iff (f : G → A)).1 f.2 (1, 1),
      simpa only [H, mul_one, sub_self, zero_add, (mem_one_cocycles_iff (f : G → A)).1 f.2 (1, 1)],
    end,
    map_add' := λ x y,
    begin
      have : (f : G → A) (x * y) = A.ρ x ((f : G → A) y) + (f : G → A) x :=
        (mem_one_cocycles_iff' (f : G → A)).1 f.2 (x, y),
      simpa only [H, add_comm ((f : G → A) x)],
    end },
  map_add' := λ x y, rfl,
  map_smul' := λ r x, rfl,
  inv_fun := λ f,
  { val := f,
    property := (mem_one_cocycles_iff' f).2 (λ g, by simpa only [H, ←map_add, add_comm (f g.2)]) },
  left_inv := λ f, by ext; refl,
  right_inv := λ f, by ext; refl }

/-- The 3rd object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `Fun(G × G × G, A)`. -/
def three_cochains_iso : (inhomogeneous_cochains A).X 3 ≅ Module.of k (G × G × G → A) :=
(linear_equiv.fun_congr_left k A $ ((equiv.pi_fin_succ 2 G).trans
  ((equiv.refl G).prod_congr (pi_fin_two_equiv (λ i, G)))).symm).to_Module_iso

/-- The 2nd differential in the complex of inhomogeneous cochains of `A : Rep k G`, as a
`k`-linear map `Fun(G × G, A) → Fun(G × G × G, A)`. It sends
`(f, (g₁, g₂, g₃)) ↦ ρ_A(g₁)(f(g₂, g₃)) - f(g₁g₂, g₃) + f(g₁, g₂g₃) - f(g₁, g₂).` -/
@[simps] def d_two : (G × G → A) →ₗ[k] (G × G × G → A) :=
{ to_fun := λ f g, A.ρ g.1 (f (g.2.1, g.2.2)) - f (g.1 * g.2.1, g.2.2)
    + f (g.1, g.2.1 * g.2.2) - f (g.1, g.2.1),
  map_add' := λ x y, funext $ λ g, by dsimp; rw [map_add, add_sub_add_comm (A.ρ _ _),
    add_sub_assoc, add_sub_add_comm, add_add_add_comm, add_sub_assoc, add_sub_assoc],
  map_smul' := λ r x, funext $ λ g, by dsimp; simp only [map_smul, smul_add, smul_sub] }

/-- Let `C(G, A)` denote the complex of inhomogeneous cochains of `A : Rep k G`. This lemma
says `d_two` gives a simpler expression for the 2nd differential: that is, the following
square commutes:
```
      C²(G, A) ------d²-----> C³(G, A)
        |                         |
        |                         |
        |                         |
        v                         v
  Fun(G × G, A) --d_two--> Fun(G × G × G, A)
```
where the vertical arrows are `two_cochains_iso` and `three_cochains_iso` respectively.
-/
@[reassoc] lemma comp_d_two_eq : (two_cochains_iso A).hom ≫ Module.of_hom (d_two A)
  = (inhomogeneous_cochains A).d 2 3 ≫ (three_cochains_iso A).hom :=
begin
  ext x y,
  simp only [Module.coe_comp, function.comp_app, inhomogeneous_cochains.d_def,
    inhomogeneous_cochains.d_apply, two_cochains_iso, three_cochains_iso,
    linear_equiv.to_Module_iso_inv, linear_equiv.fun_congr_left_symm,
    linear_equiv.to_Module_iso_hom, linear_equiv.coe_coe, linear_equiv.fun_congr_left_apply,
    linear_map.fun_left_apply, Module.of_hom, d_two_apply,
    pi_fin_two_equiv_symm_apply, fin.coe_zero],
  simp only [sub_eq_add_neg, fin.sum_univ_three, pow_one, neg_smul, one_smul, fin.coe_one, neg_one_sq, fin.coe_two,
  pow_succ _ 2, mul_one, add_assoc, equiv.symm_trans_apply,
  equiv.prod_congr_symm, equiv.refl_symm, equiv.prod_congr_apply, equiv.coe_refl, pi_fin_two_equiv_symm_apply, prod_map,
  id.def, equiv.pi_fin_succ_symm_apply, fin.cons_zero, fin.cons_succ, fin.coe_zero, add_right_inj],
  congr; ext i; fin_cases i; refl,
end

lemma d_two_comp_d_one : d_two A ∘ₗ d_one A = 0 :=
show Module.of_hom (d_one A) ≫ Module.of_hom (d_two A) = _,
by simp only [(iso.eq_inv_comp _).2 (comp_d_two_eq A), (iso.eq_inv_comp _).2 (comp_d_one_eq A),
  category.assoc, iso.hom_inv_id_assoc, homological_complex.d_comp_d_assoc, zero_comp, comp_zero]

/-- The 2-cocycles `Z²(G, A)` of `A : Rep k G`, defined as the kernel of the map
`Fun(G × G, A) → Fun(G × G × G, A)` sending
`(f, (g₁, g₂, g₃)) ↦ ρ_A(g₁)(f(g₂, g₃)) - f(g₁g₂, g₃) + f(g₁, g₂g₃) - f(g₁, g₂).` -/
def two_cocycles := (d_two A).ker
/-- The 2-coboundaries `B²(G, A)` of `A : Rep k G`, defined as the image of the map
`Fun(G, A) → Fun(G × G, A)` sending `(f, (g₁, g₂)) ↦ ρ_A(g₁)(f(g₂)) - f(g₁g₂) + f(g₁).` -/
def two_coboundaries := ((d_one A).cod_restrict (two_cocycles A) $
λ c, linear_map.ext_iff.1 (d_two_comp_d_one.{u} A) c).range

def H2 := two_cocycles A ⧸ two_coboundaries A

lemma mem_two_cocycles_iff (f : G × G → A) :
  f ∈ two_cocycles A ↔ ∀ g : G × G × G, A.ρ g.1 (f (g.2.1, g.2.2)) - f (g.1 * g.2.1, g.2.2)
    + f (g.1, g.2.1 * g.2.2) - f (g.1, g.2.1) = 0 :=
linear_map.mem_ker.trans function.funext_iff

lemma mem_two_cocycles_iff' (f : G × G → A) :
  f ∈ two_cocycles A ↔ ∀ g : G × G × G, f (g.1 * g.2.1, g.2.2) + f (g.1, g.2.1)
    = A.ρ g.1 (f (g.2.1, g.2.2)) + f (g.1, g.2.1 * g.2.2) :=
by simp_rw [mem_two_cocycles_iff, sub_eq_zero, sub_add_eq_add_sub, sub_eq_iff_eq_add,
  eq_comm, add_comm (f (prod.fst _, _))]

lemma two_cocycles_snd {k G : Type u} [comm_ring k] [group G]
  {A : Rep k G} (g : G) (f : two_cocycles A) :
  (f : G × G → A) (1, g) = (f : G × G → A) (1, 1) :=
begin
  have := ((mem_two_cocycles_iff' A f).1 f.2 (1, (1, g))).symm,
  simpa only [map_one, linear_map.one_apply, one_mul, add_right_inj, this],
end

lemma two_cocycles_fst {k G : Type u} [comm_ring k] [group G]
  {A : Rep k G} (g : G) (f : two_cocycles A) :
  (f : G × G → A) (g, 1) = A.ρ g ((f : G × G → A) (1, 1)) :=
begin
  have := (mem_two_cocycles_iff' A f).1 f.2 (g, (1, 1)),
  simpa only [mul_one, add_left_inj, this],
end

lemma mem_two_coboundaries_of_mem_range (f : G × G → A) (h : f ∈ (d_one A).range) :
  (⟨f, by rcases h with ⟨x, rfl⟩; exact linear_map.ext_iff.1
    (d_two_comp_d_one.{u} A) x⟩ : two_cocycles A) ∈ two_coboundaries A :=
by rcases h with ⟨x, rfl⟩; exact ⟨x, rfl⟩

lemma mem_range_of_mem_two_coboundaries (f : two_coboundaries A) :
  (f : G × G → A) ∈ (d_one A).range :=
by rcases f with ⟨f, x, rfl⟩; exact ⟨x, rfl⟩

end group_cohomology
