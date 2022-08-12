/-
Copyright (c) 2021 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import representation_theory.group_cohomology_resolution
import algebra.category.Module.projective
import category_theory.preadditive.projective_resolution
import algebra.module.ulift
import algebra.category.Group.abelian
import data.fin_simplicial_complex
import algebra.homology.exact
import algebra.homology.augment
import representation_theory.Rep
import representation_theory.cohomology.lemmas

/-! Showing `... → k[G²] → k[G]` is a projective resolution of the trivial `k[G]`-module `k`. -/

universes v u
variables (k : Type u) [comm_ring k] [nontrivial k] (G : Type u) [group G]

noncomputable theory
open_locale classical

namespace Rep

variables {G}

/-- Helper function; sends `g ∈ Gⁱ, n ∈ k` to `∑ (-1)ᵏ • (g₁, ..., ĝₖ, ..., gⱼ)`. -/
def d_aux {i j : ℕ} (hj : i = j + 1) (g : fin i → G) : (fin j → G) →₀ k :=
@finsupp.map_domain (fin i) _ _ _ (λ l, g ∘ fin.delta hj l)
  ((finsupp.linear_equiv_fun_on_fintype k k _).symm (λ (l : fin i), (-1 : k) ^ (l : ℕ)))

lemma d_aux_eq {i j : ℕ} (hj : i = j + 1) (g : fin i → G) :
  d_aux k hj g = (finset.range i).sum (λ p : ℕ, finsupp.single (g ∘ fin.delta hj p) ((-1 : k) ^ p)) :=
begin
  unfold d_aux finsupp.map_domain finsupp.sum,
  refine finset.sum_bij (λ a ha, (a : ℕ)) (λ a ha, finset.mem_range.2 a.2)
    (λ a ha, rfl) (λ a b ha hb hab, subtype.ext hab)
    (λ b H, ⟨⟨b, finset.mem_range.1 H⟩, finsupp.mem_support_iff.2 (is_unit.ne_zero
      (is_unit.pow _ (is_unit.neg is_unit_one))), rfl⟩),
end

open category_theory
variables {k G} {i j : ℕ} (hj : i = j + 1) (g : G) (a : fin i → G)

lemma d_aux_comm {i j : ℕ} (hj : i = j + 1) (g : G) (a : fin i → G) (r : k) :
  finsupp.lift _ k (fin i → G) (d_aux k hj) (representation.of_mul_action k G (fin i → G) g
    (finsupp.single a r)) =
  representation.of_mul_action k G (fin j → G) g (finsupp.lift _ k (fin i → G) (d_aux k hj)
    (finsupp.single a r)) :=
begin
  dsimp,
  simp only [representation.of_mul_action_def, finsupp.lmap_domain_apply,
    finsupp.map_domain_single, finsupp.sum_single_index],
  simp only [finsupp.map_domain_smul, finsupp.map_domain_single,
    finsupp.sum_single_index, zero_smul, d_aux, ←finsupp.map_domain_comp],
  refl,
end

variables (k G)

def d_hom {i j : ℕ} (hj : i = j + 1) : ((fin i → G) →₀ k) →ₗ[k] ((fin j → G) →₀ k) :=
finsupp.lift _ k (fin i → G) (d_aux k hj)

/-- Sends `g ∈ Gⁱ` to `∑ (-1)ᵏ • (g₁, ..., ĝₖ, ..., gⱼ)`. -/
def d {i j : ℕ} (hj : i = j + 1) :
  of_mul_action k G (fin i → G) ⟶ of_mul_action k G (fin j → G) :=
{ comm' := λ g, linear_map.to_add_monoid_hom_injective
    (finsupp.add_hom_ext (λ a r, d_aux_comm hj g a r)),
  hom := d_hom k G hj }

variables {k G}

@[simp] lemma d_def {i j : ℕ} (hj : i = j + 1) : ⇑(d k G hj).hom = ⇑(d_hom k G hj) := rfl

lemma d_hom_single {i j : ℕ} (hj : i = j + 1) (c : fin i → G) (n : k) :
  d_hom k G hj (finsupp.single c n) = (finset.range i).sum (λ p : ℕ, finsupp.single
    (c ∘ fin.delta hj p) ((-1 : k) ^ p * n)):=
begin
  simp only [mul_comm _ n],
  simp only [←smul_eq_mul, ←finsupp.smul_single, ←finset.smul_sum],
  erw finsupp.lift_apply,
  rw [finsupp.sum_single_index, d_aux_eq],
  rw zero_smul,
end

lemma d_hom_of {i j : ℕ} (hj : i = j + 1) (c : fin i → G) :
  d_hom k G hj (finsupp.single c 1) = d_aux k hj c :=
begin
  erw finsupp.lift_apply,
  rw [finsupp.sum_single_index, one_smul],
  rw zero_smul,
end

lemma ughh {i : ℕ} {N : Type*} [add_comm_monoid N] {f : ℕ → k → N} :
  ((finsupp.linear_equiv_fun_on_fintype k k _).symm (λ (l : fin i), (-1 : k) ^ (l : ℕ))).sum (λ x, f (x : ℕ)) =
  (finset.range i).sum (λ p, f p ((-1 : k) ^ p)) :=
finset.sum_bij (λ a ha, (a : ℕ)) (λ a ha, finset.mem_range.2 a.2) (λ a ha, rfl)
    (λ a b ha hb hab, subtype.ext $ hab) (λ b H, ⟨⟨b, finset.mem_range.1 H⟩,
     finsupp.mem_support_iff.2 (is_unit.ne_zero
      (is_unit.pow _ (is_unit.neg is_unit_one))), rfl⟩)

theorem d_hom_squared_of {i j l : ℕ} (hj : i = j + 1) (hl : j = l + 1) (c : fin i → G) (r : k) :
  (d_hom k G hl (d_hom k G hj $ finsupp.single c r)) = 0 :=
begin
  rw [←finsupp.smul_single_one, linear_map.map_smul, linear_map.map_smul],
  convert smul_zero _,
  rw [d_hom_of, d_aux_eq, linear_map.map_sum],
  simp only [d_hom_single, ←finset.sum_product'],
  refine finset.sum_involution (λ pq h, invo pq) _ _ _ _,
  { intros pq hpq,
    unfold invo,
    rw [add_eq_zero_iff_eq_neg, ←finsupp.single_neg, function.comp.assoc],
    conv_rhs {rw function.comp.assoc},
    split_ifs,
    all_goals {congr' 2},
    any_goals {ext, dsimp},
    { rw fin.delta_comm_apply _ _ h },
    { simp [mul_comm, pow_succ], },
    { cases pq with p q,
      cases p, { push_neg at h, cases h },
      simp only [nat.pred_succ, pow_succ],
      push_neg at h,
      have hqp : q ≤ p := nat.lt_succ_iff.mp h,
      rw fin.delta_comm_apply.symm hl hj hqp,
      simp only [nat.succ_sub_succ_eq_sub, tsub_zero] },
    { rw ←neg_one_mul ((-1 : k) ^ _ * _),
      conv_rhs { congr, rw ←pow_one (-1 : k) },
      simp only [←mul_assoc, ←pow_add],
      congr' 1,
      omega }},
  { rintros ⟨p, q⟩ h _ hfalse,
    rw prod.ext_iff at hfalse,
    rcases hfalse with ⟨h1, h2⟩,
    dsimp at *,
    unfold invo at *,
    split_ifs at *,
    { subst h1,revert h_1,
      apply nat.not_succ_le_self },
    { exact h_1 (h1 ▸ le_refl _) } },
  { rintro ⟨p, q⟩ hpqrange,
    unfold invo,
    simp only [hl, hj, finset.mem_product, finset.mem_range] at ⊢ hpqrange,
    split_ifs,
      { exact ⟨nat.add_lt_add_right hpqrange.2 _, lt_of_le_of_lt h hpqrange.2⟩ },
      { cases p,
        { exact false.elim (h (zero_le _))},
        { exact ⟨lt_trans hpqrange.2 (nat.lt_succ_self _), (add_lt_add_iff_right 1).1 hpqrange.1⟩}}},
  { intros,
    exact invo_invo _ }
end

theorem d_hom_squared {i j l : ℕ} (hj : i = j + 1) (hl : j = l + 1) (c : of_mul_action k G (fin i → G)) :
  (d_hom k G hl (d_hom k G hj c)) = 0 :=
begin
  refine @monoid_algebra.induction_on k (fin i → G) _ _ _ c (λ g, _) _ _,
  { exact d_hom_squared_of hj hl g (1 : k) },
  { intros a b ha hb,
    simp only [linear_map.map_add, ha, hb, zero_add] },
  { intros r a ha,
    simp only [linear_map.map_smul_of_tower, ha, smul_zero] }
end

variables (k G)

instance {k : Type u} [comm_ring k] {G : Type u} [group G]
  {V : Type u} [add_comm_group V] [module k V] [nontrivial V] (ρ : representation k G V) :
  nontrivial (Rep.of ρ) := by assumption

instance {k : Type u} [comm_ring k] {G : Type u} [group G]
  {V : Type u} [add_comm_group V] [module k V] [nontrivial V] (ρ : representation k G V) :
  nontrivial (Rep.of ρ).V := by assumption

abbreviation Trivial : Rep k G :=
Rep.of representation.trivial

open category_theory

/-- The chain complex `... → k[Gⁿ] → ... → k[G]`. -/
def std_resn_complex : chain_complex (Rep k G) ℕ :=
chain_complex.of (λ n, of_mul_action k G (fin (n + 1) → G))
(λ n, d k G rfl) (λ n, Action.hom.ext _ _ $ linear_map.ext $ d_hom_squared rfl rfl)

variables {k G}

lemma coeff_sum_comm (g : G) (x : monoid_algebra k G) :
  finsupp.total G k k (λ g : G, 1) (representation.of_mul_action k G G g x) =
    finsupp.total G k k (λ g : G, 1) x :=
begin
  refine (finset.sum_bij (λ a ha, g * a) (λ a ha, finsupp.mem_support_iff.2 $ _) (λ a ha, _)
    (λ a b ha hb hab, mul_left_cancel hab) (λ b H, _)).symm,
  { simpa only [representation.of_mul_action_apply,
      smul_eq_mul, inv_mul_cancel_left, ←finsupp.mem_support_iff], },
  { simp only [representation.of_mul_action_apply, one_mul, smul_eq_mul, mul_one,
      inv_mul_cancel_left] },
  { rw [finsupp.mem_support_iff, representation.of_mul_action_apply] at H,
    exact ⟨g⁻¹ * b, ⟨finsupp.mem_support_iff.2 H, (mul_inv_cancel_left _ _).symm⟩⟩ }
end

variables (k G)

/-- The hom `k[G] → k` sending `∑ nᵢgᵢ ↦ ∑ nᵢ`. -/
def coeff_sum : Rep.of_mul_action k G G ⟶ Trivial k G :=
{ hom := finsupp.total G (Trivial k G) k (λ g, (1 : k)),
  comm' := λ g, by ext; exact coeff_sum_comm g (finsupp.single a 1) }

variables {k G}

lemma coeff_sum_single {x : G} {n : k} : (coeff_sum k G).hom (finsupp.single x n) = n :=
begin
  erw finsupp.total_single,
  exact mul_one _,
end

lemma range_coeff_sum_eq_top :
  (coeff_sum k G).hom.range = ⊤ :=
linear_map.range_eq_top.2 $
begin
  intro n,
  use finsupp.single 1 n,
  erw finsupp.total_single,
  exact mul_one _,
end

lemma dom_one_iso_comm (g : G) (x : monoid_algebra k (fin 1 → G)) :
  @finsupp.dom_lcongr k k _ _ _ _ _ (fin.dom_one_equiv G)
    ((representation.of_mul_action k G (fin 1 → G)) g x)
  = representation.of_mul_action k G G g (@finsupp.dom_lcongr k k _ _ _ _ _
    (fin.dom_one_equiv G) x) :=
begin
  refine x.induction_on _ _ _,
  { intro x,
    simp only [monoid_algebra.of_apply, finsupp.dom_lcongr_apply,
      finsupp.dom_congr_apply, finsupp.dom_lcongr_single, representation.of_mul_action_single,
      finsupp.equiv_map_domain_single],
    refl },
  { intros w z hw hz,
    simp only [map_add, mul_add, hw, hz] },
  { intros r f hf,
    simp only [map_smul, hf, mul_smul_comm] }
end

variables (k G)

def dom_one_iso : Rep.of_mul_action k G (fin 1 → G) ≅ Rep.of_mul_action k G G :=
Action.mk_iso (@finsupp.dom_lcongr k k _ _ _ _ _ (fin.dom_one_equiv G)).to_Module_iso $
  λ g, linear_map.ext (λ x, dom_one_iso_comm _ _)

variables {k G}

lemma dom_one_iso_map_one (r : k) :
  (dom_one_iso k G).hom.hom (finsupp.single 1 r) = (finsupp.single 1 r) :=
begin
  ext,
  simp [dom_one_iso, fin.dom_one_equiv],
end

lemma coeff_sum_dom_one_iso_apply {g : of_mul_action k G (fin 1 → G)} :
  (coeff_sum k G).hom ((dom_one_iso k G).hom.hom g) = finsupp.total (fin 1 → G)
    (Trivial k G) k (λ g, (1 : k)) g :=
begin
  refine add_monoid_hom.ext_iff.1 (@finsupp.add_hom_ext (fin 1 → G) k _ _ _
    (((coeff_sum k G).hom.comp (dom_one_iso k G).hom.hom).to_add_monoid_hom) (finsupp.total (fin 1 → G)
    ↥(Trivial k G) k (λ (g : fin 1 → G), (1 : k))).to_add_monoid_hom (λ x y, _)) g,
  simp [dom_one_iso, coeff_sum_single],
end

lemma coeff_sum_d_hom (x : (fin 2 → G) →₀ k) :
  (coeff_sum k G).hom ((dom_one_iso k G).hom.hom $ d_hom k G rfl x) = 0 :=
begin
  refine linear_map.ext_iff.1 (@finsupp.lhom_ext _ _ _ _ _ _ _ _ _
  ((coeff_sum k G).hom.comp ((@finsupp.dom_lcongr _ k _ _ _ _ _  $ fin.dom_one_equiv G).to_linear_map.comp
    (d k G rfl).hom)) 0 _) x,
  intros g b,
  dsimp,
  rw [d_hom_single, ←finsupp.dom_congr_apply, add_equiv.map_sum, linear_map.map_sum],
  simp only [mul_one, finsupp.dom_congr_apply, finsupp.equiv_map_domain_single, coeff_sum_single],
  rw [finset.range_add_one, finset.sum_insert (@finset.not_mem_range_self 1)],
  simp only [pow_one, neg_mul, finset.range_one, finset.sum_singleton, pow_zero, add_left_neg],
end

variables (k G)

instance fdsf : (@to_Module_monoid_algebra k G _ _).additive :=
{ map_add' := λ X Y f g, by refl }

instance fdsfdf : (@equivalence_Module_monoid_algebra k G _ _).functor.additive :=
{ map_add' := λ X Y f g, by refl }

instance fdffsf : (@of_Module_monoid_algebra k G _ _).additive :=
{ map_add' := λ X Y f g, by refl }

def std_resn_Module_complex : chain_complex (Module (monoid_algebra k G)) ℕ :=
(equivalence_Module_monoid_algebra.functor.map_homological_complex _).obj (std_resn_complex k G)

/-- The hom `... → ℤ[G²] → ℤ[G]` → `... → 0 → ℤ → 0 → ...` which is `coeff_sum` at 0
  and 0 everywhere else. -/
def std_resn_π : std_resn_complex k G ⟶ ((chain_complex.single₀
  (Rep k G)).obj (Trivial k G)) :=
{ f := λ n, nat.rec_on n ((dom_one_iso k G).hom.comp (coeff_sum k G)) (λ n hn, 0),
  comm' := λ i j hij, by
  { induction j with j hj,
    { ext1,
      refine linear_map.ext (λ x, _),
      cases hij,
      dsimp,
      exact (coeff_sum_d_hom x).symm },
    { simp only [chain_complex.single₀_obj_X_d, category_theory.limits.comp_zero] }}}

variables {k G}

lemma delta_zero_cons (g : Rep.of_mul_action k G (fin 1 → G)) :
  finsupp.map_domain (λ v : fin 2 → G, v ∘ fin.delta rfl 0) (finsupp.map_domain (fin.cons 1) g) = g :=
begin
  rw ←finsupp.map_domain_comp,
  convert finsupp.map_domain_id,
  ext v i,
  rw subsingleton.elim i 0,
  dsimp,
  convert @fin.cons_succ 1 (λ i, G) (1 : G) v 0,
end

lemma delta_one_cons (g : Rep.of_mul_action k G (fin 1 → G)) :
  finsupp.map_domain (λ v : fin 2 → G, v ∘ fin.delta rfl 1) (finsupp.map_domain (fin.cons 1) g) =
    finsupp.single 1 ((coeff_sum k G).hom ((dom_one_iso k G).hom.hom g)) :=
begin
  rw [←finsupp.map_domain_comp, finsupp.eq_single_iff],
  split,
  { intros i hi,
    obtain ⟨j, hjg, rfl⟩ := finset.mem_image.1 (finsupp.map_domain_support hi),
    rw finset.mem_singleton,
    ext k,
    rw subsingleton.elim k 0,
    dsimp,
    convert @fin.cons_zero 1 (λ i, G) (1 : G) _ },
  { rw coeff_sum_dom_one_iso_apply,
    unfold finsupp.map_domain,
    dsimp,
    rw finsupp.total_apply,
    simp only [finsupp.sum_apply, cons_delta_two, finsupp.single_eq_same],
    unfold finsupp.sum,
    congr,
    ext,
    dsimp,
    rw mul_one,
    convert finsupp.single_eq_same,
    }
end

variables (n : ℕ)

lemma d_hom_two_apply (x : (fin 2 → G) →₀ k) :
  d_hom k G (show 2 = 1 + 1, from rfl) x =
  finsupp.map_domain (λ v : fin 2 → G, v ∘ fin.delta rfl 0) x
    - finsupp.map_domain (λ v : fin 2 → G, v ∘ fin.delta rfl 1) x :=
begin
  dsimp [d, d_hom, finsupp.sum],
  simp only [d_aux_eq, finset.range_add_one],
  unfold finsupp.map_domain,
  rw ←finsupp.sum_sub,
  congr,
  ext1 v, ext1 m,
  rw [finset.sum_insert, finset.sum_insert (@finset.not_mem_range_self 0)],
  { simp [sub_eq_neg_add] },
  { rw [←finset.range_add_one, zero_add],
    exact finset.not_mem_range_self }
end

lemma d_hom_cons (x : (fin 1 → G) →₀ k) (hx : x ∈ ((coeff_sum k G).hom.comp
    (dom_one_iso k G).hom.hom).ker) :
  d_hom k G (show 2 = 1 + 1, from rfl) (finsupp.map_domain (fin.cons 1) x) = x :=
begin
  cases x with x hx,
  rw [d_hom_two_apply, delta_zero_cons, delta_one_cons],
  convert sub_zero _,
  rw finsupp.single_eq_zero,
  erw linear_map.mem_ker.1 hx,
end

open category_theory category_theory.limits

lemma std_resn_Module_exact₀ : category_theory.exact
  (equivalence_Module_monoid_algebra.functor.map (d k G (show 2 = 1 + 1, from rfl)))
 (equivalence_Module_monoid_algebra.functor.map $
   (dom_one_iso k G).hom ≫ (coeff_sum k G)) :=
(Module.exact_iff _ _).2 $ by ext; exact ⟨by rintros ⟨y, rfl⟩; exact coeff_sum_d_hom _,
  λ hx, ⟨finsupp.map_domain (fin.cons 1) x, d_hom_cons x hx⟩⟩

instance jkdgfds : (category_theory.forget₂ (Rep k G) (Module k)).additive :=
{ map_add' := λ x y f g, rfl }

variables (k G)

/-- The exact sequence of `k`-modules `... → k[G²] → k[G] → k → 0`.
  We need this to show 1 is null-homotopic as a map of `k`-module complexes. -/
def std_resn_aug_forget₂ :=
((category_theory.forget₂ _ (Module.{u} k)).map_homological_complex _).obj
  ((std_resn_complex k G).augment ((dom_one_iso k G).hom ≫ (coeff_sum k G))
  (by ext; exact coeff_sum_d_hom _))

lemma std_resn_aug_forget₂_d_succ : (std_resn_aug_forget₂ k G).d (n + 2) (n + 1) = d_hom k G rfl :=
show (category_theory.forget₂ _ _).map (((chain_complex.of _ _ _).augment _ _).d _ _) = _,
by rw [chain_complex.augment_d_succ_succ, chain_complex.of_d]; refl

/-/-- Basically the map `k → k[G]` sending `n ↦ n • 1` -/
def std_resn_homotopy_aux : k →ₗ[k] (fin 1 → G) →₀ k :=
finsupp.lsingle 1-/

/-- Homotopy constructor for when you have a family `fₙ : Cₙ → Dₙ₊₁` (as opposed
  to `Cᵢ → Dⱼ` with `j = i + 1`).-/
def homotopy.of {V : Type u} [category_theory.category V]
  [category_theory.preadditive V] {C D : chain_complex V ℕ} (f g : C ⟶ D)
(hom : Π n, C.X n ⟶ D.X (n + 1))
(comm0 : f.f 0 = hom 0 ≫ D.d 1 0 + g.f 0)
(comm : ∀ i, f.f (i + 1) = C.d (i + 1) i ≫ hom i + hom (i + 1)
    ≫ D.d (i + 2) (i + 1) + g.f (i + 1) . obviously') :
  homotopy f g :=
{ hom := λ i j, if h : i + 1 = j then
    hom i ≫ category_theory.eq_to_hom (congr_arg D.X h)
  else
    0,
  zero' := λ i j w, by rwa dif_neg,
  comm := λ i,
  begin
    induction i with i hi,
    { simpa using comm0 },
    { simpa using comm i},
  end }

variables {k G}

lemma yeah (x : fin 1 → G) : finsupp.single x (1 : k) = finsupp.single 1
  ((coeff_sum k G).hom ((dom_one_iso k G).hom.hom (finsupp.single x 1)))
  + d_hom k G rfl (finsupp.map_domain (fin.cons 1) (finsupp.single x 1)) :=
by rw [d_hom_two_apply, delta_zero_cons, delta_one_cons, add_sub_cancel'_right]

lemma cons_d (g : G) (x : fin (n + 1) → G) :
  finsupp.map_domain (@fin.cons _ (λ i , G) g) (d_hom k G rfl (finsupp.single x 1))
  + d_hom k G rfl (finsupp.single (fin.cons g x) 1)
  = finsupp.single x 1 :=
begin
  conv_lhs {rw add_comm},
  rw [d_hom_of, d_aux_eq, finset.range_succ', finset.sum_insert, add_assoc],
  { convert add_zero _,
    { rw [finset.sum_image (λ i hi j hj hij, nat.succ_injective hij), d_hom_of,
        d_aux_eq, finsupp.map_domain_finset_sum, ←finset.sum_add_distrib],
      refine finset.sum_eq_zero _,
      intros i hi,
      dsimp,
      simp only [finsupp.map_domain_single, pow_succ, neg_one_mul,
        finsupp.single_neg, neg_add_eq_sub, sub_eq_zero],
      congr,
      exact (fin.cons_delta_succ x g i).symm },
    { rw fin.cons_delta_zero },
    { rw pow_zero }},
  { intro h,
    obtain ⟨i, hi, hi'⟩ := finset.mem_image.1 h,
    exact nat.succ_ne_zero _ hi' }
end


lemma fucksake (g : G) (x : fin (n + 1) → G) :
  finsupp.map_domain (@fin.cons _ (λ i , G) g) (d_hom k G rfl (finsupp.single x 1))
  + d_hom k G rfl (finsupp.map_domain (@fin.cons _ (λ i, G) g) (finsupp.single x 1))
  = finsupp.single x 1 :=
begin
  rw finsupp.map_domain_single,
  rw cons_d,
end

/-#check homotopy.mk_inductive (𝟙 (std_resn_aug_forget₂ k G))
  (finsupp.lsingle 1)
  (begin
    ext,
    show (1 : k) = (coeff_sum k G).hom ((dom_one_iso k G).hom.hom (finsupp.single 1 1)),
    rw [dom_one_iso_map_one, coeff_sum_single],
  end) (finsupp.lmap_domain k k (@fin.cons 1 (λ i, G) 1))
  (begin
    ext1 x, ext1,
    exact yeah _ _
  end) (λ n f, ⟨finsupp.lmap_domain k k (@fin.cons _ (λ i, G) 1),
  begin
    ext,
    dsimp,

  end⟩)-/

variables (k G)

def std_resn_homotopy_aux :
  (std_resn_aug_forget₂ k G).X n →ₗ[k] (std_resn_aug_forget₂ k G).X (n + 1) :=
nat.rec_on n (finsupp.lsingle 1) (λ m fm, finsupp.lmap_domain k k (@fin.cons _ (λ i, G) 1))

lemma std_resn_homotopy_cond :
  @linear_map.id k ((std_resn_aug_forget₂ k G).X (n + 1)) _ _ _ =
  (std_resn_homotopy_aux k G n).comp ((std_resn_aug_forget₂ k G).d _ _)
  + ((std_resn_aug_forget₂ k G).d _ _).comp (std_resn_homotopy_aux k G (n + 1)) + 0 :=
begin
  rw [add_zero, std_resn_aug_forget₂_d_succ],
  ext1, ext1,
  induction n with n hn,
  { dsimp [std_resn_homotopy_aux, std_resn_complex],
    rw [d_hom_two_apply, delta_zero_cons, delta_one_cons],
    exact (add_sub_cancel'_right _ _).symm },
  { dsimp [std_resn_homotopy_aux],
    rw [std_resn_aug_forget₂_d_succ, finsupp.map_domain_single],
    exact (cons_d _ (1 : G) _).symm, }
end

/-- The identity chain map on `... ℤ[G²] → ℤ[G] → ℤ` (as a complex of `AddCommGroup`s)
  is homotopic to 0. -/
def std_resn_homotopy :
  homotopy (𝟙 (std_resn_aug_forget₂ k G)) 0 :=
homotopy.of (𝟙 (std_resn_aug_forget₂ k G)) _ (std_resn_homotopy_aux k G)
(by { ext,
  show (1 : k) = (coeff_sum k G).hom ((dom_one_iso k G).hom.hom (finsupp.single 1 1)) + 0,
  rw [dom_one_iso_map_one, coeff_sum_single, add_zero] }) (std_resn_homotopy_cond k G)

open_locale zero_object

/-- A complex on which 1 is nullhomotopic is homotopy equivalent to the zero complex. -/
def homotopy_equiv_of_null_homotopic_id {V : Type u}
  [category_theory.category V] [category_theory.preadditive V]
  [has_zero_object V] {ι : Type*}
  (c : complex_shape ι) (C : homological_complex V c)
  (H : homotopy (𝟙 C) 0) : homotopy_equiv C 0 :=
⟨0, 0, (homotopy.of_eq zero_comp).trans H.symm, homotopy.of_eq (has_zero_object.to_zero_ext _ _)⟩
/-
def exact_of_null_homotopic_id' {V : Type u}
  [category_theory.category V] [category_theory.preadditive V]
  [has_zero_object V] [has_images V] [has_kernels V] [has_cokernels V]
  [has_image_maps V] [has_equalizers V] {ι : Type*}
  (c : complex_shape ι) (C : homological_complex V c)
  (h : homotopy (𝟙 C) 0) (i j k : ι) (hij : c.rel i j) (hjk : c.rel j k) :
  category_theory.exact (C.d i j) (C.d j k) :=
(category_theory.preadditive.exact_iff_homology_zero _ _).2 $
⟨homological_complex.d_comp_d _ _ _ _, ⟨_⟩⟩-/
/-- A chain complex (of `AddCommGroup`s) on which the identity is null-homotopic is exact. -/
def exact_of_null_homotopic_id {V : Type u}
  [category_theory.category V] [category_theory.preadditive V]
  [has_zero_object V] [has_images V] [has_kernels V] [has_cokernels V]
  [has_image_maps V] [has_equalizers V] {ι : Type*}
  (c : complex_shape ι) (C : homological_complex V c)
  (h : homotopy (𝟙 C) 0) (j : ι) :
  category_theory.exact (C.d_to j) (C.d_from j) :=
(category_theory.preadditive.exact_iff_homology_zero (C.d_to j) (C.d_from j)).2 $
⟨homological_complex.d_to_comp_d_from _ _, ⟨
  (homology_obj_iso_of_homotopy_equiv (homotopy_equiv_of_null_homotopic_id c C h) _).trans
  (homology_functor _ c j).map_zero_object⟩⟩

lemma exact_to_from_iff {V : Type u} [category_theory.category V] [has_images V]
  [has_zero_morphisms V] [has_zero_object V] [has_equalizers V] (C : chain_complex V ℕ) {j : ℕ} :
  category_theory.exact (C.d_to (j + 1)) (C.d_from (j + 1))
    ↔ category_theory.exact (C.d (j + 2) (j + 1)) (C.d (j + 1) j) :=
by rw [C.d_to_eq rfl, C.d_from_eq rfl, category_theory.exact_iso_comp,
  category_theory.exact_comp_iso]
#check category_theory.functor.exact_of_exact_map

lemma ugh (n : ℕ) : category_theory.exact ((std_resn_complex k G).d (n + 2) (n + 1))
  ((std_resn_complex k G).d (n + 1) n) :=
(category_theory.forget₂ (Rep k G) (Module.{u} k)).exact_of_exact_map $
(exact_to_from_iff _).1 (exact_of_null_homotopic_id _ _ (std_resn_homotopy k G) (n + 2))

lemma exact_d_to_d_from (n : ℕ) : category_theory.exact ((std_resn_complex k G).d_to (n + 1))
  ((std_resn_complex k G).d_from (n + 1)) :=
(category_theory.forget₂ (Rep k G) (Module.{u} k)).exact_of_exact_map $
begin
  rw [(std_resn_complex k G).d_to_eq rfl, (std_resn_complex k G).d_from_eq rfl,
     category_theory.functor.map_comp, category_theory.functor.map_comp,
     category_theory.exact_iso_comp, category_theory.exact_comp_iso],
  exact (exact_to_from_iff _).1 (exact_of_null_homotopic_id _ _ (std_resn_homotopy k G) (n + 2)),
end
#check (Rep.equivalence_Module_monoid_algebra.functor.map_homological_complex _).obj (std_resn_complex k G)

variables (k G)

def std_Module_resn := (Rep.equivalence_Module_monoid_algebra.functor.map_homological_complex _).obj
  (std_resn_complex k G)

lemma exact_blah (n : ℕ) : category_theory.exact ((std_Module_resn k G).d_to (n + 1))
  ((std_Module_resn k G).d_from (n + 1)) :=
begin
  simp only [(std_Module_resn k G).d_to_eq rfl, (std_Module_resn k G).d_from_eq rfl,
    category_theory.exact_comp_iso, category_theory.exact_iso_comp],
  refine (category_theory.abelian.is_equivalence.exact_iff _ _ _).2 _,
  rw ←exact_to_from_iff,
  exact exact_d_to_d_from _ _ _,
end

abbreviation Trivial_Module := Rep.equivalence_Module_monoid_algebra.functor.obj (Trivial k G)
--(category_theory.abelian.is_equivalence.exact_iff _ _ _).2 (exact_d_to_d_from _ _ _)

#check dom_one_iso
/-{ f := λ n, nat.rec_on n ((dom_one_iso k G).hom.comp (coeff_sum k G)) (λ n hn, 0),
  comm' := λ i j hij, by
  { induction j with j hj,
    { ext1,
      refine linear_map.ext (λ x, _),
      cases hij,
      dsimp,
      exact (coeff_sum_d_hom x).symm },
    { simp only [chain_complex.single₀_obj_X_d, category_theory.limits.comp_zero] }}}-/

#check Trivial
#check (⇑(Rep.equivalence_Module_monoid_algebra.functor.map
  ((dom_one_iso k G).hom ≫ (coeff_sum k G))) : ((fin 1 → G) →₀ k) → k)

#check (⇑((dom_one_iso k G).hom.hom ≫ (coeff_sum k G).hom) : ((fin 1 → G) →₀ k) → k)

example : ((Rep.equivalence_Module_monoid_algebra.functor.map
  ((dom_one_iso k G).hom ≫ (coeff_sum k G))) : ((fin 1 → G) →₀ k) → k) =
  (((dom_one_iso k G).hom.hom ≫ (coeff_sum k G).hom) : ((fin 1 → G) →₀ k) → k) := rfl
  --(representation.of_mul_action k G (fin 1 → G)).as_module → (@representation.trivial k G _ _).as_module)

lemma hmmm : (Rep.equivalence_Module_monoid_algebra.functor.map
  ((dom_one_iso k G).hom ≫ (coeff_sum k G))).range = ⊤ :=
linear_map.range_eq_top.2 $
  show function.surjective ((dom_one_iso k G).hom.hom ≫ (coeff_sum k G).hom),
  from linear_map.range_eq_top.1 ((linear_equiv.range_comp _ (coeff_sum k G).hom).trans (@range_coeff_sum_eq_top k _ _ G _))
/-- The resolution `... → ℤ[G²] → ℤ[G]` of the trivial `ℤ[G]`-module `ℤ` as
a projective resolution. -/
def std_resn : category_theory.ProjectiveResolution (Trivial_Module k G) :=
{ complex := std_Module_resn k G,
  π := (Rep.equivalence_Module_monoid_algebra.functor.map_homological_complex _).map
  (std_resn_π k G) ≫ ((chain_complex.single₀_map_homological_complex
Rep.equivalence_Module_monoid_algebra.functor).hom.app (Trivial k G)),
  projective := λ n, @Module.projective_of_free.{u u u} (monoid_algebra k G) _
    (Module.of _ (representation.of_mul_action k G (fin (n + 1) → G)).as_module) (fin n → G)
    (group_cohomology.resolution.of_mul_action_basis k G n),
  exact₀ := std_resn_Module_exact₀,
  exact := λ n, (exact_to_from_iff _).1 $ exact_blah _ _ _,
  epi := (Module.epi_iff_range_eq_top _).2 $ linear_map.range_eq_top.2 $
    show function.surjective ((dom_one_iso k G).hom.hom ≫ (coeff_sum k G).hom), from
      linear_map.range_eq_top.1 ((linear_equiv.range_comp _ (coeff_sum k G).hom).trans
      (@range_coeff_sum_eq_top k _ _ G _)) }
#where
end Rep
