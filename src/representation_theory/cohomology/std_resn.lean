/-
Copyright (c) 2021 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import representation_theory.cohomology.group_ring
import algebra.category.Module.projective
import category_theory.preadditive.projective_resolution
import algebra.module.ulift
import algebra.category.Group.abelian
import data.fin_simplicial_complex
import algebra.homology.augment
import representation_theory.cohomology.lemmas

/-! Showing `... → ℤ[G²] → ℤ[G]` is a projective resolution of the trivial `ℤ[G]`-module `ℤ`. -/

universes v u
variables (R : Type u) [comm_ring R] (G : Type u) [group G]

noncomputable theory
open_locale classical

namespace Rep

/-- Helper function; sends `g ∈ Gⁱ, n ∈ ℤ` to `∑ (-1)ᵏn • (g₁, ..., ĝₖ, ..., gⱼ)`. -/
def d_aux {i j : ℕ} (hj : i = j + 1) (g : fin i → G) : monoid_algebra R (fin j → G) :=
(finset.range i).sum (λ p, finsupp.single (λ k, g $ fin.delta hj p k) ((-1 : R) ^ p))

open category_theory
variables {i j : ℕ} (hj : i = j + 1) (g : G) (a : fin i → G)

lemma d_comm {i j : ℕ} (hj : i = j + 1) (g : G) (a : fin i → G) :
  finsupp.lift _ R (fin i → G) (d_aux R G hj) (representation.of_mul_action R G (fin i → G) g (finsupp.single a 1)) =
    representation.of_mul_action R G (fin j → G) g (finsupp.lift _ R (fin i → G) (d_aux R G hj) (finsupp.single a 1)) :=
begin
  dsimp,
  simp only [finsupp.map_domain_single, finsupp.sum_single_index, zero_smul, one_smul],
  unfold finsupp.map_domain,
  unfold d_aux finsupp.sum,
  refine finset.sum_bij _ _ _ _ _,
  use (λ p hp k, a $ fin.delta hj p k),
  intros p hp,
  rw finsupp.mem_support_iff,
  intro h0,
  sorry,sorry, sorry, sorry
end

/-- Sends `g ∈ Gⁱ` to `∑ (-1)ᵏ • (g₁, ..., ĝₖ, ..., gⱼ)`. -/
def d {i j : ℕ} (hj : i = j + 1) :
  of_mul_action R G (fin i → G) ⟶ of_mul_action R G (fin j → G) :=
{ comm' := λ g,
  begin
    sorry
  end,
  hom := finsupp.lift _ R (fin i → G) (d_aux R G hj) }

variables {G}

lemma d_single {i j : ℕ} (hj : i = j + 1) (c : fin i → G) (n : R) :
  (d R G hj).hom (finsupp.single c n) = (finset.range i).sum (λ p, finsupp.single
    (λ k, c $ fin.delta hj p k) ((-1 : R) ^ p * n)) :=
begin
  erw finsupp.lift_apply,
  rw finsupp.sum_single_index,
  unfold d_aux,
  rw finset.smul_sum,
  simp only [finsupp.smul_single, smul_eq_mul, mul_comm],
  rw zero_smul
end

lemma d_of {i j : ℕ} (hj : i = j + 1) (c : fin i → G) :
  (d R G hj).hom (monoid_algebra.of _ _  c) = (finset.range i).sum (λ p, finsupp.single
    (λ k, c $ fin.delta hj p k) ((-1 : R) ^ p)) :=
begin
  simp only [monoid_algebra.of_apply, d_single, mul_one],
end

theorem d_squared_of {i j k : ℕ} (hj : i = j + 1) (hk : j = k + 1) (c : fin i → G) :
  ((d R G hk).hom ((d R G hj).hom $ monoid_algebra.of _ _ c)) = 0 :=
begin
  ext g,
  simp only [d_of, linear_map.map_sum, linear_map.map_smul_of_tower,
    finset.smul_sum, ←finset.sum_product'],
  congr,
  sorry
  /-refine finset.sum_involution (λ pq h, invo pq) _ _ _ _,
  { intros pq hpq,
    unfold invo,
    split_ifs,
    { simp [fin.delta_comm_apply hk hj h, mul_comm, pow_succ] },
    { cases pq with p q,
      cases p, { push_neg at h, cases h },
      simp only [nat.pred_succ, pow_succ],
      push_neg at h,
      have hqp : q ≤ p := nat.lt_succ_iff.mp h,
      simp_rw fin.delta_comm_apply.symm hk hj hqp,
      simp [mul_comm ((-1 : ℤ) ^ p)]}},
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
    simp only [hk, hj, finset.mem_product, finset.mem_range] at ⊢ hpqrange,
    split_ifs,
      { exact ⟨nat.add_lt_add_right hpqrange.2 _, lt_of_le_of_lt h hpqrange.2⟩ },
      { cases p,
        { exact false.elim (h (zero_le _))},
        { exact ⟨lt_trans hpqrange.2 (nat.lt_succ_self _), (add_lt_add_iff_right 1).1 hpqrange.1⟩}}},
  { intros,
    exact invo_invo _ },-/
end

theorem d_squared {i j k : ℕ} (hj : i = j + 1) (hk : j = k + 1) (c : of_mul_action R G (fin i → G)) :
  ((d R G hk).hom ((d R G hj).hom c)) = 0 :=
begin
  refine @monoid_algebra.induction_on R (fin i → G) _ _ _ c _ _ _,
  { exact d_squared_of R hj hk },
  { intros a b ha hb,
    simp only [linear_map.map_add, ha, hb, zero_add] },
  { intros r a ha,
    simp only [linear_map.map_smul_of_tower, ha, smul_zero] }
end

variables (G)
/-- Don't want a `ℤ[G]`-module instance on `(ulift) ℤ` I don't think, so here's `ulift ℤ`
  with the trivial action as a `Module`. -/

abbreviation Trivial : Rep R G :=
Rep.of representation.trivial

open category_theory

/-- The chain complex `... → ℤ[Gⁿ] → ... → ℤ[G]`. -/
def std_resn_complex : chain_complex (Rep R G) ℕ :=
chain_complex.of (λ n, of_mul_action R G (fin (n + 1) → G))
(λ n, d R G rfl) (λ n, by sorry)

/-- The hom `ℤ[G] → ℤ` sending `∑ nᵢgᵢ ↦ ∑ nᵢ`. -/
def coeff_sum : of_mul_action R G G ⟶ Trivial R G :=
{ comm' := λ g, by
  { refine linear_map.ext (λ x, _),
    dunfold of_mul_action Trivial,
    simp only [Rep.of_ρ, category_theory.comp_apply],
    rw [representation.of_mul_action_apply, finsupp.lmap_domain_apply],
    sorry,
     },
 hom := (finsupp.total G (Trivial R G) R (λ g, (1 : R)))}

variables {G}

lemma coeff_sum_single {x : G} {n : R} : (coeff_sum R G).hom (finsupp.single x n) = n :=
begin
  erw finsupp.total_single,
  exact mul_one _,
end

lemma range_coeff_sum_eq_top :
  (coeff_sum R G).hom.range = ⊤ :=
linear_map.range_eq_top.2 $
begin
  intro n,
  use finsupp.single 1 n,
  erw finsupp.total_single,
  exact mul_one _,
end

lemma coeff_sum_dom_one_equiv_apply {g : of_mul_action R G (fin 1 → G)} :
  (coeff_sum R G).hom (finsupp.dom_congr (fin.dom_one_equiv G) g) = finsupp.total (fin 1 → G)
    (Trivial R G) R (λ g, (1 : R)) g :=
begin
  refine add_monoid_hom.ext_iff.1 (@finsupp.add_hom_ext (fin 1 → G) R _ _ _
    ((coeff_sum R G).hom.to_add_monoid_hom.comp (@finsupp.dom_congr _ _ R _
    (fin.dom_one_equiv G)).to_add_monoid_hom) (finsupp.total (fin 1 → G)
    ↥(Trivial R G) R (λ (g : fin 1 → G), (1 : R))).to_add_monoid_hom _) g,
  intros x y,
  dsimp,
  simp only [coeff_sum_single, finsupp.equiv_map_domain_single, finsupp.total_single,
    algebra.id.smul_eq_mul, mul_one],
end

lemma coeff_sum_d {x : of_mul_action R G (fin 2 → G)} :
  (coeff_sum R G).hom (finsupp.dom_congr (fin.dom_one_equiv G) $ (d R G rfl).hom x) = 0 :=
begin
  refine linear_map.ext_iff.1 (@finsupp.lhom_ext _ _ _ _ _ _ _ _ _
  ((coeff_sum R G).hom.comp ((@finsupp.dom_lcongr _ R _ _ _ _ _  $ fin.dom_one_equiv G).to_linear_map.comp
    (d R G rfl).hom)) 0 _) x,
  intros g b,
  dsimp,
  rw [d_single, ←finsupp.dom_congr_apply, add_equiv.map_sum, linear_map.map_sum],
  simp only [mul_one, finsupp.dom_congr_apply, finsupp.equiv_map_domain_single, coeff_sum_single],
  rw [finset.range_add_one, finset.sum_insert (@finset.not_mem_range_self 1)],
  simp only [pow_one, neg_mul, finset.range_one, finset.sum_singleton, pow_zero, add_left_neg],
end

variables (G)

/-- The hom `... → ℤ[G²] → ℤ[G]` → `... → 0 → ℤ → 0 → ...` which is `coeff_sum` at 0
  and 0 everywhere else. -/
def std_resn_π : std_resn_complex R G ⟶ ((chain_complex.single₀
  (Rep R G)).obj (Trivial R G)) :=
{ f := λ n, nat.rec_on n ((coeff_sum R G).hom.comp (@finsupp.dom_lcongr _ R _ _ _ _ _ $ fin.dom_one_equiv G).to_linear_map)
    (λ n hn, 0),
  comm' := λ i j hij, by
  { induction j with j hj,
    { ext1,
      cases hij,
      exact coeff_sum_d.symm },
    { simp only [limits.comp_zero, chain_complex.single₀_obj_X_d] at * }}}

variables {G}

lemma delta_zero_cons (g : group_ring (fin 1 → G)) :
  finsupp.map_domain (λ v : fin 2 → G, v ∘ fin.delta rfl 0) (cons 1 1 g) = g :=
begin
  show finsupp.map_domain _ (finsupp.map_domain _ _) = _,
  dsimp,
  rw ←finsupp.map_domain_comp,
  convert finsupp.map_domain_id,
  ext v i,
  rw subsingleton.elim i 0,
  dsimp,
  convert @fin.cons_succ 1 (λ i, G) (1 : G) v 0,
end

lemma delta_one_cons (g : group_ring (fin 1 → G)) :
  finsupp.map_domain (λ v : fin 2 → G, v ∘ fin.delta rfl 1) (cons 1 1 g) =
    finsupp.single 1 (coeff_sum G (dom_one_equiv G g)).down :=
begin
  show finsupp.map_domain _ (finsupp.map_domain _ _) = _,
  dsimp,
  rw [←finsupp.map_domain_comp, finsupp.eq_single_iff],
  split,
  { intros i hi,
    obtain ⟨j, hjg, rfl⟩ := finset.mem_image.1 (finsupp.map_domain_support hi),
    rw finset.mem_singleton,
    ext k,
    rw subsingleton.elim k 0,
    dsimp,
    convert @fin.cons_zero 1 (λ i, G) (1 : G) _ },
  { rw coeff_sum_dom_one_equiv_apply,
    unfold finsupp.map_domain,
    dsimp,
    rw finsupp.total_apply,
    simp only [finsupp.sum_apply, cons_delta_two, finsupp.single_eq_same],
    unfold finsupp.sum,
    rw ulift.sum_down,
    congr,
    ext,
    dsimp,
    rw mul_one,
    convert finsupp.single_eq_same,
    }
end

variables (n : ℕ)

lemma d_two_apply (x : group_ring (fin 2 → G)) :
  d G (show 2 = 1 + 1, from rfl) x =
  finsupp.map_domain (λ v : fin 2 → G, v ∘ fin.delta rfl 0) x
    - finsupp.map_domain (λ v : fin 2 → G, v ∘ fin.delta rfl 1) x :=
begin
  unfold d,
  simp only [finsupp.lift_add_hom_apply, d_aux, add_monoid_hom.to_fun_eq_coe,
    linear_map.coe_mk, add_monoid_hom.coe_mk],
  simp only [finset.range_add_one],
  unfold finsupp.map_domain,
  rw ←finsupp.sum_sub,
  congr,
  ext1 v, ext1 m,
  rw [finset.sum_insert, finset.sum_insert (@finset.not_mem_range_self 0)],
  { simp only [neg_one_mul, finsupp.single_neg, add_zero, one_mul,
     finset.sum_empty, finset.range_zero, pow_one, pow_zero, neg_add_eq_sub], },
  { rw [←finset.range_add_one, zero_add],
    exact finset.not_mem_range_self }
end

lemma d_cons (x : group_ring (fin 1 → G)) (hx : x ∈ ((coeff_sum G).comp
    (dom_one_equiv G).to_linear_map).ker) :
  d G (show 2 = 1 + 1, from rfl) (cons 1 1 x) = x :=
begin
  cases x with x hx,
  rw [d_two_apply, delta_zero_cons, delta_one_cons],
  convert sub_zero _,
  rw finsupp.single_eq_zero,
  erw linear_map.mem_ker.1 hx,
  exact ulift.zero_down,
end

lemma std_resn_exact₀ : exact (Module.as_hom $ d G (show 2 = 1 + 1, from rfl))
  (Module.as_hom ((coeff_sum G).comp (dom_one_equiv G).to_linear_map)) :=
(Module.exact_iff _ _).2 $
begin
  ext,
  split,
  { rintros ⟨y, rfl⟩,
    exact coeff_sum_d },
  { intro hx,
    use cons 1 1 x,
    exact d_cons x hx }
end

-- idk where this is .
instance : functor.additive (forget₂ (Module (group_ring G)) AddCommGroup) :=
{ map_add' := λ x y f g, rfl }

variables (G)

/-- The exact sequence of `AddCommGroup`s `... → ℤ[G²] → ℤ[G] → ℤ → 0`.
  We need this to show 1 is null-homotopic as a map of `AddCommGroup` complexes. -/
abbreviation std_resn_aug_AddCommGroup :=
((forget₂ _ AddCommGroup).map_homological_complex _).obj ((std_resn_complex G).augment
((coeff_sum G).comp (dom_one_equiv G).to_linear_map) (by ext1; exact coeff_sum_d))

/-- Basically the map `ℤ → ℤ[G]` sending `n ↦ n • 1` -/
def std_resn_homotopy_aux : trivial G →+ group_ring (fin 1 → G) :=
{ to_fun := λ n, finsupp.single 1 n.down,
  map_zero' := finsupp.single_zero,
  map_add' := λ x y, finsupp.single_add }

/-- Homotopy constructor for when you have a family `fₙ : Cₙ → Dₙ₊₁` (as opposed
  to `Cᵢ → Dⱼ` with `j = i + 1`).-/
def homotopy.of {C D : chain_complex AddCommGroup ℕ} (f g : C ⟶ D)
(hom : Π n, C.X n ⟶ D.X (n + 1))
(comm0 : f.f 0 = hom 0 ≫ D.d 1 0 + g.f 0)
(comm : ∀ i, f.f (i + 1) = C.d (i + 1) i ≫ hom i + hom (i + 1)
    ≫ D.d (i + 2) (i + 1) + g.f (i + 1) . obviously') :
  homotopy f g :=
{ hom := λ i j, if h : i + 1 = j then
    hom i ≫ eq_to_hom (congr_arg D.X h)
  else
    0,
  zero' := λ i j w, by rwa dif_neg,
  comm := λ i,
  begin
    induction i with i hi,
    { simpa using comm0 },
    { simpa using comm i},
  end }

variables {G}

lemma cons_d (g : G) (x : fin (n + 1) → G) :
  d G rfl (of (fin (n + 2) → G) $ fin.cons g x) + cons n g (d G rfl (of _ x)) = of _ x :=
begin
  show _ + finsupp.map_domain.add_monoid_hom _ _ = _,
  rw [d_of, finset.range_succ', finset.sum_insert, add_assoc],
  { convert add_zero _,
    { rw [finset.sum_image (λ i hi j hj hij, nat.succ_injective hij), d_of,
        add_monoid_hom.map_sum, ←finset.sum_add_distrib],
      refine finset.sum_eq_zero _,
      intros i hi,
      dsimp,
      simp only [finsupp.map_domain_single, pow_succ, neg_one_mul,
        finsupp.single_neg, neg_add_eq_sub, sub_eq_zero],
      congr,
      exact (fin.cons_delta_succ x g i).symm },
    { rw [pow_zero, of_apply],
      congr,
      ext i,
      rw [fin.delta_zero_succ, fin.cons_succ] }},
  { intro h,
    obtain ⟨i, hi, hi'⟩ := finset.mem_image.1 h,
    exact nat.succ_ne_zero _ hi' }
end

variables (G)

/-- The identity chain map on `... ℤ[G²] → ℤ[G] → ℤ` (as a complex of `AddCommGroup`s)
  is homotopic to 0. -/
def std_resn_homotopy :
  homotopy (𝟙 (std_resn_aug_AddCommGroup G)) 0 :=
homotopy.of _ _ (λ n, nat.rec_on n (std_resn_homotopy_aux G) (λ m fm, cons _ (1 : G)))
(by { ext1,
  show x = coeff_sum G (dom_one_equiv G (finsupp.single _ _)) + 0,
  rw [coeff_sum_dom_one_equiv_apply, finsupp.total_single, add_zero],
  ext,
  simp only [mul_one, algebra.id.smul_eq_mul, ulift.smul_down']}) $
λ i, nat.rec_on i
(begin
  ext1,
  refine x.induction_on _ _ _,
  { intro x,
    dsimp,
    show finsupp.single _ _ = finsupp.single _ (coeff_sum G (dom_one_equiv _ _)).down
      + d _ _ _ + _,
    simp only [coeff_sum_dom_one_equiv_apply, finsupp.total_single, add_zero],
    simp only [cons, finsupp.map_domain.add_monoid_hom_apply, one_zsmul,
      finsupp.map_domain_single, eq_to_hom_refl, Module.id_apply],
    erw d_two_apply,
    simp only [cons_delta_two, add_sub_cancel'_right, finsupp.map_domain_single],
    sorry
    /-congr,
    ext j,
    rw [function.comp_app, @subsingleton.elim (fin 1) _ j 0],
    convert (@fin.cons_succ 1 (λ i, G) 1 x _).symm -/
    },
  { intros f g hf hg,
    rw [add_monoid_hom.map_add, add_monoid_hom.map_add, hf, hg]},
  { intros r f hf,
    rw [add_monoid_hom.map_zsmul, add_monoid_hom.map_zsmul, hf]}
end)
(λ j hj,
begin
  clear hj,
  ext1,
  refine x.induction_on _ _ _,
  { intro y,
    dsimp at *,
    show finsupp.single _ _ = cons _ (1 : G) _ + _ + 0,
    simp only [add_zero, comp_apply, finsupp.map_domain.add_monoid_hom_apply,
      chain_complex.augment_d_succ_succ, finsupp.map_domain_single],
    simp only [add_comm],
    dunfold std_resn_complex,
    rw [chain_complex.of_d, chain_complex.of_d],
    unfold cons,
    dsimp,
    rw finsupp.map_domain_single,
    exact (cons_d _ _ _).symm },
  { intros f g hf hg,
    rw [add_monoid_hom.map_add, add_monoid_hom.map_add, hf, hg]},
  { intros r f hf,
    rw [add_monoid_hom.map_zsmul, add_monoid_hom.map_zsmul, hf] }
end)

/- Don't know what assumptions on the category I need to make this compile & be
  maximally general so it will just be AddCommGroup for now -/
/-- A complex on which 1 is nullhomotopic is homotopy equivalent to the zero complex. -/
def homotopy_equiv_of_null_homotopic {ι : Type*}
  (c : complex_shape ι) (C : homological_complex AddCommGroup c)
  (H : homotopy (𝟙 C) 0) : homotopy_equiv C 0 :=
⟨0, 0, H.symm, homotopy.of_eq (limits.has_zero_object.to_zero_ext _ _)⟩

/-- A chain complex (of `AddCommGroup`s) on which the identity is null-homotopic is exact. -/
def exact_of_homotopy_zero {ι : Type*}
  {c : complex_shape ι} {C : homological_complex AddCommGroup c}
  (h : homotopy (𝟙 C) 0) (j : ι) :
  exact (C.d_to j) (C.d_from j) :=
(preadditive.exact_iff_homology_zero (C.d_to j) (C.d_from j)).2 $
⟨homological_complex.d_to_comp_d_from _ _, ⟨
  (homology_obj_iso_of_homotopy_equiv (homotopy_equiv_of_null_homotopic c C h) _).trans
  (functor.map_zero_object (homology_functor AddCommGroup c j))⟩⟩

lemma exact_to_from_iff {V : Type*} [category V] [limits.has_images V] [limits.has_zero_morphisms V]
  [limits.has_zero_object V] [limits.has_equalizers V] {C : chain_complex V ℕ} {j : ℕ} :
  exact (C.d_to (j + 1)) (C.d_from (j + 1)) ↔ exact (C.d (j + 2) (j + 1)) (C.d (j + 1) j) :=
begin
  rw [C.d_to_eq rfl, C.d_from_eq rfl, exact_iso_comp, exact_comp_iso],
end

instance exact_of_AddCommGroup_exact {R : Type*} [ring R]
  {A B C : Module R} (f : A ⟶ B) (g : B ⟶ C)
  [h : exact ((forget₂ (Module R) AddCommGroup).map f)
    ((forget₂ (Module R) AddCommGroup).map g)] :
  exact f g :=
sorry

instance exact_d_to_d_from (n : ℕ) : exact ((std_resn_complex G).d_to (n + 1))
  ((std_resn_complex G).d_from (n + 1)) :=
@group_ring.exact_of_AddCommGroup_exact _ _ _ _ _ _ _ $
begin
  rw [(std_resn_complex G).d_to_eq rfl, (std_resn_complex G).d_from_eq rfl,
     category_theory.functor.map_comp, category_theory.functor.map_comp,
     exact_iso_comp, exact_comp_iso],
  exact exact_to_from_iff.1 (exact_of_homotopy_zero (std_resn_homotopy G) (n + 2)),
end

/-- The resolution `... → ℤ[G²] → ℤ[G]` of the trivial `ℤ[G]`-module `ℤ` as
a projective resolution. -/
def std_resn : ProjectiveResolution (trivial G) :=
{ complex := std_resn_complex G,
  π := std_resn_π G,
  projective := λ n, @Module.projective_of_free.{u u u} _ _
    (Module.of (group_ring G) (group_ring (fin (n + 1) → G))) _ (basis.{u} G n),
  exact₀ := group_ring.std_resn_exact₀,
  exact := λ n, exact_to_from_iff.1 $ group_ring.exact_d_to_d_from G _,
  epi := (Module.epi_iff_range_eq_top _).2 $ ((dom_one_equiv G).range_comp _).trans
    range_coeff_sum_eq_top }


end group_ring
