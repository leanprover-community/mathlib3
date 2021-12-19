import algebra.group.cohomology.group_ring
import algebra.category.Module.projective
import category_theory.preadditive.projective_resolution
import algebra.module.ulift
import algebra.category.Group.abelian
import algebra.homology.augment
universes u
variables (G : Type u) [group G]
open group_cohomology.cochain_succ
noncomputable theory
open_locale classical

lemma finset.range_succ' (n : ℕ) :
  finset.range (n + 1) = insert 0 ((finset.range n).image nat.succ) :=
begin
  ext i,
  simp only [finset.mem_insert, finset.mem_image, finset.mem_range],
  cases i with i,
  { exact ⟨λ h, or.inl rfl, λ h, nat.succ_pos _⟩ },
  { exact ⟨λ h, or.inr ⟨i, ⟨finset.mem_range.2 $ nat.succ_lt_succ_iff.1 h, rfl⟩⟩,
    λ h, by obtain ⟨j, ⟨hj, hj'⟩⟩ := h.resolve_left (nat.succ_ne_zero i);
      rwa [←hj', nat.succ_lt_succ_iff, ←finset.mem_range]⟩}
end

@[to_additive] lemma ulift.prod_down {α : Type*} {β : Type*} [comm_monoid β] {s : finset α}
  (f : α → ulift β) :
  (s.prod f).down = s.prod (ulift.down ∘ f) :=
begin
  refine s.induction_on _ _,
  { simp only [ulift.one_down, finset.prod_empty] },
  { intros a t ht hf,
    simp only [*, finset.prod_insert, not_false_iff, ulift.mul_down] at *}
end

--not sure where to find this
def fin.dom_one_equiv (α : Type u) : (fin 1 → α) ≃ α :=
{ to_fun := λ f, f 0,
  inv_fun := λ x i, x,
  left_inv := λ x, funext $ λ i, by rw subsingleton.elim i 0,
  right_inv := λ x, rfl }

lemma fin.injective_cons_zero {n : ℕ} {α : fin (n + 1) → Type*} (x : α 0) :
  function.injective (fin.cons x) :=
begin
  intros y z hyz,
  ext i,
  have := congr_fun hyz i.succ,
  dsimp at this,
  rwa [fin.cons_succ, fin.cons_succ] at this,
end

lemma fin.injective_cons_tail {n : ℕ} {α : fin (n + 1) → Type*} (x : Π i : fin n, α i.succ) :
  function.injective (λ y : α 0, fin.cons y x) :=
begin
  intros y z hyz,
  replace hyz := congr_fun hyz 0,
  dsimp at hyz,
  rwa [fin.cons_zero, fin.cons_zero] at hyz,
end

lemma fin.delta_zero_succ (n : ℕ) :
  fin.delta rfl 0 = @fin.succ n :=
begin
  ext,
  unfold fin.delta,
  dsimp,
  rw [if_neg (nat.not_lt_zero _), fin.coe_succ],
end

lemma fin.cons_delta_zero {n : ℕ} {α : Type*} (x : fin n → α) (y : α) :
  (fin.cons y x ∘ fin.delta rfl 0 : fin n → α) = x :=
begin
  ext j,
  rw [function.comp_app, fin.delta_zero_succ, fin.cons_succ],
end

lemma fin.cons_delta_succ {n : ℕ} {α : Type*} (x : fin (n + 1) → α) (y : α) (m : ℕ) :
  (fin.cons y x ∘ fin.delta rfl m.succ : fin (n + 1) → α) =
  fin.cons y (x ∘ fin.delta rfl m : fin n → α) :=
begin
  ext j,
  refine fin.cases _ (λ i, _) j,
  { rw [fin.cons_zero, function.comp_app],
    convert fin.cons_zero _ _,
    refl },
  { rw fin.cons_succ,
    dsimp,
    convert fin.cons_succ _ _ _,
    { refl },
    { ext,
      unfold fin.delta,
      dsimp,
      by_cases h : (i : ℕ) < m,
      { rw [if_pos h, if_pos, fin.coe_succ],
        { rw fin.coe_succ,
          exact nat.succ_lt_succ_iff.2 h }},
      { rw [if_neg h, if_neg, fin.coe_succ],
        exact (λ hn, h $ by rw fin.coe_succ at hn; exact nat.succ_lt_succ_iff.1 hn) }}},
end

@[to_additive] lemma mul_equiv.map_pow {M N : Type*} [monoid M] [monoid N]
  (f : M ≃* N) (x : M) (n : ℕ) :
  f (x ^ n) = (f x) ^ n :=
f.to_monoid_hom.map_pow _ _

lemma mul_equiv.map_gpow {M N : Type*} [group M] [group N]
  (f : M ≃* N) (x : M) (n : ℤ) :
  f (x ^ n) = (f x) ^ n :=
f.to_monoid_hom.map_gpow _ _

lemma add_equiv.map_gsmul {M N : Type*} [add_group M] [add_group N]
  (f : M ≃+ N) (x : M) (n : ℤ) :
  f (n • x) = n • f x :=
f.to_add_monoid_hom.map_gsmul _ _

attribute [to_additive add_equiv.map_gsmul] mul_equiv.map_gpow

namespace group_ring

def d_aux {i j : ℕ} (hj : i = j + 1) (c : fin i → G) : ℤ →+ (group_ring (fin j → G)) :=
{ to_fun := λ n, (finset.range i).sum (λ p, finsupp.single
    (λ k, c $ fin.delta hj p k) ((-1 : ℤ) ^ p * n)),
  map_zero' := by simp only [finsupp.single_zero, finset.sum_const_zero, mul_zero],
  map_add' := λ v w, by simp only [mul_add, finsupp.single_add, finset.sum_add_distrib] }

def d_add_hom {i j : ℕ} (hj : i = j + 1) : group_ring (fin i → G) →+ group_ring (fin j → G) :=
finsupp.lift_add_hom (d_aux G hj)

def d {i j : ℕ} (hj : i = j + 1) : group_ring (fin i → G) →ₗ[group_ring G] group_ring (fin j → G) :=
{ map_smul' := λ g x,
  begin
    refine x.induction_on _ _ _,
    { intro x,
      refine g.induction_on _ _ _,
      { intro g,
        dsimp,
        unfold d_aux,
        dsimp,
        erw of_smul_of,
        simp only [finset.smul_sum, mul_one, finsupp.single_zero, smul_eq_mul,
          finset.sum_const_zero, of_apply, pi.smul_apply, mul_zero, finsupp.sum_single_index],
        congr,
        ext1 p,
        simp only [gsmul_single_one, gsmul_single_one],
        rw [smul_algebra_smul_comm, one_smul, of_smul_of],
        congr },
      { intros a b ha hb,
        simp only [add_smul, add_monoid_hom.to_fun_eq_coe, add_monoid_hom.map_add] at ⊢ ha hb,
        rw [ha, hb] },
      { intros r a ha,
        simp only [smul_assoc, add_monoid_hom.to_fun_eq_coe, add_monoid_hom.map_gsmul] at ⊢ ha,
        rw ha }},
    { intros a b ha hb,
      simp only [smul_add, add_monoid_hom.to_fun_eq_coe, add_monoid_hom.map_add] at ⊢ ha hb,
      rw [ha, hb] },
    { intros r a ha,
      simp only [smul_algebra_smul_comm, add_monoid_hom.to_fun_eq_coe,
        add_monoid_hom.map_gsmul] at ⊢ ha,
      rw ha }
  end,
  ..finsupp.lift_add_hom (d_aux G hj) }


lemma d_of {i j : ℕ} (hj : i = j + 1) (c : fin i → G) :
  d G hj (of _ c) = (finset.range i).sum (λ p, finsupp.single
    (λ k, c $ fin.delta hj p k) ((-1 : ℤ) ^ p)) :=
begin
  erw finsupp.lift_add_hom_apply_single,
  show (finset.range i).sum _ = _,
  congr, ext, congr,
  rw mul_one,
end

def invo : ℕ × ℕ → ℕ × ℕ :=
λ j, if j.1 ≤ j.2 then (j.2 + 1, j.1) else (j.2, j.1 - 1)

lemma invo_pos {j : ℕ × ℕ} (h : j.1 ≤ j.2) :
  invo j = (j.2 + 1, j.1) := if_pos h

lemma invo_neg {j : ℕ × ℕ} (h : ¬j.1 ≤ j.2) :
  invo j = (j.2, j.1 - 1) := if_neg h

lemma invo_invo (j : ℕ × ℕ) : invo (invo j) = j :=
begin
  by_cases h : j.1 ≤ j.2,
  { rw [invo_pos h, invo_neg],
    { exact prod.ext rfl rfl },
    { linarith }},
  { rw [invo_neg h, invo_pos],
    { exact prod.ext (nat.sub_add_cancel (by linarith)) rfl },
    { exact (nat.le_pred_of_lt (not_le.1 h)) }},
end

theorem d_squared_of {i j k : ℕ} (hj : i = j + 1) (hk : j = k + 1) (c : fin i → G) :
  (d G hk (d G hj $ of _ c)) = 0 :=
begin
  ext g,
  --show _ = (0 : ℤ),
  simp only [d_of],
  rw linear_map.map_sum,
  simp only [gsmul_single_one, linear_map.map_smul_of_tower, d_of],
  simp_rw finset.smul_sum,
  rw ← finset.sum_product',
  congr,
  refine finset.sum_involution (λ pq h, invo pq) _ _ _ _,
  { intros pq hpq,
    unfold invo,
    split_ifs,
    { simp only [fin.delta_comm_apply hk hj h, mul_comm, pow_succ, mul_one, finsupp.smul_single',
        of_apply, neg_mul_eq_neg_mul_symm, finsupp.single_neg, one_mul, add_right_neg] },
    { -- kill the pred.
      cases pq with p q,
      -- pred 0 can't happen
      cases p, { push_neg at h, cases h },
      -- rewrite now succeeds
      simp [nat.pred_succ, pow_succ],
      push_neg at h,
      have hqp : q ≤ p := nat.lt_succ_iff.mp h,
      have := fin.delta_comm_apply.symm hk hj hqp,
      simp_rw this,
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
    exact invo_invo _ },
end

theorem d_squared {i j k : ℕ} (hj : i = j + 1) (hk : j = k + 1) (c : group_ring (fin i → G)) :
  (d G hk (d G hj c)) = 0 :=
begin
  refine c.induction_on _ _ _,
  { exact d_squared_of G hj hk },
  { intros a b ha hb,
    simp only [linear_map.map_add, ha, hb, zero_add] },
  { intros r a ha,
    simp only [linear_map.map_smul_of_tower, ha, smul_zero] }
end

instance trivial_action : distrib_mul_action G ℤ :=
by refine { smul := λ g n, n, .. }; {intros, refl}

def trivial : Module (group_ring G) :=
{ carrier := (ulift ℤ : Type u),
  is_add_comm_group := ulift.add_comm_group,
  is_module := @ulift.module' _ _ _ _ $ distrib_mul_action.to_module }

open category_theory

def std_resn_complex : chain_complex (Module (group_ring G)) ℕ :=
chain_complex.of (λ n, Module.of (group_ring G) (group_ring (fin (n + 1) → G)))
(λ n, d G rfl) (λ n, by ext1; exact d_squared _ _ _ _)

def coeff_sum : group_ring G →ₗ[group_ring G] trivial G :=
{ map_smul' := λ g x, by
  { dsimp,
    refine x.induction_on _ _ _,
    { intro y,
      refine g.induction_on _ _ _,
      { intro z,
        erw monoid_algebra.single_mul_single,
        simp only [mul_one, one_gsmul, finsupp.total_single, of_apply],
        ext,
        show _ = finsupp.total _ _ _ _ _,
        rw [finsupp.total_single, one_smul],
        refl },
      { intros a b ha hb,
        rw [add_mul, add_smul, linear_map.map_add, ha, hb]},
      { intros r a ha,
        rw [smul_mul_assoc, linear_map.map_smul, ha, smul_assoc] }},
    { intros a b ha hb,
      rw [mul_add, linear_map.map_add, ha, hb, linear_map.map_add, smul_add]},
    { intros r a ha,
      rw [mul_smul_comm, linear_map.map_smul, ha, linear_map.map_smul, smul_algebra_smul_comm]}}
  .. (finsupp.total G (trivial G) ℤ (λ g, ulift.up 1))}

lemma coeff_sum_single {x : G} {n : ℤ} : coeff_sum G (finsupp.single x n) = ulift.up n :=
begin
  erw finsupp.total_single,
  ext,
  exact mul_one _,
end

lemma range_coeff_sum_eq_top :
  (coeff_sum G).range = ⊤ :=
linear_map.range_eq_top.2 $
begin
  intro n,
  use finsupp.single 1 n.down,
  erw finsupp.total_single,
  ext,
  exact mul_one _,
end

def group_ring_one_equiv : group_ring (fin 1 → G) ≃ₗ[group_ring G] group_ring G :=
{ map_smul' := λ x y, by
  { refine x.induction_on _ _ _,
    { dsimp,
      intro g,
      ext,
      rw [smul_def, finsupp.total_single, one_smul],
      simp only [monoid_algebra.single_mul_apply, one_mul, finsupp.equiv_map_domain_apply,
        finsupp.comap_smul_apply],
      congr },
    { intros a b ha hb,
      simp only [add_smul, add_equiv.map_add', ha, hb]},
    { intros r a ha,
      simp only [add_equiv.to_fun_eq_coe, add_equiv.map_gsmul, smul_assoc] at ⊢ ha,
      rw ha }},
  ..finsupp.dom_congr (fin.dom_one_equiv G) }

lemma group_ring_one_equiv_single {g : fin 1 → G} {m : ℤ} :
  group_ring_one_equiv G (finsupp.single g m) = finsupp.single (g 0) m :=
begin
  erw [finsupp.dom_congr_apply, finsupp.equiv_map_domain_single],
  refl,
end

lemma coeff_sum_group_ring_one_equiv_apply {g : group_ring (fin 1 → G)} :
  coeff_sum G (group_ring_one_equiv G g) = finsupp.total (fin 1 → G)
    (trivial G) ℤ (λ g, ulift.up 1) g :=
begin
  refine g.induction_on _ _ _,
  { intros g,
    rw [of_apply, group_ring_one_equiv_single, coeff_sum_single, finsupp.total_single, one_smul] },
  { intros a b ha hb,
    simp only [linear_equiv.map_add, linear_map.map_add, ha, hb], },
  { intros r a ha,
    simp only [←linear_equiv.coe_to_linear_map, linear_map.map_smul_of_tower,
      linear_map.map_smul] at ⊢ ha,
    rw ha }
end

lemma coeff_sum_d {x : group_ring (fin 2 → G)} :
  coeff_sum G (group_ring_one_equiv G $ d G rfl x) = 0 :=
begin
  refine x.induction_on _ _ _,
  { intro g,
    rw [d_of, linear_equiv.map_sum, linear_map.map_sum],
    unfold group_ring_one_equiv,
    dsimp,
    simp only [finsupp.dom_congr_apply, finsupp.equiv_map_domain_single, coeff_sum_single],
    rw [finset.range_add_one, finset.sum_insert (@finset.not_mem_range_self 1)],
    ext,
    simp only [ulift.zero_down, pow_one, add_left_neg, finset.sum_singleton,
        finset.range_one, pow_zero, ulift.add_down] },
  { intros a b ha hb,
    simp only [linear_map.map_add, linear_equiv.map_add, ha, hb, zero_add] },
  { intros r a ha,
    simp only [linear_map.map_smul_of_tower, ←linear_equiv.coe_to_linear_map] at ha ⊢,
    rw [ha, smul_zero] }
end

def std_resn_π : std_resn_complex G ⟶ ((chain_complex.single₀
  (Module (group_ring G))).obj (trivial G)) :=
{ f := λ n, nat.rec_on n ((coeff_sum G).comp (group_ring_one_equiv G).to_linear_map)
    (λ n hn, 0),
  comm' := λ i j hij, by
  { induction j with j hj,
    { ext1,
      cases hij,
      exact (coeff_sum_d _).symm },
    { simp only [limits.comp_zero, chain_complex.single₀_obj_X_d] at * }}}

def cons (n : ℕ) (r : G) : group_ring (fin n → G) →+ group_ring (fin (n + 1) → G) :=
finsupp.map_domain.add_monoid_hom (@fin.cons n (λ i, G) r)

lemma cons_of (g : fin 1 → G) :
  cons G 1 1 (of _ g) = of (fin 2 → G) (fin.cons (1 : G) g) :=
finsupp.map_domain_single

variables (g : group_ring (fin 1 → G))

lemma delta_zero_cons (g : group_ring (fin 1 → G)) :
  finsupp.map_domain (λ v : fin 2 → G, v ∘ fin.delta rfl 0) (cons G 1 1 g) = g :=
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

lemma cons_delta_two {M : Type*} [monoid M] (f : fin 1 → M) :
  (fin.cons 1 f : fin 2 → M) ∘ (fin.delta rfl 1) = 1 :=
begin
  ext,
  rw [subsingleton.elim x 0, function.comp_app],
  dunfold fin.delta,
  convert @fin.cons_zero 1 (λ i, M) _ _,
end

lemma delta_one_cons (g : group_ring (fin 1 → G)) :
  finsupp.map_domain (λ v : fin 2 → G, v ∘ fin.delta rfl 1) (cons G 1 1 g) =
    finsupp.single 1 (coeff_sum G (group_ring_one_equiv G g)).down :=
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
  { rw coeff_sum_group_ring_one_equiv_apply,
    unfold finsupp.map_domain,
    dsimp,
    rw finsupp.total_apply,
    simp only [finsupp.sum_apply, cons_delta_two, finsupp.single_eq_same],
    unfold finsupp.sum,
    rw ulift.sum_down,
    congr,
    ext,
    dsimp,
    rw mul_one }
end

variables (n : ℕ)

instance (M : submodule (group_ring G) (group_ring (fin n → G))) :
  has_coe M (group_ring (fin n → G)) :=
{ coe := λ m, m.1 }

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
  { simp only [neg_mul_eq_neg_mul_symm, finsupp.single_neg, add_zero, one_mul,
     finset.sum_empty, finset.range_zero, pow_one, pow_zero, neg_add_eq_sub] },
  { rw [←finset.range_add_one, zero_add],
    exact finset.not_mem_range_self }
end

lemma d_cons (x : group_ring (fin 1 → G)) (hx : x ∈ ((coeff_sum G).comp
    (group_ring_one_equiv G).to_linear_map).ker) :
  d G (show 2 = 1 + 1, from rfl) (cons G 1 1 x) = x :=
begin
  cases x with x hx,
  rw [d_two_apply, delta_zero_cons, delta_one_cons],
  convert sub_zero _,
  rw finsupp.single_eq_zero,
  erw linear_map.mem_ker.1 hx,
  exact ulift.zero_down,
end

instance std_resn_exact₀ : exact (Module.as_hom $ d G (show 2 = 1 + 1, from rfl))
  (Module.as_hom ((coeff_sum G).comp (group_ring_one_equiv G).to_linear_map)) :=
(Module.exact_iff _ _).2 $
begin
  ext,
  split,
  { rintros ⟨y, rfl⟩,
    exact coeff_sum_d G },
  { intro hx,
    use cons G 1 1 x,
    exact d_cons G x hx }
end

-- idk where this is .
instance : functor.additive (forget₂ (Module (group_ring G)) AddCommGroup) :=
{ map_zero' := λ x y, rfl,
  map_add' := λ  x y f g, rfl }

abbreviation std_resn_aug_AddCommGroup :=
((forget₂ (Module (group_ring G)) AddCommGroup).map_homological_complex (complex_shape.down ℕ)).obj
  ((std_resn_complex G).augment ((coeff_sum G).comp (group_ring_one_equiv G).to_linear_map)
  (by ext1; exact coeff_sum_d G))

def std_resn_homotopy_aux : trivial G →+ group_ring (fin 1 → G) :=
{ to_fun := λ n, finsupp.single 1 n.down,
  map_zero' := finsupp.single_zero,
  map_add' := λ x y, finsupp.single_add }

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

lemma cons_d (g : G) (x : fin (n + 1) → G) :
  d G rfl (of (fin (n + 2) → G) $ fin.cons g x) + cons G n g (d G rfl (of _ x)) = of _ x :=
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

def std_resn_homotopy :
  homotopy (𝟙 (std_resn_aug_AddCommGroup G)) 0 :=
homotopy.of _ _ (λ n, nat.rec_on n (std_resn_homotopy_aux G) (λ m fm, cons G _ 1))
(by { ext1,
  show x = coeff_sum G (group_ring_one_equiv G (finsupp.single _ _)) + 0,
  rw [coeff_sum_group_ring_one_equiv_apply, finsupp.total_single, add_zero],
  ext,
  simp only [mul_one, algebra.id.smul_eq_mul, ulift.smul_down']}) $
λ i, nat.rec_on i
(begin
  ext1,
  refine x.induction_on _ _ _,
  { intro x,
    dsimp,
    show finsupp.single _ _ = finsupp.single _ (coeff_sum G (group_ring_one_equiv _ _)).down
      + d _ _ _ + _,
    simp only [coeff_sum_group_ring_one_equiv_apply, finsupp.total_single, add_zero],
    simp only [cons, finsupp.map_domain.add_monoid_hom_apply, one_gsmul,
      finsupp.map_domain_single, eq_to_hom_refl, Module.id_apply],
    erw d_two_apply,
    simp only [cons_delta_two, add_sub_cancel'_right, finsupp.map_domain_single],
    congr,
    ext j,
    rw [function.comp_app, @subsingleton.elim (fin 1) _ j 0],
    convert (@fin.cons_succ 1 (λ i, G) 1 x _).symm },
  { intros f g hf hg,
    rw [add_monoid_hom.map_add, add_monoid_hom.map_add, hf, hg]},
  { intros r f hf,
    rw [add_monoid_hom.map_gsmul, add_monoid_hom.map_gsmul, hf]}
end)
(λ j hj,
begin
  clear hj,
  ext1,
  refine x.induction_on _ _ _,
  { intro y,
    dsimp at *,
    show finsupp.single _ _ = cons G _ _ _ + _ + 0,
    simp only [add_zero, comp_apply, finsupp.map_domain.add_monoid_hom_apply,
      chain_complex.augment_d_succ_succ, finsupp.map_domain_single],
    simp only [add_comm],
    dunfold std_resn_complex,
    rw [chain_complex.of_d, chain_complex.of_d],
    unfold cons,
    dsimp,
    rw finsupp.map_domain_single,
    exact (cons_d _ _ _ _).symm },
  { intros f g hf hg,
    rw [add_monoid_hom.map_add, add_monoid_hom.map_add, hf, hg]},
  { intros r f hf,
    rw [add_monoid_hom.map_gsmul, add_monoid_hom.map_gsmul, hf] }
end)

--cba to work out what instances I need here
def exact_of_homotopy_zero {ι : Type*}
  {c : complex_shape ι} {C : homological_complex AddCommGroup c}
  (h : homotopy (𝟙 C) 0) (j : ι) :
  exact (C.d_to j) (C.d_from j) :=
(preadditive.exact_iff_homology_zero (C.d_to j) (C.d_from j)).2 $
⟨homological_complex.d_to_comp_d_from _ _, ⟨@limits.iso_zero_of_epi_zero _ _ _ _
  ((homology_functor _ c j).obj C) _ $
begin
  have := homology_map_eq_of_homotopy h j,
  rw (homology_functor _ _ _).map_zero at this,
  { rw [← this, functor.map_id'],
    exact category_struct.id.epi _},
  { exact homological_complex.homology_additive _ },
end⟩⟩

lemma exact_to_from_iff {V : Type*} [category V] [limits.has_images V] [limits.has_zero_morphisms V]
  [limits.has_zero_object V] [limits.has_equalizers V] {C : chain_complex V ℕ} {j : ℕ} :
  exact (C.d_to (j + 1)) (C.d_from (j + 1)) ↔ exact (C.d (j + 2) (j + 1)) (C.d (j + 1) j) :=
begin
  rw [C.d_to_eq rfl, C.d_from_eq rfl, exact_iso_comp, exact_comp_iso],
end

-- idk how to do this stupid obvious thing
instance exact_of_AddCommGroup_exact {R : Type*} [ring R]
  {A B C : Module R} (f : A ⟶ B) (g : B ⟶ C)
  [h : exact ((forget₂ (Module R) AddCommGroup).map f) ((forget₂ (Module R) AddCommGroup).map g)] :
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

def std_resn : ProjectiveResolution (trivial G) :=
{ complex := std_resn_complex G,
  π := std_resn_π G,
  projective := λ n, @Module.projective_of_free.{u u u} _ _
    (Module.of (group_ring G) (group_ring (fin (n + 1) → G))) _ (basis.{u} G n),
  exact₀ := group_ring.std_resn_exact₀ G,
  exact := λ n, exact_to_from_iff.1 $ group_ring.exact_d_to_d_from G _,
  epi := (Module.epi_iff_range_eq_top _).2 $ ((group_ring_one_equiv G).range_comp _).trans
    (range_coeff_sum_eq_top G) }


end group_ring
