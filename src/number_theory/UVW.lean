import number_theory.general_bernoullli_number_properties_three
import number_theory.teich_char
import topology.algebra.nonarchimedean.bases

open_locale big_operators
local attribute [instance] zmod.topological_space

open filter
open_locale topological_space

open_locale big_operators

variables (p : ℕ) [fact (nat.prime p)] (d : ℕ) (R : Type*) [normed_comm_ring R] (m : ℕ)
(hd : d.gcd p = 1) (χ : dirichlet_character R (d*(p^m))) {c : ℕ} (hc : c.gcd p = 1)
(hc' : c.gcd d = 1) (na : ∀ (n : ℕ) (f : ℕ → R),
  ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
(w : weight_space (units (zmod d) × units ℤ_[p]) R)

variable [fact (0 < d)]
variables [complete_space R] [char_zero R]

/-- Gives the equivalence (ℤ/(m * n)ℤ)ˣ ≃* (ℤ/mℤ)ˣ × (ℤ/nℤ)ˣ -/
-- It would be nice to use units.homeomorph.prod_units instead, however no way to identify it as a mul_equiv.
abbreviation units.chinese_remainder {m n : ℕ} (h : m.coprime n) :
  (zmod (m * n))ˣ ≃* (zmod m)ˣ × (zmod n)ˣ :=
mul_equiv.trans (units.map_equiv (zmod.chinese_remainder h).to_mul_equiv) mul_equiv.prod_units

lemma h1 (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) :
  filter.tendsto f.comp (nhds ((continuous_map.id (zmod d)ˣ).prod_map
    (continuous_map.id ℤ_[p]ˣ))) (nhds f) :=
begin
  convert_to filter.tendsto f.comp (nhds (continuous_map.id _)) (nhds f),
  { congr, ext a,
    { congr, },
    { simp only [continuous_map.id_apply], rw units.ext_iff, congr, }, },
  { delta filter.tendsto, delta filter.map, rw filter.le_def,
    intros x hx, simp,
    rw mem_nhds_iff at *,
    rcases hx with ⟨s, hs, h1, h2⟩,
    refine ⟨f.comp ⁻¹' s, _, _, _⟩,
    { intros a ha,
      rw set.mem_preimage at *,
      apply hs ha, },
    { refine is_open.preimage _ h1, exact continuous_map.continuous_comp f, },
    { rw set.mem_preimage, rw continuous_map.comp_id, apply h2, }, },
end

open continuous_map

private lemma preimage_gen {α β γ : Type*} [topological_space α] [topological_space β]
  [topological_space γ] (g : C(β, γ)) {s : set α} (hs : is_compact s) {u : set γ} (hu : is_open u) :
  continuous_map.comp g ⁻¹' (compact_open.gen s u) = compact_open.gen s (g ⁻¹' u) :=
begin
  ext ⟨f, _⟩,
  change g ∘ f '' s ⊆ u ↔ f '' s ⊆ g ⁻¹' u,
  rw [set.image_comp, set.image_subset_iff]
end

lemma helper_char (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) (g : ℕ → C((zmod d)ˣ × ℤ_[p]ˣ, (zmod d)ˣ × ℤ_[p]ˣ))
  (h : filter.tendsto (λ j : ℕ, g j) filter.at_top (nhds (continuous_map.id _))) :
  filter.tendsto (λ j : ℕ, continuous_map.comp f (g j)) filter.at_top (nhds f) :=
begin
  apply topological_space.tendsto_nhds_generate_from,
  simp only [exists_prop, set.mem_set_of_eq, filter.mem_at_top_sets, ge_iff_le, set.mem_preimage, forall_exists_index, and_imp],
  simp_rw [← @set.mem_preimage _ _ f.comp _ _],
  rintros s t compt a opena hs mems,
  simp_rw [hs, preimage_gen _ compt opena],
  rw tendsto_nhds at h, simp only [filter.mem_at_top_sets, ge_iff_le, set.mem_preimage] at h,
  apply h,
  { apply continuous_map.is_open_gen compt (continuous.is_open_preimage (map_continuous _) _ opena), },
  { rw ← preimage_gen _ compt opena, rw set.mem_preimage, rw comp_id, rw ← hs, apply mems, },
end

/-lemma fn_eq_sum_char_fn [normed_algebra ℚ R] [norm_one_class R] (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) : filter.tendsto
  (λ j : ℕ, ∑ a : (zmod (d * (p^j)))ˣ, (f (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_right _ _)
     (zmod d) _ (zmod.char_p d)).to_monoid_hom a,
     rev_coe p (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_left _ _) (zmod (p^j)) _ _).to_monoid_hom a)) •
     (locally_constant.char_fn R (is_clopen_units_clopen_from p d j
     ((units.chinese_remainder (nat.coprime_pow_spl p d j hd)) a)))  : C((zmod d)ˣ × ℤ_[p]ˣ, R)))
  (filter.at_top) (nhds f) := sorry-/

lemma integral_loc_const_eval [normed_algebra ℚ R] [norm_one_class R]
  (f : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) :
  measure.integral (bernoulli_measure' p d R hc hc' hd na) f =
  (bernoulli_measure' p d R hc hc' hd na).val f :=
begin
  delta measure.integral, simp,
  convert dense_inducing.extend_eq (measure.dense_ind_inclusion _ _) (measure.integral_cont _) _,
  apply_instance,
  apply_instance,
  apply_instance,
end

lemma trying [normed_algebra ℚ R] [norm_one_class R] (f : C((zmod d)ˣ × ℤ_[p]ˣ, R))
  (i : ℕ → locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R)
  (hf : filter.tendsto (λ j : ℕ, (i j : C((zmod d)ˣ × ℤ_[p]ˣ, R))) (filter.at_top) (nhds f)) :
  filter.tendsto (λ j : ℕ, (bernoulli_measure' p d R hc hc' hd na).1 (i j)) (filter.at_top)
  (nhds (measure.integral (bernoulli_measure' p d R hc hc' hd na) f)) :=
begin
  convert filter.tendsto.comp (continuous.tendsto (continuous_linear_map.continuous (measure.integral
     (bernoulli_measure' p d R hc hc' hd na) )) f) hf,
  ext,
  simp,
  rw integral_loc_const_eval, simp,
end

lemma locally_constant.to_continuous_map_smul (f : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) (r : R) :
  ((r • f : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) : C((zmod d)ˣ × ℤ_[p]ˣ, R)) =
  r • (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) :=
begin
  ext,
  simp only [locally_constant.coe_continuous_map, locally_constant.coe_smul,
    continuous_map.coe_smul],
end

variables [normed_algebra ℚ_[p] R] [fact (0 < m)]

-- this is the difficult simp
lemma mul_equiv.prod_units.coe_symm_apply {M : Type*} {N : Type*} [monoid M] [monoid N]
  (a : Mˣ) (b : Nˣ) : (mul_equiv.prod_units.symm (a, b) : M × N) = (a, b) :=
by { delta mul_equiv.prod_units, simp }

lemma prod.eq_fst_snd {α β : Type*} (a : α × β) : a = (a.fst, a.snd) := by refine prod.ext rfl rfl

lemma ring_equiv.to_monoid_hom_inv_fun_eq_inv_fun {R S : Type*} [semiring R] [semiring S]
  (h : R ≃+* S) : (h : R ≃* S).inv_fun = h.inv_fun := by { ext, solve_by_elim }

lemma units.chinese_remainder_symm_apply_fst {n : ℕ} (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  (((units.chinese_remainder (nat.coprime_pow_spl p d n hd)).symm a : zmod (d * (p^n))) : zmod d) =
  (a.fst : zmod d) :=
begin
  delta units.chinese_remainder,
  simp only [ring_equiv.to_mul_equiv_eq_coe, mul_equiv.symm_trans_apply],
  rw units.map_equiv, simp, rw prod.eq_fst_snd a,
  rw mul_equiv.prod_units.coe_symm_apply, rw ← mul_equiv.inv_fun_eq_symm,
  rw ring_equiv.to_monoid_hom_inv_fun_eq_inv_fun (zmod.chinese_remainder
    (nat.coprime_pow_spl p d n hd)),
  change (zmod.cast_hom (dvd_mul_right d (p^n)) (zmod d))((zmod.chinese_remainder _).inv_fun
    (↑(a.fst), ↑(a.snd))) = ↑(a.fst),
  rw proj_fst',
end

lemma units.chinese_remainder_symm_apply_snd {n : ℕ} (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  (((units.chinese_remainder (nat.coprime_pow_spl p d n hd)).symm a : zmod (d * (p^n))) : zmod (p^n)) =
  (a.snd : zmod (p^n)) :=
begin
  delta units.chinese_remainder,
  simp only [ring_equiv.to_mul_equiv_eq_coe, mul_equiv.symm_trans_apply],
  rw units.map_equiv, simp, rw prod.eq_fst_snd a,
  rw mul_equiv.prod_units.coe_symm_apply, rw ← mul_equiv.inv_fun_eq_symm,
  rw ring_equiv.to_monoid_hom_inv_fun_eq_inv_fun (zmod.chinese_remainder
    (nat.coprime_pow_spl p d n hd)),
  change (zmod.cast_hom (dvd_mul_left (p^n) d) (zmod (p^n)))((zmod.chinese_remainder _).inv_fun
    (↑(a.fst), ↑(a.snd))) = ↑(a.snd),
  rw proj_snd',
end

lemma padic_int.is_unit_to_zmod_pow_of_is_unit (n : ℕ) (hn : 1 < n) (x : ℤ_[p])
  (hx : is_unit (padic_int.to_zmod_pow n x)) : is_unit x :=
begin
  rw padic_int.is_unit_iff,
  by_contra h,
  have hx' := lt_of_le_of_ne (padic_int.norm_le_one _) h,
  rw padic_int.norm_lt_one_iff_dvd at hx',
  cases hx' with y hy,
  rw hy at hx,
  rw ring_hom.map_mul at hx,
  rw is_unit.mul_iff at hx,
  simp only [map_nat_cast] at hx,
  have : ¬ is_unit (p : zmod (p^n)),
  { intro h,
    set q : (zmod (p^n))ˣ := is_unit.unit h,
    have := zmod.val_coe_unit_coprime q,
    rw is_unit.unit_spec at this,
    rw nat.coprime_pow_right_iff (lt_trans zero_lt_one hn) at this,
    rw zmod.val_cast_of_lt _ at this,
    simp only [nat.coprime_self] at this,
    apply @nat.prime.ne_one p (fact.out _),
    rw this,
    conv { congr, rw ← pow_one p, },
    rw pow_lt_pow_iff _, apply hn,
    apply nat.prime.one_lt (fact.out _),
    apply_instance, },
  apply this, apply hx.1,
end

lemma helper_289 {n : ℕ} (hn : 1 < n) (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  loc_const_ind_fn R p d (locally_constant.char_fn R (is_clopen_units_clopen_from p d n a)) =
  locally_constant.char_fn R (is_clopen_clopen_from p d n (↑(((units.chinese_remainder
  (nat.coprime_pow_spl p d n hd)).symm) a))) :=
begin
  ext,
  rw loc_const_ind_fn, rw ← locally_constant.to_fun_eq_coe,
  simp only, rw ind_fn, simp only, split_ifs,
  { by_cases hx : x ∈ clopen_from p d n ↑(((units.chinese_remainder
      (nat.coprime_pow_spl p d n hd)).symm) a),
    { rw (locally_constant.char_fn_one R x _).1 hx, rw ← locally_constant.char_fn_one R _ _,
      rw set.mem_prod, rw set.mem_preimage, rw set.mem_singleton_iff, rw set.mem_singleton_iff,
      rw units.ext_iff, rw units.ext_iff, rw is_unit.unit_spec, rw units.coe_map,
      rw is_unit.unit_spec, rw mem_clopen_from at hx, rw hx.1, rw ring_hom.to_monoid_hom_eq_coe,
      rw ring_hom.coe_monoid_hom, rw ← hx.2, rw units.chinese_remainder_symm_apply_fst,
      rw units.chinese_remainder_symm_apply_snd, refine ⟨rfl, rfl⟩, },
    { rw (locally_constant.char_fn_zero R x _).1 hx, rw ← locally_constant.char_fn_zero R _ _,
      -- this should be a separate lemma mem_units_clopen_from
      rw set.mem_prod, rw set.mem_preimage, rw set.mem_singleton_iff, rw set.mem_singleton_iff,
      rw units.ext_iff, rw units.ext_iff, rw is_unit.unit_spec, rw units.coe_map,
      rw is_unit.unit_spec, intro h', apply hx, rw mem_clopen_from, rw h'.1,
      rw ring_hom.to_monoid_hom_eq_coe at h', rw ring_hom.coe_monoid_hom at h',
      rw h'.2, rw units.chinese_remainder_symm_apply_fst,
      rw units.chinese_remainder_symm_apply_snd, refine ⟨rfl, rfl⟩, }, },
  rw (locally_constant.char_fn_zero R x _).1 _,
  rw mem_clopen_from, intro h', apply h, rw units.chinese_remainder_symm_apply_fst at h',
  rw units.chinese_remainder_symm_apply_snd at h', split,
  { rw h'.1, apply units.is_unit _, },
  { apply padic_int.is_unit_to_zmod_pow_of_is_unit p n hn x.snd, rw ← h'.2, apply units.is_unit _, },
end

variable [fact (0 < d)]

lemma ring_equiv.eq_inv_fun_iff {α β : Type*} [semiring α] [semiring β] (h : α ≃+* β) (x : β) (y : α) :
  y = h.inv_fun x ↔ h y = x := ⟨λ h, by simp only [h, ring_equiv.inv_fun_eq_symm,
    ring_equiv.apply_symm_apply], λ h, by { rw [ring_equiv.inv_fun_eq_symm, ← h,
    ring_equiv.symm_apply_apply], }⟩

lemma proj_fst'' {n : ℕ} (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
((zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).inv_fun (↑(a.fst), ↑(a.snd)) : zmod d) = a.fst :=
proj_fst' _ _ _ _ _

lemma proj_snd'' {n : ℕ} (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
(padic_int.to_zmod_pow n) ((zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).inv_fun (↑(a.fst), ↑(a.snd)) : ℤ_[p]) = a.snd :=
begin
  rw ← zmod.int_cast_cast,
  rw ring_hom.map_int_cast,
  rw zmod.int_cast_cast, convert proj_snd' _ _ _ _ _,
end

lemma bernoulli_measure'_eval_char_fn [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n)
  (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  (bernoulli_measure' p d R hc hc' hd na).val (locally_constant.char_fn R
  (is_clopen_units_clopen_from p d n a)) =
  (algebra_map ℚ R (E_c p d hc n ((zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).inv_fun
  ((a.1 : zmod d), (a.2 : zmod (p^n))))) ) :=
begin
  delta bernoulli_measure', simp only [linear_map.coe_mk, ring_equiv.inv_fun_eq_symm],
  delta bernoulli_distribution, simp only [linear_map.coe_mk],
  rw sequence_limit_eq _ n _,
  { delta g, simp only [algebra.id.smul_eq_mul],
    convert finset.sum_eq_single_of_mem _ _ (λ b memb hb, _),
    swap 2, { refine ((zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).inv_fun
      ((a.1 : zmod d), (a.2 : zmod (p^n)))), },
    { conv_lhs { rw ← one_mul ((algebra_map ℚ R)
        (E_c p d hc n (((zmod.chinese_remainder _).symm) (↑(a.fst), ↑(a.snd))))), },
      congr,
      rw loc_const_ind_fn, simp only [ring_equiv.inv_fun_eq_symm, locally_constant.coe_mk],
      rw ind_fn, simp only, rw dif_pos _,
      { symmetry, rw ← locally_constant.char_fn_one, rw set.mem_prod,
        simp only [prod.fst_zmod_cast, prod.snd_zmod_cast, set.mem_singleton_iff,
          ring_hom.to_monoid_hom_eq_coe, set.mem_preimage],
        rw units.ext_iff, rw units.ext_iff,
        rw is_unit.unit_spec, rw units.coe_map, rw is_unit.unit_spec,
        rw ← ring_equiv.inv_fun_eq_symm,
        rw proj_fst'', rw ring_hom.coe_monoid_hom (@padic_int.to_zmod_pow p _ n),
        rw proj_snd'', simp only [eq_self_iff_true, and_self], },
      { rw ← ring_equiv.inv_fun_eq_symm,
        simp only [prod.fst_zmod_cast, prod.snd_zmod_cast],
        split,
        { rw proj_fst'', apply units.is_unit, },
        { apply padic_int.is_unit_to_zmod_pow_of_is_unit p n hn,
          rw proj_snd'', apply units.is_unit, }, }, },
    { delta zmod', apply finset.mem_univ, },
    { rw mul_eq_zero_of_left _, rw helper_289 p d R hd hn a,
      rw ← locally_constant.char_fn_zero R _ _, rw mem_clopen_from, intro h, apply hb,
      rw units.chinese_remainder_symm_apply_snd at h,
      rw units.chinese_remainder_symm_apply_fst at h,
      rw h.2, rw ← h.1,
      rw ring_equiv.eq_inv_fun_iff, rw ← ring_equiv.coe_to_equiv,
      change (zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).to_equiv b = _,
      rw prod.ext_iff, rw inv_fst', rw inv_snd',
      simp only [prod.fst_zmod_cast, eq_self_iff_true, prod.snd_zmod_cast, true_and],
      conv_rhs { rw ← zmod.int_cast_cast, }, rw ring_hom.map_int_cast,
      rw zmod.int_cast_cast, }, },
  { convert seq_lim_g_char_fn p d R n
      ((units.chinese_remainder (nat.coprime_pow_spl p d n hd)).symm a : zmod (d * p^n)) hc hc' hd _,
    { apply helper_289 p d R hd hn a, },
    { apply fact.out _, apply_instance, }, },
end

lemma nat_spec' (p : ℕ → Prop) (h : ({n : ℕ | ∀ (x : ℕ), x ≥ n → p x}).nonempty) (x : ℕ)
  (hx : x ≥ Inf {n : ℕ | ∀ (x : ℕ) (hx : x ≥ n), p x}) : p x := nat.Inf_mem h x hx

noncomputable def U_def [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (k : ℕ) :=
  ∑ (x : (zmod (d * p ^ k))ˣ),
  ((asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m)^n) x : R) *
  ((((x : zmod (d * p^k))).val)^(n - 1) : R)) •
  (algebra_map ℚ R) (int.fract (↑x / (↑d * ↑p ^ k)))
-- Idea 1 : replacing k by m + k so we can remove (hk : m ≤ k)
-- Idea 2 : Use `asso_dirichlet_character` instead to get rid of hk, since coercion on non-units
-- can be anywhere

lemma finset.sum_equiv' {s t α : Type*} [fintype s] [fintype t] [add_comm_monoid α] (h : s ≃ t)
  (f : t → α) : ∑ (x : t), f x = ∑ (x : s), f (h x) :=
begin
  apply finset.sum_bij,
  swap 5, { rintros, refine h.inv_fun a, },
  { rintros, apply finset.mem_univ _, },
  { simp only [equiv.inv_fun_as_coe, equiv.apply_symm_apply, eq_self_iff_true, implies_true_iff], },
  { simp only [equiv.inv_fun_as_coe, embedding_like.apply_eq_iff_eq, imp_self, forall_2_true_iff], },
  { refine λ a ha, ⟨h a, finset.mem_univ _, _⟩,
    simp only [equiv.inv_fun_as_coe, equiv.symm_apply_apply], },
end

lemma finset.sum_equiv {s t α : Type*} [fintype s] [fintype t] [add_comm_monoid α] (h : s ≃ t)
  (f : s → α) : ∑ (x : s), f x = ∑ (x : t), f (h.inv_fun x) :=
begin
  rw finset.sum_equiv' h, simp,
end

noncomputable def units.equiv_is_unit {α : Type*} [monoid α] : units α ≃ {x : α // is_unit x} :=
{ to_fun := λ u, ⟨u, units.is_unit u⟩,
  inv_fun := λ ⟨u, hu⟩, is_unit.unit hu,
  left_inv := λ x, units.ext_iff.2 (is_unit.unit_spec _),
  right_inv := λ x, by { apply subtype.ext_val, tidy, }, }

noncomputable def zmod.units_equiv_coprime' {n : ℕ} [fact (0 < n)] :
  units (zmod n) ≃ {x : ℕ // x < n ∧ x.coprime n} :=
{ to_fun := λ u, ⟨(u : zmod n).val, ⟨zmod.val_lt _, zmod.val_coe_unit_coprime _⟩ ⟩,
  inv_fun := λ x, zmod.unit_of_coprime _ x.2.2,
  left_inv := begin rw function.left_inverse, sorry, end,
  right_inv := sorry, }

instance zmod.units_fintype (n : ℕ) : fintype (zmod n)ˣ :=
begin
  by_cases n = 0,
  { rw h, refine units_int.fintype, },
  { haveI : fact (0 < n),
    { apply fact_iff.2, apply nat.pos_of_ne_zero h, },
    apply_instance, },
end

-- not needed?
lemma set.finite_of_finite_inter {α : Type*} (s : finset α) (t : set α) :
  set.finite ((s : set α) ∩ t : set α) := set.finite.inter_of_left (finset.finite_to_set s) t

lemma sum_units_eq {x : ℕ} (hx : 0 < x) (f : ℕ → R) :
  ∑ (i : units (zmod (d * p^x))), f (i : zmod (d * p^x)).val =
  ∑ i in set.finite.to_finset (set.finite_of_finite_inter (finset.range (d * p^x))
  ({x | x.coprime d} ∩ {x | x.coprime p})), f i :=
begin
  apply finset.sum_bij,
  swap 5, { refine λ a ha, (a : zmod (d * p^x)).val, },
  { intros a ha,
    simp only [set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe, finset.mem_range,
      set.mem_set_of_eq],
    refine ⟨zmod.val_lt _, _⟩,
    set b := zmod.units_equiv_coprime a,
    have := nat.coprime_mul_iff_right.1 b.2,
    rw nat.coprime_pow_right_iff hx at this,
    apply this, },
  { intros a ha, refl, },
  { intros a₁ a₂ ha₁ ha₂ h,
    haveI : fact (0 < d * p^x) := imp p d x,
    rw units.ext_iff, rw zmod.val_injective _ h, },
  { intros b hb,
    simp only [set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe, finset.mem_range,
      set.mem_set_of_eq] at hb,
    refine ⟨zmod.units_equiv_coprime.inv_fun ⟨b, (zmod.val_cast_of_lt hb.1).symm ▸
      (nat.coprime.mul_right hb.2.1 (nat.coprime.pow_right _ hb.2.2)) ⟩, finset.mem_univ _, _⟩,
    rw zmod.units_equiv_coprime,
    simp only [zmod.coe_unit_of_coprime, zmod.nat_cast_val, zmod.cast_nat_cast'],
    rw zmod.val_cast_of_lt hb.1, },
end

lemma dirichlet_character.mul_eq_mul {n : ℕ} (χ ψ : dirichlet_character R n) {a : ℕ}
  (ha : is_unit (a : zmod n)) :
  asso_dirichlet_character (χ.mul ψ) a = asso_dirichlet_character (χ * ψ) a :=
begin
  delta dirichlet_character.mul,
  have lcm_eq_self : lcm n n = n := nat.lcm_self n,
  have h1 := classical.some_spec ((χ.change_level (dvd_lcm_left n n) * ψ.change_level
    (dvd_lcm_right n n)).factors_through_conductor).ind_char,
  have h2 := congr_arg asso_dirichlet_character h1,
  rw monoid_hom.ext_iff at h2, specialize h2 a,
  have h : is_unit (a : zmod (lcm n n)),
  { convert ha, }, -- lcm_eq_self ▸ ha does not work
  rw dirichlet_character.change_level_asso_dirichlet_character_eq' _ _ h at h2,
  rw zmod.cast_nat_cast (dirichlet_character.conductor_dvd ((χ.change_level (dvd_lcm_left n n) *
    ψ.change_level (dvd_lcm_right n n)))) at h2,
  delta dirichlet_character.asso_primitive_character,
  rw ← h2,
  rw dirichlet_character.asso_dirichlet_character_mul,
  rw dirichlet_character.asso_dirichlet_character_mul, rw monoid_hom.mul_apply,
  rw monoid_hom.mul_apply,
  rw dirichlet_character.change_level_asso_dirichlet_character_eq' _ _ h,
  rw dirichlet_character.change_level_asso_dirichlet_character_eq' _ _ h,
  rw zmod.cast_nat_cast (dvd_lcm_left n n) a,
  any_goals { refine zmod.char_p _, },
end

lemma helper_U_1 [normed_algebra ℚ R] [norm_one_class R] {n : ℕ} (x : ℕ) :
  ∑ (x_1 : ℕ) in finset.range (d * p ^ x), (1 / ↑(d * p ^ x : ℕ) : ℚ) •
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) (↑p * ↑x_1) *
  (↑p ^ (n - 1) * ↑x_1 ^ n)) = ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime p})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x)) := sorry

lemma helper_U_2 [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) :
  tendsto (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime d})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x))) at_top (nhds 0) := sorry

lemma helper_U_3 (x : ℕ) : finset.range (d * p^x) = set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime d})) ∪ ((set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime p}))) ∪ set.finite.to_finset (set.finite_of_finite_inter (finset.range (d * p^x))
  ({x | x.coprime d} ∩ {x | x.coprime p}))) :=
begin
  ext,
  simp only [finset.mem_range, finset.mem_union, set.finite.mem_to_finset, set.mem_inter_eq,
    finset.mem_coe, set.mem_set_of_eq],
  split, -- better way to do this?
  { intro h,
    by_cases h' : a.coprime d ∧ a.coprime p, { right, right, refine ⟨h, h'⟩, },
    { rw not_and_distrib at h', cases h',
      { left, refine ⟨h, h'⟩, },
      { right, left, refine ⟨h, h'⟩, }, }, },
  { intro h, cases h, apply h.1,
    cases h, apply h.1, apply h.1, },
end

lemma zmod.is_unit_val_of_unit {n k : ℕ} [fact (0 < n)] (hk : k ∣ n) (u : (zmod n)ˣ) :
  is_unit ((u : zmod n).val : zmod k) :=
by { sorry, }

lemma U [normed_algebra ℚ R] [norm_one_class R] [no_zero_divisors R] (n : ℕ) (hn : 1 < n)
  (hχ : χ.is_even) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥) :
  filter.tendsto (λ j : ℕ, U_def p d R m χ n j)
  filter.at_top (nhds ((1 - asso_dirichlet_character (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) n)) ) :=
begin
  delta U_def,
  have h1 := lim_even_character d p m χ na hn hχ hp,
  have h2 := filter.tendsto.const_mul ((asso_dirichlet_character
    (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑p * ↑p ^ (n - 1)) h1,
  have h3 := filter.tendsto.sub (filter.tendsto.sub h1 (helper_U_2 p d R m χ n)) h2,
  clear h1 h2,
  convert (tendsto_congr' _).2 h3, -- might need a tendsto_congr' here
  { rw sub_zero, rw ← one_sub_mul, },
  { clear h3,
    rw eventually_eq, rw eventually_at_top,
    refine ⟨m, λ x hx, _⟩,
    simp only,
    haveI : fact (0 < d * p^x) := imp p d x,
    have h1 : d * p^m ∣ d * p^x, sorry,
    rw finset.smul_sum, rw finset.mul_sum, simp_rw mul_smul_comm,
    conv_rhs { congr, skip, apply_congr, skip, rw mul_mul_mul_comm, rw ← monoid_hom.map_mul, },
    conv_lhs { apply_congr, skip, rw coe_coe, rw coe_coe,
      rw ← zmod.nat_cast_val (x_1 : zmod (d * p^x)),
      rw ← zmod.nat_cast_val (x_1 : zmod (d * p^x)),
      rw fract_eq_self (zero_le_and_lt_one p d _ _).1 (zero_le_and_lt_one p d _ _).2,
      conv { congr, rw ← dirichlet_character.mul_eq_mul R χ
        (teichmuller_character_mod_p_change_level p d R m ^ n) (zmod.is_unit_val_of_unit h1 x_1), }, },
    convert sum_units_eq p d R _ (λ (y : ℕ), ((asso_dirichlet_character
      (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑y * ↑y ^ (n - 1)) •
      (algebra_map ℚ R) (((y : ℚ) / (↑d * ↑p ^ x)))),
    rw helper_U_1, apply sub_eq_of_eq_add', rw ← finset.sum_union _,
    apply sub_eq_of_eq_add', rw ← finset.sum_union _,
    { apply finset.sum_congr,
      { rw ← helper_U_3, },
      { intros y hy, rw ← algebra_map_smul R (1 / ↑(d * p ^ x : ℕ) : ℚ), rw smul_eq_mul, rw smul_eq_mul,
        { rw mul_comm, rw ← mul_one (y : ℚ), rw ← mul_div, rw ring_hom.map_mul, rw map_nat_cast,
          rw ← mul_assoc, rw [nat.cast_mul d _, nat.cast_pow p], apply congr_arg2 _ _ rfl,
          rw mul_assoc, apply congr_arg2 _ rfl _, rw ← pow_succ', rw nat.sub_add_cancel (le_of_lt hn), },
        { apply_instance, }, }, },
    sorry,
    sorry,
    sorry, },
end
#exit
lemma teichmuller_character_mod_p_change_level_def :
  teichmuller_character_mod_p_change_level p d R m = dirichlet_character.change_level (((units.map ((algebra_map ℚ_[p] R).comp
  (padic_int.coe.ring_hom)).to_monoid_hom).comp (teichmuller_character_mod_p p) : dirichlet_character R p)⁻¹ )
  (begin apply dvd_mul_of_dvd_right (dvd_pow_self p (ne_of_gt (fact.out _))), apply_instance, end) := rfl

variable (c)

noncomputable def V_def [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (j : ℕ) :=
∑ (x : (zmod (d * p ^ j))ˣ), ((asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m)^n) x : R) *
  ((((x : zmod (d * p^j))).val)^(n - 1) : R)) •
  (algebra_map ℚ R) (↑c * int.fract (((((c : zmod (d * p^(2 * j))))⁻¹ : zmod (d * p^(2 * j))) * x : ℚ) / (↑d * ↑p ^ j)))

variables (hc) (hc')

noncomputable def V_h_def [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (k : ℕ) :=
∑ (x : (zmod (d * p ^ k))ˣ), (asso_dirichlet_character (χ * teichmuller_character_mod_p_change_level p d R m ^ n) x) *
(↑(c ^ (n - 1)) * (algebra_map ℚ R) (↑(n - 1) * (↑d * (↑p ^ k *
(↑⌊↑((c : zmod (d * p^(2 * k)))⁻¹.val * ((x : zmod (d * p^k)) ).val) / ((d : ℚ) * ↑p ^ k)⌋ *
(↑d * (↑p ^ k * int.fract (((c : zmod (d * p^(2 * k)))⁻¹.val * ((x : zmod (d * p^k)) ).val : ℕ) /
((d : ℚ) * ↑p ^ k))))^(n - 1 - 1)))) * (↑c * int.fract ((((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k)))
* (x : ℚ)) / ((d : ℚ) * ↑p ^ k)))))

--lemma coprime_prime_non_zero {n : ℕ} (hn : nat.coprime n p) : n ≠ 0 := sorry

lemma nat.coprime_mul_pow {a b c : ℕ} (n : ℕ) (h1 : a.coprime b) (h2 : a.coprime c) :
  a.coprime (b * c^n) := nat.coprime_mul_iff_right.2 ⟨h1,
begin
  cases n,
  { apply nat.coprime_one_right _, },
  { rw nat.coprime_pow_right_iff (nat.succ_pos n),
    apply h2, },
end ⟩

--generalize
lemma nat.one_lt_mul_of_ne_one (k : ℕ) (h : d * p^k ≠ 1) : 1 < d * p^k :=
begin
  change 1 < _,
  rw nat.one_lt_iff_ne_zero_and_ne_one,
  refine ⟨nat.mul_ne_zero _ _, h⟩,
  --why does apply_instance not work? is there an easier way?
  { apply ne_zero_of_lt (fact.out _), exact 0, swap 2, convert _inst_3, },
  { apply pow_ne_zero _ (nat.prime.ne_zero (fact.out _)), apply_instance, },
end

lemma exists_V_h1_1 [normed_algebra ℚ R] [norm_one_class R] (hc' : c.coprime d) (hc : c.coprime p)
  (k : ℕ) : ∃ z : ℕ, c * ((c : zmod (d * p^(2 * k)))⁻¹.val) = dite (1 < d * p^(2 * k))
  (λ h, 1 + z * (d * p^(2 * k))) (λ h, 0) :=
begin
  have c_cop : c.coprime (d * p^(2 * k)) := nat.coprime_mul_pow (2 * k) hc' hc,
  by_cases eq_one : (d * p^(2 * k)) = 1,
  { have k_zero : ¬ 1 < d * p^(2 * k),
    { rw eq_one, simp only [nat.lt_one_iff, nat.one_ne_zero, not_false_iff], },
    refine ⟨1, _⟩, rw dif_neg k_zero,
    rw eq_one, simp only [nat.mul_eq_zero, zmod.val_eq_zero, eq_iff_true_of_subsingleton, or_true], },
  have h : (1 : zmod (d * p^(2 * k))).val = 1,
  { have : ((1 : ℕ) : zmod (d * p^(2 * k))) = 1, simp,
    rw ← this,
    rw zmod.val_cast_of_lt (nat.one_lt_mul_of_ne_one p d _ eq_one), },
  simp_rw dif_pos (nat.one_lt_mul_of_ne_one p d _ eq_one),
  conv { congr, funext, find 1 {rw ← h}, },
  conv { congr, funext, rw mul_comm z _, },
  apply (zmod.nat_coe_zmod_eq_iff _ _ _).1 _,
  { apply imp p d _, },
  { rw nat.cast_mul, rw zmod.nat_cast_val, rw zmod.cast_inv _ _ _ c_cop _,
    rw zmod.cast_nat_cast _, apply zmod.coe_mul_inv_eq_one _ c_cop,
    swap 2, { refine zmod.char_p _, },
    any_goals { apply dvd_rfl, }, },
end

lemma exists_V_h1_3 [normed_algebra ℚ R] [norm_one_class R] (hc' : c.coprime d) (hc : c.coprime p)
  (n k : ℕ) (hn : 0 < n) (x : (zmod (d * p^k))ˣ) : ∃ z : ℕ, ((x : zmod (d * p^k)).val)^n = c^n *
  (((c : zmod (d * p^(2 * k))))⁻¹.val * (x : zmod (d * p^k)).val)^n - z * (d * p^(2 * k)) :=
begin
  rw mul_pow, rw ← mul_assoc, rw ← mul_pow,
  obtain ⟨z₁, hz₁⟩ := exists_V_h1_1 p d R c hc' hc k,
  --obtain ⟨z₂, hz₂⟩ := exists_V_h1_2 p d R c _ x,
  rw hz₁,
  by_cases (d * p^(2 * k)) = 1,
  { refine ⟨0, _⟩, rw zero_mul,
    { rw nat.sub_zero,
      have h' : d * p^k = 1,
      { rw nat.mul_eq_one_iff, rw nat.mul_eq_one_iff at h, rw pow_mul' at h, rw pow_two at h,
        rw nat.mul_eq_one_iff at h, refine ⟨h.1, h.2.1⟩, },
      have : (x : (zmod (d * p ^ k))).val = 0,
      { rw zmod.val_eq_zero, sorry, },
      rw this, rw zero_pow, rw mul_zero, apply hn, }, },
  rw dif_pos (nat.one_lt_mul_of_ne_one p d _ h),
  rw add_pow, rw finset.sum_range_succ, rw one_pow, rw one_mul, rw nat.sub_self, rw pow_zero,
  rw one_mul, rw nat.choose_self, rw nat.cast_one, rw add_comm, rw add_mul, rw one_mul,
  simp_rw one_pow, simp_rw one_mul, simp_rw mul_pow _ (d * p^(2 * k)),
  conv { congr, funext, conv { to_rhs, congr, congr, skip, congr, apply_congr, skip,
    rw ← nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero (finset.mem_range_sub_ne_zero H)),
    rw pow_succ (d * p^(2 * k)) _, rw ← mul_assoc _ (d * p^(2 * k)) _,
    rw mul_comm _ (d * p^(2 * k)), rw mul_assoc, rw mul_assoc, }, },
  rw ← finset.mul_sum, rw mul_assoc, rw mul_comm (d * p^(2 * k)) _,
  refine ⟨(∑ (x : ℕ) in finset.range n, z₁ ^ (n - x).pred.succ *
    ((d * p ^ (2 * k)) ^ (n - x).pred * ↑(n.choose x))) * (x : zmod (d * p^k)).val ^ n, _⟩,
  rw nat.add_sub_cancel _ _,
end

lemma zmod.unit_ne_zero {n : ℕ} [fact (1 < n)] (a : (zmod n)ˣ) : (a : zmod n).val ≠ 0 :=
begin
  intro h,
  rw zmod.val_eq_zero at h,
  have : is_unit (0 : zmod n),
  { rw ← h, simp, },
  rw is_unit_zero_iff at this,
  apply @zero_ne_one _ _ _,
  rw this,
  apply zmod.nontrivial,
end

lemma exists_V_h1_4 [normed_algebra ℚ R] [norm_one_class R] (n k : ℕ) (hn : 0 < n) (hk : k ≠ 0)
  (x : (zmod (d * p^k))ˣ) :
  c^n * (((c : zmod (d * p^(2 * k))))⁻¹.val * (x : zmod (d * p^k)).val)^n >
  (classical.some (exists_V_h1_3 p d R c hc' hc n k hn x)) * (d * p^(2 * k)) :=
begin
  apply nat.lt_of_sub_eq_succ,
  rw ← classical.some_spec (exists_V_h1_3 p d R c hc' hc _ _ hn x),
  swap, { apply ((x : zmod (d * p^k)).val^n).pred, },
  rw (nat.succ_pred_eq_of_pos _),
  apply pow_pos _, apply nat.pos_of_ne_zero,
  haveI : fact (1 < d * p^k),
  { apply fact_iff.2, apply nat.one_lt_mul_of_ne_one p d _ _,
    intro h,
    rw nat.mul_eq_one_iff at h,
    have := (pow_eq_one_iff hk).1 h.2,
    apply nat.prime.ne_one (fact.out _) this, },
  apply zmod.unit_ne_zero,
end

lemma sq_mul (a b : ℚ) : (a * b)^2 = a * b^2 * a := by linarith

lemma exists_V_h1_5 [normed_algebra ℚ R] [norm_one_class R] (n k : ℕ) (hn : n ≠ 0) (x : (zmod (d * p^k))ˣ) :
  ∃ z : ℤ, ((((c : zmod (d * p^(2 * k))))⁻¹.val *
  (x : zmod (d * p^k)).val : ℕ) : ℚ)^n = (z * (d * p^(2 * k)) : ℚ) + n * (d * p^k) * ((int.floor (( (((((c : zmod (d * p^(2 * k))))⁻¹.val *
  (x : zmod (d * p^k)).val : ℕ)) / (d * p^k) : ℚ))))) * (d * p^k * int.fract (((((c : zmod (d * p^(2 * k))))⁻¹.val *
  (x : zmod (d * p^k)).val : ℕ)) / (d * p^k)))^(n - 1) + (d * p^k * int.fract (((((c : zmod (d * p^(2 * k))))⁻¹.val *
  (x : zmod (d * p^k)).val : ℕ)) / (d * p^k)))^n :=
begin
  have h1 : (d * p^k : ℚ) ≠ 0,
  { norm_cast, apply ne_zero_of_lt, refine fact_iff.1 (imp p d k), },
  conv { congr, funext, conv { to_lhs, rw [← mul_div_cancel'
        ((((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val) : ℕ) : ℚ) h1,
  ← int.floor_add_fract ((((c : zmod (d * p^(2 * k)))⁻¹.val *
        (x : zmod (d * p^k)).val) : ℕ) / (d * p^k) : ℚ),
  mul_add, add_pow, finset.sum_range_succ', pow_zero, one_mul, nat.sub_zero, nat.choose_zero_right,
  nat.cast_one, mul_one, ← nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero hn), finset.sum_range_succ',
  zero_add, pow_one, nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero hn), nat.choose_one_right,
  mul_comm _ (n : ℚ), ← mul_assoc (n : ℚ) _ _, ← mul_assoc (n : ℚ) _ _],
  congr, congr, apply_congr, skip, conv { rw pow_succ, rw pow_succ, rw mul_assoc (d * p^k : ℚ) _,
    rw ← mul_assoc _ ((d * p^k : ℚ) * _) _, rw ← mul_assoc _ (d * p^k : ℚ) _,
    rw mul_comm _ (d * p^k : ℚ), rw ← mul_assoc (d * p^k : ℚ) _ _,
    rw ← mul_assoc (d * p^k : ℚ) _ _, rw ← mul_assoc (d * p^k : ℚ) _ _, rw ← sq, rw sq_mul,
    rw ← pow_mul', rw mul_assoc (d * p^(2 * k) : ℚ) _ _, rw mul_assoc (d * p^(2 * k) : ℚ) _ _,
    rw mul_assoc (d * p^(2 * k) : ℚ) _ _, rw mul_assoc (d * p^(2 * k) : ℚ) _ _,
    rw mul_assoc (d * p^(2 * k) : ℚ) _ _, rw mul_comm (d * p^(2 * k) : ℚ),
    congr, congr, congr, skip, congr, congr, skip,
    rw ← nat.cast_pow,
    rw ← nat.cast_mul d (p^k),
    rw fract_eq_of_zmod_eq _ ((((c : zmod (d * p^(2 * k)))⁻¹.val *
        (x : zmod (d * p^k)).val) : ℕ) : zmod (d * p^k)).val (d * p^k) _,
    rw nat.cast_mul d (p^k), rw nat.cast_pow,
    rw fract_eq_self (zero_le_and_lt_one p d _ _).1 (zero_le_and_lt_one p d _ _).2, skip,
    rw ← zmod.cast_id (d * p^k) ((((c : zmod (d * p^(2 * k)))⁻¹.val *
        (x : zmod (d * p^k)).val) : ℕ) : zmod (d * p^k)),
    rw ← zmod.nat_cast_val ((((c : zmod (d * p^(2 * k)))⁻¹.val *
        (x : zmod (d * p^k)).val) : ℕ) : zmod (d * p^k)), apply_congr refl, }, }, },
  rw [← finset.sum_mul, mul_div_cancel' _ h1],
  simp only [nat.cast_mul, --zmod.nat_cast_val,
    add_left_inj, mul_eq_mul_right_iff, mul_eq_zero,
    nat.cast_eq_zero, ← int.cast_coe_nat],
  norm_cast,
  refine ⟨∑ (x_1 : ℕ) in finset.range n.pred, ↑d * ⌊rat.mk ↑((c : zmod (d * p^(2 * k)))⁻¹.val *
    (x : zmod (d * p^k)).val) ↑(d * p ^ k)⌋ * ⌊rat.mk ↑((c : zmod (d * p^(2 * k)))⁻¹.val *
    (x : zmod (d * p^k)).val) ↑(d * p ^ k)⌋ * (↑(d * p ^ k) *
    ⌊rat.mk ↑((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val)
    ↑(d * p ^ k)⌋) ^ x_1 * ↑((((c : zmod (d * p^(2 * k)))⁻¹.val *
    (x : zmod (d * p^k)).val : ℕ) : zmod (d * p^k)).val ^ (n - (x_1 + 1 + 1))) *
    ↑(n.choose (x_1 + 1 + 1)), _⟩,
  left, apply finset.sum_congr rfl (λ y hy, rfl),
  recover,
  apply_instance,
end

lemma nat.sub_ne_zero {n k : ℕ} (h : k < n) : n - k ≠ 0 :=
begin
  intro h',
  rw nat.sub_eq_zero_iff_le at h',
  rw ← not_lt at h',
  apply h' h,
end

lemma helper_300 [normed_algebra ℚ R] [norm_one_class R] (hd : d.coprime p)
  (hc' : c.coprime d) (hc : c.coprime p) (n : ℕ) (hn : 1 < n) : (λ k : ℕ,
  (V_def p d R m χ c n k) - (((χ * teichmuller_character_mod_p_change_level p d R m ^ n) (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime_pow_spl p c m hc⟩))) *
  (c : R)^n * (U_def p d R m χ n k) + (V_h_def p d R m χ c n k))) =ᶠ[@at_top ℕ _]
  (λ k : ℕ, (∑ (x : (zmod (d * p ^ k))ˣ), (asso_dirichlet_character
  (χ * teichmuller_character_mod_p_change_level p d R m ^ n)
  (x : zmod (d * p^m))) * (((c ^ (n - 1) : ℕ) : R) *
  (algebra_map ℚ R) ((↑d * (↑p ^ k * int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹.val *
  (x : zmod (d * p^k)).val) / (↑d * ↑p ^ k)))) ^ (n - 1) *
  (↑c * int.fract (↑(c : zmod (d * p^(2 * k)))⁻¹ * ↑x / (↑d * ↑p ^ k))))) -
  (asso_dirichlet_character (χ * teichmuller_character_mod_p_change_level p d R m ^ n) c) *
  (↑c ^ n * (U_def p d R m χ n k)) + (∑ (x : (zmod (d * p ^ k))ˣ),
  (asso_dirichlet_character (χ * teichmuller_character_mod_p_change_level p d R m ^ n)
  (x : zmod (d * p^m))) * (((c ^ (n - 1) : ℕ) : R) * (algebra_map ℚ R) (↑(n - 1 : ℕ) *
  (↑d * (↑p ^ k * (↑⌊(((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val : ℕ) : ℚ) / (↑d * ↑p ^ k)⌋ *
  (↑d * (↑p ^ k * int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val) /
  (↑d * ↑p ^ k)))) ^ (n - 1 - 1)))) * (↑c * int.fract (↑(c : zmod (d * p^(2 * k)))⁻¹ *
  (x : ℚ) / (↑d * ↑p ^ k))))) - V_h_def p d R m χ c n k) + (∑ (x : (zmod (d * p ^ k))ˣ),
  (asso_dirichlet_character (χ * teichmuller_character_mod_p_change_level p d R m ^ n)
  (x : zmod (d * p^m))) * (-↑(classical.some (exists_V_h1_3 p d R c hc' hc (n - 1) k (nat.sub_pos_of_lt hn) x) * (d * p ^ (2 * k))) *
  (algebra_map ℚ R) (↑c * int.fract (↑(c : zmod (d * p^(2 * k)))⁻¹ * ↑x / (↑d * ↑p ^ k)))) +
  ∑ (x : (zmod (d * p ^ k))ˣ), (asso_dirichlet_character
  (χ * teichmuller_character_mod_p_change_level p d R m ^ n) (x : zmod (d * p^m))) * (↑(c ^ (n - 1) : ℕ) *
  (algebra_map ℚ R) (↑(classical.some (exists_V_h1_5 p d R c (n - 1) k (nat.sub_ne_zero hn) x)) *
  (↑d * ↑p ^ (2 * k)) * (↑c * int.fract (↑(c : zmod (d * p^(2 * k)))⁻¹ * ↑x / (↑d * ↑p ^ k)))))))) :=
begin
  rw eventually_eq, rw eventually_at_top,
  refine ⟨1, λ k hk, _⟩,
  { have h3 : k ≠ 0 := ne_zero_of_lt (nat.succ_le_iff.1 hk),
    have h4 : n - 1 ≠ 0 := nat.sub_ne_zero hn,
    conv_rhs { congr, congr, skip, rw V_h_def, rw ← finset.sum_sub_distrib,
      conv { apply_congr, skip, rw sub_self, }, rw finset.sum_const_zero, },
    rw add_zero, rw add_comm, rw ← sub_sub, rw add_comm, rw ← add_sub_assoc,
    rw mul_assoc _ (↑c ^ n) (U_def p d R m χ n k),
    apply congr_arg2 _ _ _,
    { delta V_def,
      conv_lhs { congr, apply_congr, skip, rw ← nat.cast_pow,
        rw classical.some_spec (exists_V_h1_3 p d R c hc' hc _ _ (nat.sub_pos_of_lt hn) x),
        rw nat.cast_sub (le_of_lt (exists_V_h1_4 p d R c hc hc' _ _ (nat.sub_pos_of_lt hn) h3 x)),
        rw sub_eq_neg_add _ _,
        rw nat.cast_mul (c^(n - 1)) _, rw ← map_nat_cast (algebra_map ℚ R) (((c : zmod (d * p^(2 * k)))⁻¹.val *
          (x : zmod (d * p^k)).val) ^ (n - 1)),
        rw nat.cast_pow ((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val) _,
        rw classical.some_spec (exists_V_h1_5 p d R c _ _ h4 x), },
      simp_rw [← finset.sum_add_distrib, ← mul_add, smul_eq_mul],
      delta V_h_def, rw ← finset.sum_sub_distrib,
      apply finset.sum_congr,
      refl,
      { intros x hx, rw mul_assoc, rw ← mul_sub, apply congr_arg2 _ rfl _,
        simp_rw [add_mul, add_assoc],
        rw add_sub_assoc, apply congr_arg2 _ rfl _,
        rw mul_assoc, rw ← mul_sub, rw ← mul_add, congr,
        rw ← ring_hom.map_mul, rw ← ring_hom.map_add, rw ← ring_hom.map_sub,
        apply congr_arg, rw add_mul, rw add_sub_assoc, apply congr_arg2 _ rfl _, rw ← sub_mul,
        apply congr_arg2 _ _ rfl, rw add_sub_right_comm,
        conv_rhs { rw ← mul_assoc (↑d) (↑p ^ k) _, },
        convert zero_add _, rw sub_eq_zero, simp_rw [mul_assoc], }, },
    { apply congr_arg2 _ _ rfl, rw ← asso_dirichlet_character_eq_char _ _,
      rw zmod.coe_unit_of_coprime, }, },
end
.

/-@[to_additive]
lemma tendsto_list_prod' {ι α M : Type*} [topological_space M] [monoid M] [has_continuous_mul M]
  (β : ℕ → Type*) [∀ b : ℕ, preorder (β b)] {f : Π(i : ℕ), (β i) → M} --{x : filter ι} --{a : M}
  (s : Π(i : ℕ), finset (β i)) :
  ∀ (l : Π(n : ℕ), list (β n)), (∀ g : Π(n : ℕ), (β n), tendsto (λ b : ℕ, f b (g b : β b)) at_top (𝓝 1)) →
  tendsto (λ b, ((l b).map (λ c, f b c)).prod) at_top (𝓝 1) :=
| []       _ := by simp [tendsto_const_nhds]
| (f :: l) h := sorry
/-  {f : ι → α → M} {x : filter α} {a : ι → M} :
  ∀ l:list ι, (∀i∈l, tendsto (f i) x (𝓝 (a i))) →
    tendsto (λb, (l.map (λc, f c b)).prod) x (𝓝 ((l.map a).prod))
| []       _ := by simp [tendsto_const_nhds]
| (f :: l) h :=
  begin
    simp only [list.map_cons, list.prod_cons],
    exact (h f (list.mem_cons_self _ _)).mul
      (tendsto_list_prod l (assume c hc, h c (list.mem_cons_of_mem _ hc)))
  end-/

-- I think this statement can be suitably modified to be made correct using profinite systems.
@[to_additive]
lemma tendsto_finset_prod' {α M : Type*} --[preorder ι] [nonempty ι] [semilattice_sup ι]
  [topological_space M] [comm_group M] [topological_group M] (β : ℕ → Type*)
  [∀ b : ℕ, preorder (β b)]
  --(g : (Π (i : ℕ), β i → M) → M)
  {f : Π(i : ℕ), (β i) → M} --{x : filter ι} --{a : M}
  (s : Π(i : ℕ), finset (β i)) (h : ∀ (g : Π(n : ℕ), (s n)), tendsto (λ b : ℕ, f b (g b)) at_top (𝓝 1)) :
  tendsto (λ b, ∏ c in s b, f b c) at_top (𝓝 1) :=
begin
  rw tendsto_finset_prod,
--  simp at h,
--  rw tendsto.mul,
  intros U hU,
  rw mem_map, rw mem_at_top_sets,
--  simp only,
  refine ⟨0, λ b hb, _⟩,
  rw set.mem_preimage,
  have one_eq_prod : ∏ c in (s b), (1 : M) =  (1 : M), sorry,
  rw ← one_eq_prod at hU,
  rw ← nhds_mul_hom_apply at hU,

  --convert submonoid.prod_mem _ _,
  specialize h b hU,
  sorry
end -/

/-lemma zmod_units_nonarchimedean [nonarchimedean_ring R] (f : Π (n : ℕ), (zmod (d * p^n))ˣ → R)
--  (h : ∃ N, ∀ (n : ℕ) (hn : n ≥ N) (i : (zmod (d * p^n))ˣ), tendsto (f n) (pure i) (nhds 0)) :
-- accurate : (h : ∀ (n : ℕ) (i : (zmod (d * p^n))ˣ), tendsto (f n) (pure i) (nhds 0)) :
--    (h' : ∀ (s : set ℝ) (hs : s ∈ nhds (0 : ℝ)), ∃ N : ℕ, ∀ (n : ℕ) (hn : n ≥ N) (i : (zmod (d * p^n))ˣ),
--      ∥f n i∥ ∈ s) :
    --(h'' : ∀ (s : set R) (hs : s ∈ nhds (0 : R)), ∃ N : ℕ, ∀ (n : ℕ) (hn : n ≥ N), set.range (f n) ⊆ s)
    (h : ∀ (s : set R) (hs : s ∈ nhds (0 : R)), ∃ N : ℕ, ∀ (n : ℕ) (hn : n ≥ N) (i : (zmod (d * p^n))ˣ),
      f n i ∈ s) :
    tendsto (λ n : ℕ, (∑ i : (zmod (d * p^n))ˣ, f n i )) at_top (nhds 0) :=
begin
  rw tendsto_iff_norm_tendsto_zero,
  rw tendsto_at_top',
  intros s hs,
  obtain ⟨V, hV⟩ := nonarchimedean_ring.is_nonarchimedean s hs,
  obtain ⟨N, h'⟩ := h V _,
  refine ⟨N, λ b hb, _⟩,
  apply hV,
  apply sum_mem,
  intros c hc,
  specialize h' b hb c,
  apply h',
  { -- should be an easier way to do this? if not, make this a separate lemma
    rw mem_nhds_iff at *,
    rcases hs with ⟨t, ht, ot, memt⟩,
    refine ⟨t ∩ V, (set.inter_subset_right _ _), is_open.inter ot (open_add_subgroup.is_open _),
      set.mem_inter memt (add_submonoid.zero_mem V.to_add_subgroup.to_add_submonoid)⟩, }, -/

/- accurate : simp_rw tendsto_pure_left at h,
  rw tendsto_at_top',
  intros s hs,
--  cases h with N h,
  refine ⟨0, λ b hb, _⟩,
  obtain ⟨V, hV⟩ := nonarchimedean_ring.is_nonarchimedean s hs,
  apply hV,
  apply sum_mem,
  intros c hc,
  specialize h b c V _,
  { -- should be an easier way to do this? if not, make this a separate lemma
    rw mem_nhds_iff at *,
    rcases hs with ⟨t, ht, ot, memt⟩,
    refine ⟨t ∩ V, (set.inter_subset_right _ _), is_open.inter ot (open_add_subgroup.is_open _),
      set.mem_inter memt (add_submonoid.zero_mem V.to_add_subgroup.to_add_submonoid)⟩, },
  apply h, -/
--end

--variable [nonarchimedean_ring R]

/-
--Note : tried to remove the sup condition as above but I dont know if that will work ou, probably
-- not, the dependency causes problems as the at_top is not the same as the naturals and there does not
-- exist a natural preorder on zmod n.
lemma na_tendsto (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (f : Π (n : ℕ), (zmod (d * p^n))ˣ → R)
  (h : tendsto (λ n : ℕ, ⨆ (i : (zmod (d * p^n))ˣ), ∥f n i∥) at_top (nhds 0)) :
  tendsto (λ n : ℕ, (∑ i : (zmod (d * p^n))ˣ, f n i )) at_top (nhds 0) :=
begin
  apply summable.tendsto_at_top_zero,
  rw tendsto_pi_nhds,
  delta summable,
  simp only,
  delta has_sum, simp,
  refine ⟨0, _⟩,
  intros e he,
  rw mem_map,
  simp,
  rw mem_nhds_iff at he,
  apply summable.tendsto_at_top_zero,
  rw ennreal.tendsto_at_top_zero_of_tsum_ne_top,
  rw metric.tendsto_at_top at *,
  intros ε hε, specialize h ε hε, simp_rw dist_zero_right _ at *,
  cases h with N h,
  refine ⟨N, λ n hn, _⟩,
  specialize h n hn,
  apply lt_of_le_of_lt (na (d * p^n) (f n)) _,
  convert h, rw real.norm_eq_abs,
  symmetry,
  rw abs_eq_self,
  apply le_csupr_of_le _ _ _,
  { sorry, },
  { exact 1, },
  { apply norm_nonneg _, },
end -/

lemma helps (f : Π (n : ℕ), (zmod (d * p^n))ˣ → R)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥) (k : ℕ → ℝ)
  (h : ∀ (n : ℕ) (i : (zmod (d * p^n))ˣ), ∥f n i∥ ≤ k n) (n : ℕ) :
  ∥∑ i : (zmod (d * p^n))ˣ, f n i∥ ≤ k n :=
begin
  apply le_trans (na (d * p^n) (f n)) _,
  apply cSup_le _ _,
  { exact set.range_nonempty (λ (i : (zmod (d * p ^ n))ˣ), ∥f n i∥), },
  { intros b hb,
    cases hb with y hy,
    rw ← hy,
    apply h, },
end

lemma int.exists_int_eq_fract_mul_self (a : ℕ) {b : ℕ} (hb : b ≠ 0) : ∃ z : ℤ, (z : ℚ) = int.fract (a / b : ℚ) * b :=
begin
  obtain ⟨z, hz⟩ := int.fract_mul_nat (a / b : ℚ) b,
  refine ⟨z, _⟩,
  have : (b : ℚ) ≠ 0,
  { norm_cast, apply hb, },
  simp_rw [div_mul_cancel (a : ℚ) this] at hz,
  rw ← hz,
  rw sub_eq_self,
  change int.fract ((a : ℤ) : ℚ) = 0, rw int.fract_coe,
end

--variable (p)

lemma norm_int_eq_padic_int_norm [norm_one_class R] (z : ℤ) : ∥(z : R)∥ = ∥(z : ℤ_[p])∥ :=
begin
  rw padic_int.norm_int_cast_eq_padic_norm,
  rw ← norm_algebra_map' R (z : ℚ_[p]),
  rw ring_hom.map_int_cast,
end

lemma norm_prime_lt_one [norm_one_class R] : ∥(p : R)∥ < 1 :=
begin
  change ∥((p : ℤ) : R)∥ < 1,
  rw norm_int_eq_padic_int_norm p R,
  rw padic_int.norm_lt_one_iff_dvd _,
  simp,
end

-- if I remove hd it cannot recognize p
lemma norm_int_le_one [normed_algebra ℚ R] [norm_one_class R] (hd : d.coprime p) (z : ℤ) : ∥(z : R)∥ ≤ 1 :=
begin
  simp_rw [← ring_hom.map_int_cast (algebra_map ℚ_[p] R), ← padic_int.coe_coe_int,
    norm_algebra_map, norm_one_class.norm_one, mul_one],
  apply padic_int.norm_le_one,
end

lemma helper_3 [normed_algebra ℚ R] [norm_one_class R] (k : ℕ) (x : (zmod (d * p^k))ˣ) :
  int.fract (((((c : zmod (d * p^(2 * k))))⁻¹.val *
  (x : zmod (d * p^k)).val : ℕ)) / (d * p^k) : ℚ) = int.fract (((((c : zmod (d * p^(2 * k))))⁻¹.val *
  (x : zmod (d * p^k)).val : zmod(d * p^k))).val / (d * p^k) : ℚ) :=
begin
  rw ← nat.cast_pow,
  rw ← nat.cast_mul d (p^k),
  rw fract_eq_of_zmod_eq _ ((((c : zmod (d * p^(2 * k)))⁻¹.val *
    (x : zmod (d * p^k)).val) : ℕ) : zmod (d * p^k)).val (d * p^k) _,
  rw ← nat.cast_mul,
  rw zmod.nat_cast_val ((((c : zmod (d * p^(2 * k)))⁻¹.val *
        (x : zmod (d * p^k)).val) : ℕ) : zmod (d * p^k)),
  rw zmod.cast_id,
end
--also used in the major lemma above

lemma helper_4 [normed_algebra ℚ R] [norm_one_class R] (k : ℕ) (x : (zmod (d * p^k))ˣ) :
  int.fract (((((((c : zmod (d * p^(2 * k))))⁻¹ : zmod (d * p^(2 * k))) : ℚ) *
  x : ℚ)) / (d * p^k) : ℚ) = int.fract (((((c : zmod (d * p^(2 * k))))⁻¹.val *
  (x : zmod (d * p^k)).val : zmod(d * p^k))).val / (d * p^k) : ℚ) :=
begin
  convert helper_3 p d R c k x,
  rw nat.cast_mul,
  rw zmod.nat_cast_val _,
  rw zmod.nat_cast_val _,
  simp only [coe_coe],
  any_goals { apply imp p d _, },
end

lemma helper_5 (a b c : R) : a * b * c = a * c * b := by ring

lemma helper_6 {n : ℕ} [fact (0 < n)] (x : (zmod n)ˣ) : (x : ℚ) = ((x : zmod n).val : ℚ) :=
begin
  simp,
end

lemma helper_7 {k : ℕ} (hc' : c.coprime d) (hc : c.coprime p) (a₁ a₂ : (zmod (d * p^k))ˣ)
  (h : (((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k))) : zmod (d * p^k)) *
  (a₁ : zmod (d * p^k)) = (((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k))) : zmod (d * p^k)) *
  (a₂ : zmod (d * p^k))) : a₁ = a₂ :=
begin
  rw units.ext_iff, rw zmod.cast_inv at h, rw zmod.cast_nat_cast _ at h,
  have := congr_arg2 has_mul.mul (eq.refl (c : zmod (d * p^k))) h,
  simp_rw ← mul_assoc at this,
  rw zmod.mul_inv_of_unit _ _ at this, simp_rw one_mul at this,
  exact this,
  { apply is_unit_of_is_coprime dvd_rfl, rw nat.is_coprime_iff_coprime,
    apply nat.coprime_mul_pow k hc' hc, },
  swap, { refine zmod.char_p _, },
  any_goals { apply mul_dvd_mul_left d (pow_dvd_pow p (nat.le_mul_of_pos_left two_pos)), },
  { apply nat.coprime_mul_pow _ hc' hc, },
end

lemma zmod.inv_is_unit_of_is_unit {n : ℕ} {u : zmod n} (h : is_unit u) : is_unit u⁻¹ :=
begin
  have h' := is_unit_iff_dvd_one.1 h,
  cases h' with k h',
  rw is_unit_iff_dvd_one,
  refine ⟨u, _⟩,
  rw zmod.inv_mul_of_unit u h,
end

lemma zmod.is_unit_mul {a b g : ℕ} (n : ℕ) (h1 : g.coprime a) (h2 : g.coprime b) :
  is_unit (g : zmod (a * b^n)) :=
is_unit_of_is_coprime dvd_rfl (nat.is_coprime_iff_coprime.2 (nat.coprime_mul_pow n h1 h2))

lemma helper_301 [normed_algebra ℚ R] [norm_one_class R] (hd : d.coprime p)
  (hc' : c.coprime d) (hc : c.coprime p) (n : ℕ) (hn : 1 < n) : (λ (x : ℕ), ∑ (x_1 : (zmod (d * p ^ x))ˣ),
  (asso_dirichlet_character (χ * teichmuller_character_mod_p_change_level p d R m ^ n)) ↑x_1 *
  (↑(c ^ (n - 1) : ℕ) * (algebra_map ℚ R) ((↑d * (↑p ^ x *
  int.fract (↑((c : zmod (d * p ^ (2 * x)))⁻¹.val * (x_1 : zmod (d * p ^x)).val : ℕ) / (↑d * ↑p ^ x)))) ^ (n - 1) *
  (↑c * int.fract ((((c : zmod (d * p ^ (2 * x)))⁻¹ : zmod (d * p ^ (2 * x))) : ℚ) * (x_1 : ℚ) / (↑d * ↑p ^ x))))) -
  (asso_dirichlet_character (χ * teichmuller_character_mod_p_change_level p d R m ^ n)) ↑c *
  (↑c ^ n * U_def p d R m χ n x)) =ᶠ[at_top] 0 :=
begin
  rw eventually_eq,
  rw eventually_at_top,
  refine ⟨m, λ k hk, _⟩,
  have h' : d * p ^ k ∣ d * p ^ (2 * k) :=
    mul_dvd_mul_left d (pow_dvd_pow p (nat.le_mul_of_pos_left two_pos)),
  have h1 : (d * p^k : ℚ) ≠ 0,
  { norm_cast, apply nat.mul_ne_zero (ne_zero_of_lt (fact.out _)) _,
    exact 0, apply_instance, apply pow_ne_zero k (nat.prime.ne_zero (fact.out _)), apply_instance, },
  have h2 : d * p^m ∣ d * p^k := mul_dvd_mul_left d (pow_dvd_pow p hk),
  rw pi.zero_apply, rw sub_eq_zero, delta U_def,
  simp_rw [helper_3 p d R, helper_4 p d R, finset.mul_sum, ← mul_assoc, smul_eq_mul, ← mul_assoc],
  apply finset.sum_bij,
  { intros a ha, apply finset.mem_univ _, },
  swap 4, { intros a ha, apply is_unit.unit,
    swap, { exact (c : zmod (d * p^(2 * k)))⁻¹.val * (a : zmod (d * p^k)).val, },
    apply is_unit.mul _ _,
    { rw zmod.nat_cast_val, rw zmod.cast_inv _ _ _ (nat.coprime_mul_pow _ hc' hc) h',
      rw zmod.cast_nat_cast h', apply zmod.inv_is_unit_of_is_unit,
      apply zmod.is_unit_mul _ hc' hc,
      { refine zmod.char_p _, }, },
    { rw zmod.nat_cast_val, rw zmod.cast_id, apply units.is_unit a, }, },
  { intros a ha, conv_rhs { rw helper_5 R _ (c^n : R) _, rw mul_assoc, rw mul_assoc, },
    rw mul_assoc, apply congr_arg2,
    { simp_rw ← units.coe_hom_apply,
      rw ← monoid_hom.map_mul _, congr,
      --rw units.ext_iff,
      simp only [units.coe_hom_apply, zmod.nat_cast_val, zmod.cast_id', id.def,
        ring_hom.to_monoid_hom_eq_coe, units.coe_map,
        ring_hom.coe_monoid_hom, zmod.cast_hom_apply, units.coe_mul, zmod.coe_unit_of_coprime],
      rw coe_coe (is_unit.unit _), rw is_unit.unit_spec,
      rw zmod.cast_mul h2, rw zmod.cast_inv _ _ _ _ h',
      rw zmod.cast_nat_cast h' _, rw zmod.cast_inv _ _ _ _ h2, rw zmod.cast_nat_cast h2 _,
      rw ← mul_assoc, rw zmod.mul_inv_of_unit _, rw one_mul,
      rw coe_coe,
      any_goals { refine zmod.char_p _, },
      any_goals { apply nat.coprime.mul_right hc' (nat.coprime_pow_spl p c _ hc), },
      { apply zmod.is_unit_mul _ hc' hc, }, },
    { rw ring_hom.map_mul, rw fract_eq_self _, rw mul_div_cancel' _,
      rw ← mul_assoc, rw ring_hom.map_mul, rw ← mul_assoc, rw map_nat_cast,
      rw helper_5 R _ _ (c : R), rw mul_assoc, apply congr_arg2,
      { rw nat.cast_pow, rw ← pow_succ', rw nat.sub_add_cancel _, apply le_of_lt hn, }, --might need change
      { simp_rw [helper_6],
        rw fract_eq_self, rw ← nat.cast_pow, rw map_nat_cast, congr,
        { rw nat.cast_pow, congr, },
        { apply (zero_le_and_lt_one p d _ _).1, },
        { apply (zero_le_and_lt_one p d _ _).2, }, },
      { apply h1, },
      { apply (zero_le_and_lt_one p d _ _).2, },
      { apply (zero_le_and_lt_one p d _ _).1, }, }, },
  { intros a₁ a₂ ha₁ ha₂ h,
    simp only at h, rw units.ext_iff at h,
    rw is_unit.unit_spec at h, rw is_unit.unit_spec at h,
    simp_rw [zmod.nat_cast_val, zmod.cast_id] at h,
    apply helper_7 p d c hc' hc _ _ h, },
  { intros b hb, simp_rw [units.ext_iff, is_unit.unit_spec],
    refine ⟨is_unit.unit _, _, _⟩,
    { exact c * (b : zmod (d * p^k)), },
    { apply is_unit.mul _ (units.is_unit _), apply zmod.is_unit_mul _ hc' hc, },
    { apply finset.mem_univ _, },
    { rw is_unit.unit_spec, simp_rw zmod.nat_cast_val, rw zmod.cast_id, rw ← mul_assoc,
      rw zmod.cast_inv _ _ _ _ h', rw zmod.cast_nat_cast h' _, rw zmod.inv_mul_of_unit _, rw one_mul,
      { apply zmod.is_unit_mul _ hc' hc, },
      { refine zmod.char_p _, },
      { apply nat.coprime.mul_right hc' (nat.coprime_pow_spl p c (2 * k) hc), }, }, },
end

lemma V_h1 [normed_algebra ℚ R] [norm_one_class R] (hd : d.coprime p)
  (hc' : c.coprime d) (hc : c.coprime p)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (n : ℕ) (hn : 1 < n) :
  filter.tendsto (λ (x : ℕ), V_def p d R m χ c n x -
  (↑((χ * teichmuller_character_mod_p_change_level p d R m ^ n) (zmod.unit_of_coprime c
  (nat.coprime_mul_iff_right.mpr ⟨hc', p.coprime_pow_spl c m hc⟩))) *
  ↑c ^ n * U_def p d R m χ n x + V_h_def p d R m χ c n x)) filter.at_top (nhds 0) :=
begin
  have mul_ne_zero' : ∀ n, d * p^n ≠ 0,
  { intro n, apply ne_zero_of_lt (mul_prime_pow_pos p d n), },
  rw filter.tendsto_congr' (helper_300 p d R m χ c hd hc' hc n hn),
  conv { congr, skip, skip, congr, rw ← add_zero (0 : R), rw ← add_zero ((0 : R) + 0), },
  apply tendsto.add, apply tendsto.add,
  { convert tendsto.congr' (helper_301 p d R m χ c hd hc' hc n hn).symm _,
      -- why was any of this needed?
    { ext, congr, },
    { apply tendsto_const_nhds, }, },
  { delta V_h_def,
    convert tendsto_const_nhds,
    ext, convert sub_self _, },
  { simp_rw [← finset.sum_add_distrib, ← mul_add, ring_hom.map_mul, ← mul_assoc, ← add_mul,
      mul_assoc _ (algebra_map ℚ R (d : ℚ)) _, ← ring_hom.map_mul _ (d : ℚ) _, ← nat.cast_pow,
      ← nat.cast_mul d _, map_nat_cast, mul_assoc _ d _, nat.cast_mul _ (d * p^(2 * _)),
      mul_comm _ ((d * p^(2 * _) : ℕ) : R), neg_mul_eq_mul_neg, ← mul_add, mul_assoc _ (c : R) _,
      mul_assoc, mul_comm ((d * p^(2 * _) : ℕ) : R), ← mul_assoc _ _ ((d * p^(2 * _) : ℕ) : R)],
    rw tendsto_zero_iff_norm_tendsto_zero,
    rw ← tendsto_zero_iff_norm_tendsto_zero,
    have : tendsto (λ n : ℕ, (p^n : R)) at_top (nhds 0),
    { apply tendsto_pow_at_top_nhds_0_of_norm_lt_1,
      apply norm_prime_lt_one, },
    rw tendsto_iff_norm_tendsto_zero at this,
    have h1 := tendsto.mul_const (dirichlet_character.bound (χ *
      teichmuller_character_mod_p_change_level p d R m ^ n)) this,
    rw [zero_mul] at h1,
    apply squeeze_zero_norm _ h1,
    simp only [sub_zero], intro z,
    convert helps p d R _ na _ _ z,
    intros e x,
    simp_rw [two_mul e, pow_add, ← mul_assoc d (p^e) (p^e), nat.cast_mul (d * p^e) (p^e),
      ← mul_assoc _ (↑(d * p ^ e)) _, nat.cast_pow p e, mul_comm _ (↑p^e)],
    apply le_trans (norm_mul_le _ _) _,
    rw mul_le_mul_left _,
    { simp_rw [mul_assoc _ _ (↑(d * p ^ e))],
      apply le_trans (norm_mul_le _ _) _,
      rw ← mul_one (dirichlet_character.bound _),
      apply mul_le_mul (le_of_lt (dirichlet_character.lt_bound _ _)) _ (norm_nonneg _)
        (le_of_lt (dirichlet_character.bound_pos _)),
      simp_rw [← map_nat_cast (algebra_map ℚ R) (d * p^e), ← ring_hom.map_mul],
      obtain ⟨z, hz⟩ := int.exists_int_eq_fract_mul_self
        ((((c : zmod (d * p^(2 * e)))⁻¹).val * (x : zmod (d * p^e)).val )) (mul_ne_zero' e),
      { simp_rw [coe_coe x, ← zmod.nat_cast_val, ← nat.cast_mul],
        conv { congr, congr, congr, skip, rw [← hz], },
        simp_rw [ring_hom.map_int_cast, ← int.cast_coe_nat, ← int.cast_neg, ← int.cast_mul,
          ← int.cast_add, ← int.cast_mul],
        apply norm_int_le_one p d R hd, }, },
    { rw norm_pos_iff, norm_cast, apply pow_ne_zero _ (nat.prime.ne_zero _), apply fact.out, }, },
end

@[to_additive]
lemma filter.tendsto.one_mul_one {α M : Type*} [topological_space M] [monoid M]
  [has_continuous_mul M] {f g : α → M} {x : filter α} (hf : tendsto f x (𝓝 1))
  (hg : tendsto g x (𝓝 1)) : tendsto (λx, f x * g x) x (𝓝 1) :=
by { convert tendsto.mul hf hg, rw mul_one, }

lemma V_h2_1 [normed_algebra ℚ R] [norm_one_class R] (hd : d.coprime p) (hc' : c.coprime d)
  (hc : c.coprime p) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  (n : ℕ) (hn : 1 < n) (hχ : χ.is_even) :
  (λ (x : ℕ), ∑ (x_1 : (zmod (d * p ^ x))ˣ), (asso_dirichlet_character
  (χ * teichmuller_character_mod_p_change_level p d R m ^ n)) ↑x_1 * (↑(n - 1 : ℕ) * ↑(c ^ n : ℕ) *
  (algebra_map ℚ R) (↑d * ↑p ^ x * int.fract (↑((c : zmod (d * p^(2 * x)))⁻¹ : zmod (d * p^(2 * x))) *
  ↑x_1 / ↑(d * p ^ x))) ^ n * (algebra_map ℚ R) (1 / (↑d * ↑p ^ x))) - ↑(n - 1 : ℕ) *
  ((asso_dirichlet_character (χ * teichmuller_character_mod_p_change_level p d R m ^ n)) ↑c *
  (algebra_map ℚ R) (↑c ^ n)) * U_def p d R m χ n x) =ᶠ[at_top] λ (b : ℕ), 0 :=
begin
  apply eventually_eq_iff_sub.1,
  rw eventually_eq, rw eventually_at_top,
  refine ⟨m, λ k hk, _⟩, delta U_def, rw finset.mul_sum,
  have h1 : (d * p^k : ℚ) ≠ 0,
  { norm_cast, apply ne_zero_of_lt, refine fact_iff.1 (imp p d k), },
  have h2 : d * p^m ∣ d * p^k := mul_dvd_mul_left d (pow_dvd_pow p hk),
  have h5 : ∀ (x : (zmod (d * p^k))ˣ), (x : ℚ) = ((x : zmod (d * p^k)) : ℚ) := coe_coe,
  have h' : d * p ^ k ∣ d * p ^ (2 * k) :=
    mul_dvd_mul_left d (pow_dvd_pow p (nat.le_mul_of_pos_left two_pos)),
  apply finset.sum_bij,
  { intros a ha, apply finset.mem_univ _, },
  swap 4, { intros a ha, apply is_unit.unit,
   swap, { exact (c : zmod (d * p^(2 * k)))⁻¹.val * (a : zmod (d * p^k)).val, },
   -- maybe make a separate lemma?
   apply is_unit.mul _ _,
  { rw zmod.nat_cast_val, rw zmod.cast_inv _ _ _ (nat.coprime_mul_pow _ hc' hc) h',
    rw zmod.cast_nat_cast h', apply zmod.inv_is_unit_of_is_unit,
    apply zmod.is_unit_mul _ hc' hc,
    { refine zmod.char_p _, }, },
  { rw zmod.nat_cast_val, rw zmod.cast_id, apply units.is_unit a, }, },
  { intros a ha,
    --rw ← asso_dirichlet_character_eq_char, rw ← asso_dirichlet_character_eq_char,
    rw smul_eq_mul, rw mul_comm _ ((algebra_map ℚ R) (c^n : ℚ)),
    rw ← mul_assoc ((n - 1 : ℕ) : R) _ _,
    rw mul_assoc (((n - 1 : ℕ) : R) * (algebra_map ℚ R) (c^n : ℚ)) _ _,
    conv_rhs { congr, skip, conv { congr, skip, rw mul_assoc, }, rw ← mul_assoc, },
    conv_rhs { rw ← mul_assoc, rw helper_5, rw mul_comm, }, --rw ← asso_dirichlet_character_eq_char, },
    apply congr_arg2,
    { --rw ← asso_dirichlet_character_eq_char,
      -- rw ← dirichlet_character.asso_dirichlet_character_mul,
      --simp_rw ← units.coe_hom_apply,
      rw ← monoid_hom.map_mul (asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m ^ n))) _ _,
      --rw ← monoid_hom.map_mul (units.coe_hom R), rw ← monoid_hom.map_mul,
      congr,
      --rw units.ext_iff,
      simp only [units.coe_hom_apply, zmod.nat_cast_val, zmod.cast_id', id.def,
        ring_hom.to_monoid_hom_eq_coe, units.coe_map,
        ring_hom.coe_monoid_hom, zmod.cast_hom_apply, units.coe_mul, zmod.coe_unit_of_coprime],
      rw coe_coe (is_unit.unit _),
      rw is_unit.unit_spec, rw zmod.cast_mul h2, rw zmod.cast_inv _ _ _ _ h',
      rw zmod.cast_nat_cast h' _, rw zmod.cast_inv _ _ _ _ h2, rw zmod.cast_nat_cast h2 _,
      rw ← mul_assoc, rw zmod.mul_inv_of_unit _, rw one_mul,
      { rw coe_coe, },
      any_goals { refine zmod.char_p _, },
      -- { apply nat.coprime.mul_right hc' (nat.coprime_pow_spl p c _ hc), },
      any_goals { apply nat.coprime.mul_right hc' (nat.coprime_pow_spl p c _ hc), },
      { apply zmod.is_unit_mul _ hc' hc, }, },
    { --rw ring_hom.map_mul,
      rw nat.cast_mul d _, rw nat.cast_pow p _,
      rw helper_4 p d R c k a, rw fract_eq_self _, rw mul_div_cancel' _,
      simp_rw [mul_assoc], apply congr_arg2 _ rfl _, rw ← nat.cast_pow c, rw map_nat_cast,
      rw map_nat_cast, apply congr_arg2 _ rfl _, rw is_unit.unit_spec,
      simp_rw [← map_nat_cast (algebra_map ℚ R), ← ring_hom.map_pow, ← ring_hom.map_mul, mul_one_div],
      apply congr_arg, rw h5,
      simp_rw is_unit.unit_spec, rw ← nat.cast_pow p _, rw ← nat.cast_mul d _, rw fract_eq_val,
      rw mul_div, rw ← pow_succ',
      rw nat.sub_one, rw nat.add_one, rw nat.succ_pred_eq_of_pos _,
      { apply lt_trans _ hn, apply nat.zero_lt_one, },
      { apply h1, },
--      rw helper_5 R _ _ (c : R), rw mul_assoc, apply congr_arg2,
      -- { rw nat.cast_mul, rw nat.cast_pow, apply h1, }, --might need change
      -- { apply h1, },
        -- { simp_rw [helper_6],
        --   rw fract_eq_self, rw ← nat.cast_pow, rw map_nat_cast, congr,
        --   { rw nat.cast_pow, congr, },
        --   { apply (zero_le_and_lt_one p d _ _).1, },
        --   { apply (zero_le_and_lt_one p d _ _).2, }, },
        -- { apply h1, },
      { apply (zero_le_and_lt_one p d _ _).2, },
      { apply (zero_le_and_lt_one p d _ _).1, }, }, },
  { intros a₁ a₂ ha₁ ha₂ h,
    simp only at h, rw units.ext_iff at h,
    rw is_unit.unit_spec at h, rw is_unit.unit_spec at h,
    simp_rw [zmod.nat_cast_val, zmod.cast_id] at h,
    apply helper_7 p d c hc' hc _ _ h, },
  { intros b hb, simp_rw [units.ext_iff, is_unit.unit_spec],
    refine ⟨is_unit.unit _, _, _⟩,
    { exact c * (b : zmod (d * p^k)), },
    { apply is_unit.mul (zmod.is_unit_mul _ hc' hc) (units.is_unit _), },
    { apply finset.mem_univ _, },
    { rw is_unit.unit_spec, simp_rw zmod.nat_cast_val, rw zmod.cast_id, rw ← mul_assoc,
      rw zmod.cast_inv _ _ _ _ h', rw zmod.cast_nat_cast h' _, rw zmod.inv_mul_of_unit _, rw one_mul,
      { apply zmod.is_unit_mul _ hc' hc, },
      { refine zmod.char_p _, },
      { apply nat.coprime.mul_right hc' (nat.coprime_pow_spl p c (2 * k) hc), }, }, },
end

lemma helper_V_h2_2 [normed_algebra ℚ R] [norm_one_class R] (hd : d.coprime p) (hc' : c.coprime d)
  (hc : c.coprime p) (hp : 2 < p)  (n : ℕ) (hn : 1 < n) :
  (λ x : ℕ, (algebra_map ℚ R) ↑(n - 1 : ℕ) * (U_def p d R m χ n x)) =ᶠ[at_top]
  (λ k : ℕ, ∑ (x : (zmod (d * p ^ k))ˣ), (algebra_map ℚ R) ↑(n - 1 : ℕ) *
  (asso_dirichlet_character (χ * teichmuller_character_mod_p_change_level p d R m ^ n) x) *
  (algebra_map ℚ R) ((-↑(classical.some ((exists_V_h1_3 p d R c hc' hc n k (lt_trans zero_lt_one hn) x)) * (d * p ^ (2 * k)) : ℕ) +
  ↑(c ^ n : ℕ) * (↑(classical.some (exists_V_h1_5 p d R c n k (ne_zero_of_lt hn) x)) *
  (↑d * ↑p ^ (2 * k)) + ↑n * (↑d * ↑p ^ k) * ↑⌊(((c : zmod (d * p^(2 * k)))⁻¹.val *
  (x : zmod (d * p^k)).val) : ℚ) / (↑d * ↑p ^ k)⌋ * (↑d * ↑p ^ k *
  int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val) / (↑d * ↑p ^ k))) ^ (n - 1) +
  (↑d * ↑p ^ k * int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val) / (↑d * ↑p ^ k))) ^ n))
  / (↑d * ↑p ^ k))) :=
begin
  rw eventually_eq, rw eventually_at_top,
  refine ⟨1, λ k hk, _⟩,
  have h2 : ∀ (k : ℕ) (x : (zmod (d * p^k))ˣ), (x : ℚ) = ((x : zmod (d * p^k)).val : ℚ),
  { simp only [coe_coe, zmod.nat_cast_val, eq_self_iff_true, forall_2_true_iff], },
  delta U_def,
  rw finset.mul_sum, simp_rw smul_eq_mul,
  conv_lhs { apply_congr, skip, rw h2,
  rw fract_eq_self (zero_le_and_lt_one p d k x).1 (zero_le_and_lt_one p d k x).2,
  rw mul_assoc, rw ← map_nat_cast (algebra_map ℚ R) _, rw ← ring_hom.map_pow,
  rw ← ring_hom.map_mul, rw mul_div _ _ (d * p^k : ℚ), rw ← pow_succ', rw ← mul_assoc,
  rw nat.sub_add_cancel (le_of_lt hn), conv { congr, congr, skip, skip, rw ← nat.cast_pow,
  rw classical.some_spec (exists_V_h1_3 p d R c hc' hc _ _ (lt_trans zero_lt_one hn) x), },
  rw nat.cast_sub (le_of_lt (exists_V_h1_4 p d R c hc hc' _ _ (lt_trans zero_lt_one hn) (ne_zero_of_lt hk) x)),
  rw sub_eq_neg_add _ _, rw nat.cast_mul (c^n) _,
  rw nat.cast_pow ((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val) _,
  rw classical.some_spec (exists_V_h1_5 p d R c _ _ (ne_zero_of_lt hn) x),
  --rw ← zmod.nat_cast_val, rw h2,
  rw nat.cast_mul, }, --rw nat.cast_pow p,
  --rw ← nat.cast_mul _ (x : zmod (d * p^k)).val, rw ← ring_hom.map_pow, },
  simp_rw [add_div, ring_hom.map_add, mul_add, add_div, ring_hom.map_add, mul_add,
   finset.sum_add_distrib, ← add_assoc],
  congr,
  { simp_rw nat.cast_mul _ (d * p ^ (2 * k)), },
  --helper_13],
  { ext, congr, apply congr_arg, congr, rw ← nat.cast_mul _ (x : zmod (d * p^k)).val, },
end

lemma helper_13 (a b c d e f : R) : a + b + c + (d - e - f) = a + b + (c - f) + (d - e) := by ring

lemma V_h2_2 [normed_algebra ℚ R] [norm_one_class R] (hd : d.coprime p) (hc' : c.coprime d)
  (hc : c.coprime p) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  (na' : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (n : ℕ) (hn : 1 < n) : tendsto (λ (x : ℕ), (algebra_map ℚ R) ↑(n - 1 : ℕ) * U_def p d R m χ n x -
  ∑ (x_1 : (zmod (d * p ^ x))ˣ), (asso_dirichlet_character
  (χ * teichmuller_character_mod_p_change_level p d R m ^ n)) ↑x_1 * (↑(n - 1 : ℕ) * ↑(c ^ n : ℕ) *
  (algebra_map ℚ R) (↑d * ↑p ^ x * int.fract (↑((c : zmod (d * p^(2 * x)))⁻¹ : zmod (d * p^(2 * x))) *
  ↑x_1 / ↑(d * p ^ x : ℕ))) ^ n * (algebra_map ℚ R) (1 / (↑d * ↑p ^ x))) -
  (algebra_map ℚ R) ↑n * V_h_def p d R m χ c n x) at_top (𝓝 0) :=
begin
  simp_rw sub_sub,
  apply (tendsto_congr' (eventually_eq.sub (helper_V_h2_2 p d R m χ c hd hc' hc hp n hn)
    eventually_eq.rfl)).2,
  simp_rw [← sub_sub, mul_add, add_div, ring_hom.map_add, mul_add, finset.sum_add_distrib, ← add_assoc,
    ← add_sub, helper_13],
  apply filter.tendsto.zero_add_zero, apply filter.tendsto.zero_add_zero,
  { simp_rw [← finset.sum_add_distrib, ← mul_add],
    --maybe make a lemma out of this since it is used again?
    have : tendsto (λ n : ℕ, (p^n : R)) at_top (nhds 0),
    { apply tendsto_pow_at_top_nhds_0_of_norm_lt_1,
      apply norm_prime_lt_one, },
    rw tendsto_iff_norm_tendsto_zero at this,
    have hbp := tendsto.mul_const (dirichlet_character.bound (χ *
      teichmuller_character_mod_p_change_level p d R m ^ n)) this,
    rw [zero_mul] at hbp,
    apply squeeze_zero_norm _ hbp,
    simp only [sub_zero], intro z,
    convert helps p d R _ na' _ _ z,
    intros e x,
    rw [← ring_hom.map_add, nat.cast_mul, ← neg_mul, ← mul_div, ← mul_assoc, ← mul_div,
      nat.cast_mul _ (p ^ (2 * e)), nat.cast_pow p, ← add_mul],
    simp_rw [two_mul e, pow_add, ← mul_assoc (d : ℚ) (↑p^e) (↑p^e), mul_comm (↑d * ↑p ^ e) _,
      ← mul_div _ (↑d * ↑p ^ e) _],
    apply le_trans (norm_mul_le _ _) _,
    rw mul_comm (∥↑p ^ e∥) _,
    apply mul_le_mul _ _ (norm_nonneg _) (le_of_lt (dirichlet_character.bound_pos _)),
    { apply le_trans (norm_mul_le _ _) _,
      rw ← one_mul (dirichlet_character.bound _),
      apply mul_le_mul _ (le_of_lt (dirichlet_character.lt_bound
        (χ * teichmuller_character_mod_p_change_level p d R m ^ n) _)) (norm_nonneg _) zero_le_one,
      simp_rw [ring_hom.map_int_cast, ← int.cast_coe_nat, ring_hom.map_int_cast],
      apply norm_int_le_one p d R hd, },
    { rw [← mul_assoc, ring_hom.map_mul, div_self _, ring_hom.map_one, mul_one, ring_hom.map_mul],
      simp_rw [← nat.cast_pow p, map_nat_cast],
      apply le_trans (norm_mul_le _ _) _,
      rw mul_le_iff_le_one_left _,
      { simp_rw [← int.cast_coe_nat, ← int.cast_neg, ← int.cast_mul, ← int.cast_add,
          ring_hom.map_int_cast],
        apply norm_int_le_one p d R hd, },
      { rw norm_pos_iff, norm_cast, apply pow_ne_zero _ (nat.prime.ne_zero _), apply fact.out, },
      { norm_cast, apply ne_zero_of_lt, refine fact_iff.1 (imp p d e), }, }, },
  { convert tendsto_const_nhds, ext k, rw sub_eq_zero, delta V_h_def, rw finset.mul_sum,
    have h1 : (d * p^k : ℚ) ≠ 0,
    { norm_cast, apply ne_zero_of_lt, refine fact_iff.1 (imp p d k), },
    have h2 : ∀ (x : (zmod (d * p^k))ˣ), (x : ℚ) = ((x : zmod (d * p^k)).val : ℚ) :=
      λ x, by { rw [zmod.nat_cast_val, coe_coe], },
    apply finset.sum_congr _ (λ x hx, _),
    { convert refl _, apply_instance, },
    rw map_nat_cast _ n, rw mul_comm (n : R) _,
    rw mul_assoc _ _ (n : R), rw mul_comm ((algebra_map ℚ R) ↑(n - 1)) _, rw mul_assoc,
    apply congr_arg2 _ rfl _, rw ← nat.pred_eq_sub_one, rw ← nat.succ_pred_eq_of_pos (nat.lt_pred_iff.2 hn),
    rw pow_succ _ (n.pred.pred),
    have : 0 < n := lt_trans zero_lt_one hn,
    rw ← nat.succ_pred_eq_of_pos this, rw pow_succ' c n.pred, rw nat.cast_mul _ c,
    rw nat.succ_pred_eq_of_pos this, rw nat.succ_pred_eq_of_pos (nat.lt_pred_iff.2 hn),
    simp_rw [← mul_assoc (d : ℚ) _ _, ← nat.cast_pow p _, ← nat.cast_mul d _,
      mul_pow, ring_hom.map_mul, map_nat_cast, nat.pred_eq_sub_one],
    rw ← mul_assoc, rw ← mul_assoc ((c^(n - 1) : ℕ) : R) (((n - 1 : ℕ) : R) * _) _,
    rw ← mul_assoc ((c^(n - 1) : ℕ) : R) ((n - 1 : ℕ) : R) _,
    rw mul_comm _ ((n - 1 : ℕ) : R), rw mul_assoc ((n - 1 : ℕ) : R) _ _,
    rw mul_assoc ((n - 1 : ℕ) : R) _ _, rw mul_assoc ((n - 1 : ℕ) : R) _ _,
    apply congr_arg2 _ rfl _, rw ← mul_div,
    simp_rw [ring_hom.map_mul, map_nat_cast, mul_assoc], apply congr_arg2 _ rfl _,
    rw ← mul_div ((d * p ^ k : ℕ) : ℚ) _ _,
    simp_rw [mul_div_left_comm ((d * p ^ k : ℕ) : ℚ) _ _], rw div_self,
    rw mul_one,
    ring, simp_rw [nat.cast_mul _ (x : zmod (d * p^k)).val, ← h2, zmod.nat_cast_val],
    repeat { apply congr_arg2 _ _ rfl, },
    simp_rw [ring_hom.map_mul], rw mul_assoc, apply congr_arg2 _ rfl _, rw mul_comm,
    { rw nat.cast_mul, rw nat.cast_pow, apply h1, }, },
  { convert tendsto_const_nhds, ext, rw sub_eq_zero,
    apply finset.sum_congr _ (λ x hx, _),
    { convert refl _, apply_instance, },
    { rw mul_comm ((algebra_map ℚ R) ↑(n - 1)) _, rw mul_assoc, apply congr_arg2 _ rfl _,
      rw ← mul_div, rw ring_hom.map_mul, rw map_nat_cast, rw map_nat_cast, rw ← mul_assoc,
      rw mul_assoc (↑(n - 1) * ↑(c ^ n)) _ _, apply congr_arg2 _ rfl _,
      rw ← ring_hom.map_pow, rw ← ring_hom.map_mul, rw mul_one_div,
      simp_rw [nat.cast_mul, zmod.nat_cast_val, ← coe_coe, nat.cast_pow p], }, },
end

lemma V_h2 [no_zero_divisors R] [normed_algebra ℚ R] [norm_one_class R]
  (hd : d.coprime p) (hc' : c.coprime d) (hc : c.coprime p) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  (na' : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (n : ℕ) (hn : 1 < n) (hχ : χ.is_even) :
  tendsto (λ (x : ℕ), ((algebra_map ℚ R) n) * V_h_def p d R m χ c n x) at_top (𝓝 ((algebra_map ℚ R) ((↑n - 1)) *
  (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c *
  ↑c ^ n) * ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)))
  ↑p * ↑p ^ (n - 1)) * general_bernoulli_number (χ.mul
  (teichmuller_character_mod_p_change_level p d R m ^ n)) n))) :=
begin
  conv { congr, funext, rw ← sub_add_cancel ((algebra_map ℚ R) ↑n * V_h_def p d R m χ c n x) ((algebra_map ℚ R) ((n - 1 : ℕ) : ℚ) *
    (1 - (asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c *
    (algebra_map ℚ R) (c ^ n : ℚ)) * (U_def p d R m χ n x)), skip, skip, congr,
    rw ← zero_add (((algebra_map ℚ R) (↑n - 1) * _) * _), },
  apply tendsto.add,
  { conv { congr, funext, rw ← neg_neg ((algebra_map ℚ R) ↑n * V_h_def p d R m χ c n x - _), skip,
      skip, rw ← neg_neg (0 : R), },
    apply tendsto.neg,
    rw neg_zero, simp_rw neg_sub,
    conv { congr, funext, rw ← sub_add_sub_cancel _ ((algebra_map ℚ R) ((n - 1 : ℕ) : ℚ) * (U_def p d R m χ n x) -
      (∑ (x_1 : (zmod (d * p ^ x))ˣ), (asso_dirichlet_character
      (χ * teichmuller_character_mod_p_change_level p d R m ^ n) (x_1)) *
      (((n - 1 : ℕ) : R) * ((c^n : ℕ) : R) * ((algebra_map ℚ R) ((d * p^x : ℚ) *
      int.fract (↑((c : zmod (d * p^(2 * x)))⁻¹ : zmod (d * p^(2 * x))) * ↑x_1 / ↑(d * p ^ x)))^n) *
      (algebra_map ℚ R) (1 / (d * p^x))))) _, },
    apply filter.tendsto.zero_add_zero _ _,
    { apply_instance, },
    { conv { congr, funext, rw [mul_sub, mul_one, sub_mul ((algebra_map ℚ R) ↑(n - 1)) _ _, sub_sub,
        add_comm, ← sub_sub, ← sub_add, add_sub_assoc, map_nat_cast, sub_self, zero_add], },
      apply (tendsto_congr' _).2 (tendsto_const_nhds),
      apply V_h2_1 p d R m χ c hd hc' hc hp na n hn hχ, },
    apply V_h2_2 p d R m χ c hd hc' hc hp na na' n hn, },
  { convert (tendsto.const_mul ((algebra_map ℚ R) (↑n - 1) *
      (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)))
      ↑c * ↑c ^ n)) (U p d R m χ n hn hχ hp na)),
    ext, rw dirichlet_character.mul_eq_mul, rw ring_hom.map_pow,
    rw map_nat_cast (algebra_map ℚ R) c, congr, rw nat.cast_sub (le_of_lt hn), rw nat.cast_one,
    { apply zmod.is_unit_mul _ hc' hc, }, },
end

lemma V_h3 [no_zero_divisors R] [normed_algebra ℚ R] [norm_one_class R] (hd : d.coprime p)
  (hc' : c.coprime d) (hc : c.coprime p) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥∑ i in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  (na' : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (n : ℕ) (hn : 1 < n) (hχ : χ.is_even) :
  filter.tendsto (λ (x : ℕ), ↑((χ * teichmuller_character_mod_p_change_level p d R m ^ n)
  (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.mpr ⟨hc', p.coprime_pow_spl c m hc⟩))) *
  ↑c ^ n * U_def p d R m χ n x + V_h_def p d R m χ c n x) filter.at_top (nhds (((algebra_map ℚ R)
  ((↑n - 1) / ↑n) + (algebra_map ℚ R) (1 / ↑n) *
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c *
  ↑c ^ n) * ((1 - (asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑p * ↑p ^ (n - 1)) *
  general_bernoulli_number (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)) n))) :=
begin
  conv { congr, skip, skip, congr,
    rw ← add_sub_cancel' (↑((χ * teichmuller_character_mod_p_change_level p d R m ^ n)
      (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.mpr ⟨hc', p.coprime_pow_spl c m hc⟩))) *
      ↑c ^ n * ((1 - asso_dirichlet_character  (dirichlet_character.mul χ
      ((teichmuller_character_mod_p_change_level p d R m)^n)) (p) * p^(n - 1) ) *
      (general_bernoulli_number (dirichlet_character.mul χ
      ((teichmuller_character_mod_p_change_level p d R m)^n)) n))) (((algebra_map ℚ R) ((↑n - 1) / ↑n) +
      (algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c *
      ↑c ^ n) * ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑p * ↑p ^ (n - 1)) *
      general_bernoulli_number (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)) n)),
    rw ← add_sub, },
  apply tendsto.add,
  { apply tendsto.const_mul, apply U p d R m χ n hn hχ hp na, },
  { rw ← sub_mul, rw ← asso_dirichlet_character_eq_char,
    rw zmod.coe_unit_of_coprime, rw ← dirichlet_character.mul_eq_mul,
    rw ← add_sub, rw mul_assoc ((algebra_map ℚ R) (1 / ↑n)) _ _, rw ← sub_one_mul,
    rw ← ring_hom.map_one (algebra_map ℚ R), rw ← ring_hom.map_sub,-- rw add_comm (1 / ↑n) (1 : ℚ),
    rw div_sub_one _,
    { rw ← neg_sub ↑n (1 : ℚ), rw neg_div, rw ring_hom.map_neg, rw neg_mul, rw ← sub_eq_add_neg,
      rw ← mul_one_sub, rw ring_hom.map_one,
      have h : (algebra_map ℚ R) (1 / (n : ℚ)) * (algebra_map ℚ R) (n : ℚ) = 1,
      { rw ← ring_hom.map_mul, rw one_div_mul_cancel, rw ring_hom.map_one,
        { norm_cast, apply ne_zero_of_lt hn, }, },
      conv { congr, funext, rw ← one_mul (V_h_def p d R m χ c n x), rw ← h, rw mul_assoc,
        skip, skip, rw div_eq_mul_one_div, rw mul_assoc, rw ring_hom.map_mul,
        rw mul_comm _ ((algebra_map ℚ R) (1 / ↑n)), rw mul_assoc, },
      apply tendsto.const_mul,
      have := V_h2 p d R m χ c hd hc' hc hp na na' n hn hχ,
      conv at this { congr, skip, skip, congr, rw mul_assoc ((algebra_map ℚ R) (↑n - 1)) _ _, },
      apply this, },
    { norm_cast, apply ne_zero_of_lt hn, },
    { apply zmod.is_unit_mul _ hc' hc, }, },
end

lemma V [no_zero_divisors R] [normed_algebra ℚ R] [norm_one_class R] (hd : d.coprime p) (hc' : c.coprime d)
  (hc : c.coprime p) (hp : 2 < p) (hχ : χ.is_even)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (na' : ∀ (n : ℕ) (f : ℕ → R), ∥∑ i in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  (n : ℕ) (hn : 1 < n) :
  filter.tendsto (λ j : ℕ, V_def p d R m χ c n j)
  filter.at_top (nhds (( algebra_map ℚ R ((n - 1) / n) + (algebra_map ℚ R (1 / n)) *
  asso_dirichlet_character (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) (c) * c^n ) * ((1 -
  asso_dirichlet_character (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) n))) ) :=
begin
  conv { congr, funext, rw ← sub_add_cancel (V_def p d R m χ c n j) (((((χ * ((teichmuller_character_mod_p_change_level p d R m)^n)) (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime_pow_spl p c m hc⟩))
   * (c : R)^n)) * U_def p d R m χ n j : R) + (V_h_def p d R m χ c n j)), skip, skip,
  rw ← zero_add (((algebra_map ℚ R) ((↑n - 1) / ↑n) + (algebra_map ℚ R) (1 / ↑n) *
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c *
    ↑c ^ n) * ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑p *
    ↑p ^ (n - 1)) * general_bernoulli_number (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)) n)), },
  apply filter.tendsto.add,
  { apply V_h1 p d R m χ c hd hc' hc na n hn, },
  { apply V_h3 p d R m χ c hd hc' hc hp na' na n hn hχ, },
end

lemma W [no_zero_divisors R] [normed_algebra ℚ R] [norm_one_class R] (hp : 2 < p) (hχ : χ.is_even)
  (na' : ∀ (n : ℕ) (f : ℕ → R), ∥∑ i in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  (n : ℕ) (hn : 1 < n) :
  filter.tendsto (λ j : ℕ, ∑ (x : (zmod (d * p ^ j))ˣ), ((asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m)^n) x : R) *
  ((((x : zmod (d * p^j))).val)^(n - 1) : R)) • (algebra_map ℚ R) ((↑c - 1) / 2)) filter.at_top (nhds 0) :=
begin
  rw metric.tendsto_at_top, intros ε hε,
  refine ⟨max (N1 d p m χ hn (ε / 2) (half_pos hε)) (N2 d p m χ hn (ε / 2) (half_pos hε)),
    λ x hx, _⟩,
  rw dist_eq_norm,
  rw sub_zero, simp_rw smul_eq_mul R, simp_rw ← finset.sum_mul,
  have := lim_even_character_aux1 d p m χ na' hn hχ hp ε hε (max_le_iff.1 hx).1 (max_le_iff.1 hx).2,
  sorry
end
