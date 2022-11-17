import number_theory.general_bernoullli_number_properties_three
import topology.compact_open

open_locale big_operators
local attribute [instance] zmod.topological_space

variables (p : ℕ) [fact (nat.prime p)] (d : ℕ) (R : Type*) [normed_comm_ring R] (m : ℕ)
(hd : d.gcd p = 1) (χ : dirichlet_character R (d*(p^m))) {c : ℕ} (hc : c.gcd p = 1)
(hc' : c.gcd d = 1) (na : ∀ (n : ℕ) (f : ℕ → R),
  ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
(w : weight_space (units (zmod d) × units ℤ_[p]) R)

variable [fact (0 < d)]
variables [complete_space R] [char_zero R]

noncomputable abbreviation rev_coe (n : ℕ) (a : (zmod (d * p^n))ˣ) : ℤ_[p]ˣ :=
begin
  by_cases hn : n ≠ 0,
  { apply is_unit.unit,
    swap, exact (a : ℤ_[p]),
    change is_unit ↑(a : zmod (d * p^n)),
    rw ← zmod.nat_cast_val _,
    apply is_unit_padic_of_is_unit_zmod,
    have c := units.map (zmod.cast_hom (dvd_pow (dvd_refl p) hn) (zmod p)).to_monoid_hom,
    { rw zmod.nat_cast_val _,
      rw ← zmod.cast_hom_apply _,
      swap 3, { refine zmod.char_p _, },
      swap, { apply dvd_mul_of_dvd_right (dvd_pow_self p hn) d, },
      rw ← ring_hom.coe_monoid_hom,
      rw ← ring_hom.to_monoid_hom_eq_coe,
      rw ← units.coe_map ((zmod.cast_hom (dvd_mul_of_dvd_right (dvd_pow_self p hn) d) (zmod p)).to_monoid_hom) _,
      apply units.is_unit,
      apply fact_iff.2,
      apply mul_prime_pow_pos p d n, },
      -- apply pow_pos (nat.prime.pos infer_instance), apply fact.out, },
    { apply (nat.coprime_pow_right_iff (nat.pos_of_ne_zero hn) _ _).1,
      apply nat.coprime.coprime_mul_left_right, swap, { exact d, },
      apply zmod.val_coe_unit_coprime, },
    { apply fact_iff.2 (mul_prime_pow_pos p d n), }, },
      -- apply fact_iff.2 (pow_pos (nat.prime.pos (fact.out _)) _), assumption, }, },
    { exact 1, },
end

lemma lets_see : @padic_int.lift p _ ℤ_[p] _ (λ k, padic_int.to_zmod_pow k)
  (λ k₁ k₂ hk, by {simp only [padic_int.zmod_cast_comp_to_zmod_pow]}) = ring_hom.id ℤ_[p] :=
begin
  ext,
  simp only [padic_int.lift_self, ring_hom.id_apply],
end

lemma hmm (n : ℕ) : @continuous ((zmod d)ˣ × (zmod (d * p^n))ˣ) ((zmod d)ˣ × ℤ_[p]ˣ) _ _
  (prod.map (@id (zmod d)ˣ) ((@rev_coe p _ d _ n) )) :=
-- ∘ (units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom ))) :=
begin
  apply continuous.prod_mk,
  { simp only [id.def], exact continuous_fst, },
  { apply continuous_of_discrete_topology, },
    /- refine (continuous.comp _ _).comp continuous_snd,
    { apply continuous_of_discrete_topology, },
    { exact continuous_units p n, }, }, -/
end

lemma tbu (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) (n : ℕ) :
  is_locally_constant (f ∘ (prod.map id ((rev_coe p d n) ))) :=
  -- ∘ (units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom )))) :=
begin
  apply is_locally_constant.comp, apply is_locally_constant.prod_mk,
  exact is_locally_constant.of_discrete (λ (x : (zmod d)ˣ × (zmod (d * p ^ n))ˣ), id x.fst),
  -- simp, exact is_locally_constant.of_discrete prod.fst,
  exact is_locally_constant.of_discrete (λ (x : (zmod d)ˣ × (zmod (d * p ^ n))ˣ), rev_coe p d n x.snd),


  /- rw is_locally_constant.iff_exists_open, rintros x,
  set U : set ((zmod d)ˣ × ℤ_[p]ˣ) := units_clopen_from p d n
    (x.1, x.2), -- units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom x.2),
  refine ⟨U, (is_clopen_units_clopen_from p d n _).1, _, λ y hy, _⟩,
  { --separate lemma
    change x ∈ units_clopen_from p d n (x.fst,
      (units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom) x.snd),
    delta units_clopen_from,
    simp only [ring_hom.to_monoid_hom_eq_coe, set.singleton_prod, set.mem_image, set.mem_preimage,
      set.mem_singleton_iff],
    refine ⟨x.2, rfl, prod.ext rfl rfl⟩, },
  { simp only [ring_hom.to_monoid_hom_eq_coe, function.comp_app, prod_map, id.def],
    -- hy should be a separate lemma
    change y ∈ units_clopen_from p d n (x.fst,
      (units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom) x.snd) at hy,
    simp only [ring_hom.to_monoid_hom_eq_coe, set.mem_prod, set.mem_singleton_iff,
      set.mem_preimage] at hy,
    rw [hy.1, hy.2], }, -/
end

lemma shh (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) (n : ℕ) : ∑ (a : (zmod d)ˣ × (zmod (p ^ n))ˣ), f (a.fst, rev_coe p d n a) •
    (locally_constant.char_fn R (is_clopen_units_clopen_from p d n a) : C((zmod d)ˣ × ℤ_[p]ˣ, R)) =
    inclusion ((zmod d)ˣ × ℤ_[p]ˣ) R ⟨(f ∘ (prod.map (@id (zmod d)ˣ) ((rev_coe p d n) ))),
    -- ∘ (units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom )))),
    tbu p d R f n⟩ :=
    -- ⟨f ∘ (prod.map id ((rev_coe p) ∘ (units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom ))),
    -- continuous.comp f.continuous (hmm p d n)⟩ :=
begin
  ext,
  simp only [continuous_map.coe_sum, continuous_map.coe_smul,
    locally_constant.coe_continuous_map, fintype.sum_apply, pi.smul_apply,
    algebra.id.smul_eq_mul, ring_hom.to_monoid_hom_eq_coe, continuous_map.coe_mk,
    function.comp_app, prod_map, id.def],
  rw finset.sum_eq_single_of_mem (a.fst, ((units.map
    (@padic_int.to_zmod_pow p _ n).to_monoid_hom) a.snd)),
  { simp only [ring_hom.to_monoid_hom_eq_coe], rw (locally_constant.char_fn_one _ _ _).1,
    { rw mul_one, simp only [locally_constant.to_continuous_map_linear_map_apply,
        locally_constant.coe_continuous_map, locally_constant.coe_mk, function.comp_app, prod_map,
        id.def], },
    { delta units_clopen_from,
      simp only [ring_hom.to_monoid_hom_eq_coe, set.singleton_prod, set.mem_image,
        set.mem_preimage, set.mem_singleton_iff],
      refine ⟨a.snd, rfl, prod.ext rfl rfl⟩, },
    { apply_instance, }, },
  { exact finset.mem_univ (a.fst, (units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom)
      a.snd), },
  { rintros b - hb,
    convert mul_zero _,
    rw ← locally_constant.char_fn_zero,
    intro h,
    apply hb,
    delta units_clopen_from at h,
    simp only [ring_hom.to_monoid_hom_eq_coe, set.singleton_prod, set.mem_image,
      set.mem_preimage, set.mem_singleton_iff] at h,
    rcases h with ⟨y, hy, h⟩,
    rw prod.ext_iff at *,
    simp only [ring_hom.to_monoid_hom_eq_coe] at *,
    rw ← hy, rw h.2, refine ⟨h.1, rfl⟩, },
end

/-- Gives the equivalence (ℤ/(m * n)ℤ)ˣ ≃* (ℤ/mℤ)ˣ × (ℤ/nℤ)ˣ -/
abbreviation units.chinese_remainder {m n : ℕ} (h : m.coprime n) :
  (zmod (m * n))ˣ ≃* (zmod m)ˣ × (zmod n)ˣ :=
mul_equiv.trans (units.map_equiv (zmod.chinese_remainder h).to_mul_equiv) mul_equiv.prod_units

example {α β γ : Type*} [monoid α] [monoid β] [monoid γ] (h : γ ≃* α × β) : monoid_hom (α × β) γ := by refine (mul_equiv.symm h).to_monoid_hom

/- -- generated from Copilot
  lemma units_clopen_from_chinese_remainder {m n : ℕ} (h : m.coprime n) (a : (zmod m)ˣ × (zmod n)ˣ) :
  units_clopen_from p d (m * n) (a.fst, (units.map (zmod.chinese_remainder h).to_monoid_hom) a.snd) =
  units_clopen_from p d m a.fst ∩ units_clopen_from p d n a.snd := sorry -/

def mul_equiv.mul_op (α : Type*) [comm_semigroup α] : αᵐᵒᵖ ≃* α :=
⟨mul_opposite.unop, mul_opposite.op, mul_opposite.op_unop, mul_opposite.unop_op,
  λ x y, by { rw [mul_comm x y, mul_opposite.unop_mul y x], }⟩

lemma prod.map_id_id (α β : Type*) : prod.map (@id α) (@id β) = id := by { ext, simp, simp, }

lemma monoid_hom.prod_map_comp_prod_map {α₁ α₂ α₃ β₁ β₂ β₃ : Type*} [mul_one_class α₁] [mul_one_class β₁]
  [mul_one_class α₂] [mul_one_class β₂] [mul_one_class α₃] [mul_one_class β₃]
  (f : α₁ →* α₂) (f' : α₂ →* α₃) (g : β₁ →* β₂) (g' : β₂ →* β₃) :
  (monoid_hom.prod_map f' g').comp (monoid_hom.prod_map f g) =
  monoid_hom.prod_map (f'.comp f) (g'.comp g) := by { ext, simp, simp, }

def mul_equiv.prod {α β γ δ : Type*} [comm_group α] [comm_group β]
  [comm_group γ] [comm_group δ] (h1 : mul_equiv α γ)
  (h2 : mul_equiv β δ) : mul_equiv (α × β) (γ × δ) :=
⟨monoid_hom.prod_map h1.to_monoid_hom h2.to_monoid_hom, monoid_hom.prod_map h1.symm.to_monoid_hom h2.symm.to_monoid_hom,
by { refine function.left_inverse_iff_comp.mpr _, ext,
  simp only [monoid_hom.coe_prod_map, mul_equiv.coe_to_monoid_hom, function.comp_app, prod_map,
  mul_equiv.symm_apply_apply, id.def], simp only [monoid_hom.coe_prod_map, mul_equiv.coe_to_monoid_hom, function.comp_app, prod_map, mul_equiv.symm_apply_apply, id.def], }, -- rw monoid_hom.prod_map_comp_prod_map, rw mul_equiv.symm_comp_self, rw mul_equiv.symm_comp_self, rw prod.map_id_id, },
by { refine function.right_inverse_iff_comp.mpr _, ext, simp only [monoid_hom.coe_prod_map, mul_equiv.coe_to_monoid_hom, function.comp_app, prod_map, mul_equiv.apply_symm_apply, id.def], simp, }, --rw prod.map_comp_map, rw mul_equiv.self_comp_symm, rw mul_equiv.self_comp_symm, rw prod.map_id_id, },
by { simp, }⟩
.
def mul_equiv.prod_mul_op (α β : Type*) [comm_group α] [comm_group β] : (α × β)ᵐᵒᵖ ≃* αᵐᵒᵖ × βᵐᵒᵖ :=
mul_equiv.trans (mul_equiv.mul_op (α × β)) ((mul_equiv.prod (mul_equiv.mul_op α).symm (mul_equiv.mul_op β).symm)) --(mul_equiv.mul_op α).symm (mul_equiv.mul_op β).symm)

example (a b : ℝ) (ha : a ≤ b) (hb : b ≤ a) : a = b := ge_antisymm hb ha

def prod.prod_comm_comm (α β γ δ : Type*) [has_mul α] [has_mul β] [has_mul γ] [has_mul δ] :
  (α × β) × (γ × δ) ≃* (α × γ) × (β × δ) :=
  ⟨λ x, ((x.1.1, x.2.1), (x.1.2, x.2.2)),
  λ x, ((x.1.1, x.2.1), (x.1.2, x.2.2)),
  by { rw function.left_inverse_iff_comp, ext, simp, simp, simp, simp, },
  by { rw function.right_inverse_iff_comp, ext, simp, simp, simp, simp, },
  λ x y, by { simp }⟩

lemma units.embed_product_prod {α β : Type*} [comm_group α] [comm_group β] : units.embed_product (α × β) =
monoid_hom.comp (monoid_hom.comp (monoid_hom.comp (monoid_hom.prod_map (monoid_hom.id (α × β))
((mul_equiv.prod_mul_op α β).symm.to_monoid_hom)) (prod.prod_comm_comm α αᵐᵒᵖ β βᵐᵒᵖ).to_monoid_hom)
((monoid_hom.prod_map (units.embed_product α) (units.embed_product β))))
(@mul_equiv.prod_units α β _ _).to_monoid_hom :=
begin
  rw units.embed_product,
  ext,
  { change ((x : α × β), mul_opposite.op ↑x⁻¹).fst.fst = _,
    simp_rw [units.embed_product, monoid_hom.comp_apply],
    change _ = (((monoid_hom.id (α × β)).prod_map (mul_equiv.prod_mul_op α β).symm.to_monoid_hom)
      (((prod.prod_comm_comm α αᵐᵒᵖ β βᵐᵒᵖ).to_monoid_hom)
      ((((((@mul_equiv.prod_units α β _ _).to_monoid_hom) x).fst : α), mul_opposite.op ↑((((@mul_equiv.prod_units α β _ _).to_monoid_hom) x).fst)⁻¹),
      ((((@mul_equiv.prod_units α β _ _).to_monoid_hom) x).snd : β), mul_opposite.op ↑((((@mul_equiv.prod_units α β _ _).to_monoid_hom) x).snd)⁻¹))).fst.fst,
    rw prod.prod_comm_comm, sorry,
    sorry, },
  { sorry, },
  sorry
end
.

lemma units.embed_product_prod_top_eq {α β : Type*} [comm_group α] [topological_space α] [comm_group β] [topological_space β] :
  @units.topological_space (α × β) _ _ =
  topological_space.induced ((@mul_equiv.prod_units α β _ _).to_fun) (@prod.topological_space (units α) (units β) (units.topological_space) _) :=
begin
  ext, rw is_open_induced_iff',
  rw units.topological_space, rw is_open_induced_iff',
  rw units.embed_product_prod,
  split, --simp_rw is_open_prod_iff,
  { rintros ⟨t, ht, htx⟩, },
  { sorry, },
end

noncomputable def ind_fn'' (f : C(units (zmod d) × units ℤ_[p], R)) :=
  λ x : (zmod d × ℤ_[p]), @dite _ (is_unit x.1 ∧ is_unit x.2)
    (classical.dec (is_unit x.fst ∧ is_unit x.snd)) (λ h, f (is_unit.unit h.1, is_unit.unit h.2)) (λ h, 0)

lemma ind_fn_eq_fun'' (f : C(units (zmod d) × units ℤ_[p], R)) :
  f.to_fun = (ind_fn'' p d R f) ∘ (prod.map (coe : units (zmod d) → zmod d) (coe : units ℤ_[p] → ℤ_[p])) :=
begin
  ext x, rw function.comp, simp only, rw ind_fn'', simp only,
  symmetry, convert dif_pos _,
  { rw prod.ext_iff, simp only [prod_map], split,
    all_goals { rw units.ext_iff,
      rw is_unit.unit_spec (units.is_unit _), }, },
  { simp only [units.is_unit, prod_map, and_self], },
end

noncomputable def cont_ind_fn (f : C(units (zmod d) × units ℤ_[p], R)) :
  C(zmod d × ℤ_[p], R) := ⟨ind_fn'' p d R f, sorry⟩

lemma cont_ind_fn_eq_fun (f : C(units (zmod d) × units ℤ_[p], R)) :
  f = continuous_map.comp (cont_ind_fn p d R f) (continuous_map.prod_map
    (⟨(coe : units (zmod d) → zmod d), continuous_of_discrete_topology⟩)
    (⟨(coe : units ℤ_[p] → ℤ_[p]), units.continuous_coe⟩)) :=
by { ext, simp only [cont_ind_fn, continuous_map.comp, continuous_map.prod_map, function.comp,
      continuous_map.coe_mk, prod_map], rw ← continuous_map.to_fun_eq_coe, rw ind_fn_eq_fun'',
      simp, }

lemma cont_2 (n : ℕ) : continuous ((units.map ((zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).symm.to_monoid_hom.comp
  (monoid_hom.prod (monoid_hom.fst (zmod d) ℤ_[p]) ((padic_int.to_zmod_pow n).to_monoid_hom.comp
  (monoid_hom.snd _ _))) )).comp (mul_equiv.symm (@mul_equiv.prod_units (zmod d) ℤ_[p] _ _) ).to_monoid_hom) :=
begin
  apply continuous.comp, -- hit
  { --apply locally_constant.discrete_quotient,
    -- apply units.map_continuous, -- hallucination
    -- came up with an entire skeleton here
    apply cont_units_map,
    { --A1:
      change continuous (coe ∘ units.has_inv.inv),
      apply continuous.comp,
      apply units.continuous_coe, --refine @continuous.inv _ _ _ _ _ _ _ _,

      --rw continuous_iff_le_induced, intros s hs,

      --A2:
      /-rw ← top_eq_iff_cont_inv,  rw units.topological_space,
      apply le_antisymm,
      apply continuous.le_induced, apply continuous_induced_dom, --apply units.continuous_embed_product,
      have := cont_inv p, -/
      sorry, },
    { convert continuous_of_discrete_topology,
      have := disc_top_units' (d  * p^n),

      sorry, },
    /- skeleton generated by Copilot - incorrect/hallucination
      apply cont_zmod_chinese_remainder,
      apply nat.coprime_pow_spl, exact hd, },
    { apply cont_prod,
      { apply cont_fst, },
      { apply cont_comp,
        { apply cont_snd, },
        { apply cont_padic_int_to_zmod_pow, }, }, },
    { apply cont_comp,
      { apply cont_symm,
        apply cont_to_monoid_hom,
        apply cont_prod_units, },
      { apply cont_to_monoid_hom, }, }, -/
      continuity,
      { exact continuous_of_discrete_topology, },
      { simp only [ring_hom.to_monoid_hom_eq_coe, monoid_hom.prod_apply, monoid_hom.coe_fst,
          monoid_hom.coe_comp, ring_hom.coe_monoid_hom, monoid_hom.coe_snd, function.comp_app],
        refine continuous_fst.prod_mk (continuous.comp (padic_int.continuous_to_zmod_pow p n)
          continuous_snd), }, },
  { simp only [mul_equiv.coe_to_monoid_hom], rw ← mul_equiv.coe_to_equiv,
    change continuous (mul_equiv.prod_units.symm).to_equiv,
    change continuous (units.homeomorph.prod_units.symm).to_equiv,
    rw homeomorph.coe_to_equiv, apply homeomorph.continuous,
    exact has_continuous_mul_of_discrete_topology,
    exact semi_normed_ring_top_monoid, },
end

lemma shh' (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) : (λ n : ℕ, (∑ (a : (zmod (d * (p ^ n)))ˣ),
  f (units.map (zmod.cast_hom (dvd_mul_right d (p^n)) (zmod d)).to_monoid_hom a, rev_coe p d n a) •
  (locally_constant.char_fn R (is_clopen_units_clopen_from p d n ((units.chinese_remainder
  (nat.coprime_pow_spl p d n hd)) a)) : C((zmod d)ˣ × ℤ_[p]ˣ, R) ))) =
  (λ n : ℕ, f.comp (continuous_map.prod_map id (continuous_map.comp
  (⟨rev_coe p d n, continuous_of_discrete_topology⟩)
  (⟨_, sorry⟩)))) := --(λ n : ℕ, f.comp (continuous_map.prod_mk _ _)) :=
  /-((continuous_map.prod_mk ⟨(units.map (zmod.cast_hom (dvd_mul_right d (p^n))
  (zmod d)).to_monoid_hom), (continuous_of_discrete_topology)⟩ ⟨(rev_coe p d n),
  continuous_of_discrete_topology⟩).comp (⟨
  (units.map ((zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).symm.to_monoid_hom.comp
  (monoid_hom.prod (monoid_hom.fst (zmod d) ℤ_[p]) ((padic_int.to_zmod_pow n).to_monoid_hom.comp
  (monoid_hom.snd _ _))) )).comp
  (mul_equiv.symm (@mul_equiv.prod_units (zmod d) ℤ_[p] _ _) ).to_monoid_hom, cont_2 p d hd _⟩))) := -/
  --(units.map (zmod.cast_hom (dvd_mul_right d (p^n)) (zmod d)).to_monoid_hom) (rev_coe p d n)) :=
--  (units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom ).to_fun )), hmm p d n⟩) :=
    --(⟨(prod.map (@id (zmod d)ˣ) ((rev_coe p) ∘ (units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom ))).to_fun,
    --hmm p d n⟩) :=
begin
  ext y,
  simp only [continuous_map.coe_sum, continuous_map.coe_smul, locally_constant.coe_continuous_map, fintype.sum_apply,
  pi.smul_apply, algebra.id.smul_eq_mul, ring_hom.to_monoid_hom_eq_coe, continuous_map.comp_apply,
  continuous_map.coe_mk, prod_map, id.def, function.comp_app],
  convert finset.sum_eq_single_of_mem _ _ _,
  symmetry,
  convert mul_one _,
  { rw (locally_constant.char_fn_one _ _ _).1,
    {
      delta units_clopen_from,
      simp only [ring_hom.to_monoid_hom_eq_coe, set.singleton_prod, set.mem_image,
        set.mem_preimage, set.mem_singleton_iff],
      delta units.chinese_remainder, },
    sorry, },
  { apply finset.mem_univ, },
  { sorry, },
  rw finset.sum_eq_single_of_mem (y.fst, ((units.map
    (@padic_int.to_zmod_pow p _ n).to_monoid_hom) y.snd)),
  { simp only [ring_hom.to_monoid_hom_eq_coe], rw (locally_constant.char_fn_one _ _ _).1,
    { rw mul_one, },
    { delta units_clopen_from,
      simp only [ring_hom.to_monoid_hom_eq_coe, set.singleton_prod, set.mem_image,
        set.mem_preimage, set.mem_singleton_iff],
      refine ⟨y.snd, rfl, prod.ext rfl rfl⟩, },
    { apply_instance, }, },
  { exact finset.mem_univ (y.fst, (units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom)
      y.snd), },
  { rintros b - hb,
    convert mul_zero _,
    rw ← locally_constant.char_fn_zero,
    intro h,
    apply hb,
    delta units_clopen_from at h,
    simp only [ring_hom.to_monoid_hom_eq_coe, set.singleton_prod, set.mem_image,
      set.mem_preimage, set.mem_singleton_iff] at h,
    rcases h with ⟨y, hy, h⟩,
    rw prod.ext_iff at *,
    simp only [ring_hom.to_monoid_hom_eq_coe] at *,
    rw ← hy, rw h.2, refine ⟨h.1, rfl⟩, },
end

open locally_constant.density

lemma real_secret (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) (ε : ℝ) [fact (0 < ε)] :
  dist f (inclusion ((zmod d)ˣ × ℤ_[p]ˣ) R ⟨c2 ε f, loc_const ε f⟩) < ε :=
begin
  apply gt_of_gt_of_ge (half_lt_self (fact.out _)),
  { -- showing that the distance between `f` and `c2` is less than or equal to `ε/2`
  rw [dist_eq_norm, continuous_map.norm_eq_supr_norm],
-- writing the distance in terms of the sup norm
  refine cSup_le _ (λ m hm, _),
  { rw set.range_nonempty_iff_nonempty, apply_instance, }, -- this is where `nonempty X` is needed
  { cases hm with y hy,
    simp only [continuous_map.coe_sub, locally_constant.coe_mk,
      locally_constant.to_continuous_map_linear_map_apply, pi.sub_apply,
      locally_constant.coe_continuous_map] at hy,
    rw ←hy,
    -- reduced to proving ∥f(y) - c2(y)∥ ≤ ε/2
    obtain ⟨w, wT, hw⟩ := finset_clopen_prop ε f y,
    -- `w` is the unique element of `finset_clopen` to which `y` belongs
    simp only [exists_prop, exists_unique_iff_exists] at wT,
    simp only [and_imp, exists_prop, exists_unique_iff_exists] at hw,
    have : c2 ε f y = f (c' ε f w ⟨wT.1, ⟨⟨y, wT.2⟩⟩⟩),
    -- showing that `w` is the same as the `classical.some _` used in `c2`
    { delta c2, congr',
      any_goals
      { have := classical.some_spec (exists_of_exists_unique (finset_clopen_prop ε f y)),
        simp only [exists_prop, exists_unique_iff_exists] at *,
        apply hw _ (this.1) (this.2), }, },
    rw this,
    obtain ⟨U, hU, wU⟩ := exists_sub_S ε f wT.1,
    -- `U` is a set of `A` which is an element of `S` and contains `f(w)`
    cases hU with z hz,
    -- `U` is the `ε/4`-ball centered at `z`
    have mem_U : f (c' ε f w ⟨wT.1, ⟨⟨y, wT.2⟩⟩⟩) ∈ U :=
      wU ⟨(c' ε f w ⟨wT.1, ⟨⟨y, wT.2⟩⟩⟩), subtype.coe_prop _, rfl⟩,
    have tS : f y ∈ U := wU ⟨y, wT.2, rfl⟩,
    rw [hz.symm, mem_ball_iff_norm] at *,
    conv_lhs { rw sub_eq_sub_add_sub _ _ z, },
    -- unfolding everything in terms of `z`, and then using `mem_U` and `tS`
    have : ε/2 = ε/4 + ε/4, { rw div_add_div_same, linarith, },
    rw this, apply norm_add_le_of_le (le_of_lt _) (le_of_lt tS),
    rw ←norm_neg _, simp only [mem_U, neg_sub], }, },
  { apply_instance, },
end

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

/-lemma h2 (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) : filter.tendsto
  (λ (x : ℕ), (⟨prod.map id (rev_coe p ∘ (units.map (@padic_int.to_zmod_pow p _ x).to_monoid_hom)), hmm p d x⟩ : C((zmod d)ˣ × ℤ_[p]ˣ, (zmod d)ˣ × ℤ_[p]ˣ)))
  filter.at_top (nhds ((continuous_map.id (zmod d)ˣ).prod_map (continuous_map.id ℤ_[p]ˣ))) :=
begin
  rw filter.tendsto_at_top',
  rintros s hs,
  rw mem_nhds_iff at hs,
  rcases hs with ⟨t, ht, h1, h2⟩,

  sorry
end-/

/-instance : has_dist (zmod d) :=
{ dist := λ a b, ite (a = b) 0 1 }  -/

instance : uniform_space ((zmod d)ˣ × ℤ_[p]ˣ) := sorry

example : pseudo_metric_space (zmod d) :=
begin

end

noncomputable instance : pseudo_metric_space ((zmod d)ˣ × ℤ_[p]ˣ) :=
begin

end
/- begin
  refine pseudo_metric_space.induced _ _,
  { exact zmod d × ℤ_[p], },
  { exact coe, },
  refine pseudo_metric_space.induced _ _,
  { exact ℤ_[p], },
  { exact prod.snd, },
  apply_instance,
end -/

--  instance : continuous_map_class C((zmod d)ˣ × ℤ_[p]ˣ, R) ((zmod d)ˣ × ℤ_[p]ˣ) R :=
-- continuous_map.continuous_map_class

-- example : complete_space (C((zmod d)ˣ × ℤ_[p], R)) := infer_instance

example (a b : ℝ) (ha : a ≤ b) (hb : b ≤ a) : a = b := ge_antisymm hb ha

example : @uniform_space.to_topological_space ((zmod d)ˣ × ℤ_[p]ˣ) _ = prod.topological_space :=
begin
  ext,
  rw uniform_space.is_open_uniformity,
  refine ⟨λ h, _, λ h, λ y hy, _⟩,
  { -- rw uniform_space.is_open_uniformity at h,
    apply is_open_prod_iff.2 _, -- rw does not work
    intros a b hab, specialize h (a, b) hab,
    obtain ⟨ε, hε, h⟩ := metric.mem_uniformity_dist.1 h,
    refine ⟨{a}, coe⁻¹' (metric.ball (b : ℤ_[p]) ε), is_open_discrete _,
      continuous.is_open_preimage (units.continuous_coe) _ metric.is_open_ball,
      set.mem_singleton _, _, λ y hy, _⟩,
    { simp only [set.mem_preimage, metric.mem_ball, dist_self], assumption, },
    { simp only [set.mem_prod, set.mem_singleton_iff, set.mem_preimage, metric.mem_ball] at hy,
      have : dist (a, b) y < ε,
      { change dist (prod.snd ((a, b) : (zmod d) × ℤ_[p])) (prod.snd (coe y : (zmod d) × ℤ_[p])) < ε,
        rw dist_comm,
        convert hy.2,
        rw ← @prod.mk.eta _ _ y, change (coe y.1, coe y.2).snd = _, simp only, },
      specialize h this, simp only [set.mem_set_of_eq, eq_self_iff_true, forall_true_left] at h,
      exact h, }, },
  { rw ← @prod.mk.eta _ _ y at hy,
    obtain ⟨u, v, hu, hv, hyu, hyv, h'⟩ := is_open_prod_iff.1 h y.1 y.2 hy,
    apply metric.mem_uniformity_dist.2, -- why does rw not work?
    -- rw is_open_induced_iff at hv,
    obtain ⟨t, ht, hv'⟩ := is_open_induced_iff.1 hv,
    rw set.ext_iff at hv', specialize hv' y.snd, rw set.mem_preimage at hv',
    rw is_open_prod_iff at ht,
    specialize ht (coe y.snd) (mul_opposite.op ↑y.snd⁻¹),
    specialize ht (hv'.2 hyv),
    rcases ht with ⟨u', v', h'u, h'v, h'yu, h'yv, ht⟩,
    -- have h'' := metric.is_open_iff.1 h'yu,
    rw metric.is_open_iff at h'u,
    obtain ⟨ε, hε, h'u⟩ := h'u (y.snd : ℤ_[p]) h'yu,
    refine ⟨ε, hε, λ a b hab, _⟩,
    -- intros a b hab,
    simp only [set.mem_set_of_eq],
    intro hay,
    rw is_open_prod_iff at h,
    sorry, },
end

example (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) :
  @continuous ((zmod d)ˣ × ℤ_[p]ˣ) R uniform_space.to_topological_space _ f :=
begin
  refine (@continuous_def _ _ uniform_space.to_topological_space _ _).mpr _,
  intros s hs,
  have := map_continuous f,
  rw continuous_def at this,
  specialize this s hs,
  apply is_open_implies_is_open_iff.2,
  swap 2, { exact this, },
  intros a ha,
  -- convert this,

end

-- example (s : set ((zmod d)ˣ × ℤ_[p]ˣ)) (hs : is_compact s) :
--   ∃ n : ℕ, s = set.image ( (@id (zmod d)) (coe : (zmod (p^n))ˣ → ℤ_[p]ˣ))

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
  -- A1 :
  apply topological_space.tendsto_nhds_generate_from,
  simp only [exists_prop, set.mem_set_of_eq, filter.mem_at_top_sets, ge_iff_le, set.mem_preimage, forall_exists_index, and_imp],
  simp_rw [← @set.mem_preimage _ _ f.comp _ _],
  rintros s t compt a opena hs mems,
  simp_rw [hs, preimage_gen _ compt opena],
  rw tendsto_nhds at h, simp only [filter.mem_at_top_sets, ge_iff_le, set.mem_preimage] at h,
  apply h,
  { apply continuous_map.is_open_gen compt (continuous.is_open_preimage (map_continuous _) _ opena), },
  { rw ← preimage_gen _ compt opena, rw set.mem_preimage, rw comp_id, rw ← hs, apply mems, },

/-  -- A1' :
  rw ← filter.tendsto_comap_iff,
  rw filter.tendsto_def at h,
--  rw tendsto_nhds at h,
  rw filter.tendsto_def, intros s hs, apply h,
  rw mem_nhds_iff,
  simp at hs,
  cases hs with t ht, rw mem_nhds_iff at ht,
  cases ht with t' ht',
  cases t' with t1 h1, cases h1 with h1 h2,
  refine ⟨f.comp ⁻¹' (t1 ∩ interior (set.range f.comp)), _, _, _⟩,
  { apply subset_trans _ ht',
    rw set.preimage_subset_preimage_iff _,
    { apply subset_trans _ h1, apply set.inter_subset_left, },
    { intros y hy, apply interior_subset, apply set.inter_subset_right _ _ hy, }, },
  { apply continuous.is_open_preimage,
    { exact continuous_map.continuous_comp f, },
    { apply is_open.inter,
      { apply h2.1, },
      { apply is_open_interior, }, }, },
  { rw set.mem_preimage, rw continuous_map.comp_id, apply set.mem_inter,
    { apply h2.2, },
    {
      refine mem_interior.mpr _, rw continuous_map.compact_open,
      rw topological_space.generate_from,
      refine nhds_le_nhds_set.mp _,
      rw mem_interior_iff_mem_nhds, rw mem_nhds_iff, }, },
  rw filter.mem_comap_iff,

  convert h,

  rw homeomorph.comap_nhds_eq, --ext, simp, rw mem_nhds_iff,

  -- A2 :
  rw ← filter.tendsto_map'_iff, rw filter.map_at_top_eq,

  -- A3 :
  rw tendsto_nhds at h,

  -- A4:
  apply topological_space.tendsto_nhds_generate_from,
  rintros s smem mems,
  simp only [exists_prop, set.mem_set_of_eq] at smem,
  rcases smem with ⟨t, compt, ⟨a, opena, ha⟩⟩,
  --rw continuous_map.compact_open.gen at ha, --rw preimage_gen,
  rw ha,
  simp only [filter.mem_at_top_sets, ge_iff_le, set.mem_preimage],

  --simp_rw [← @set.mem_preimage _ _ f.comp _ _], rw preimage_gen _ compt opena,
  --simp_rw compact_open.gen, simp,

  simp_rw (set.ext_iff.1 ha _),
  simp only [set.image_subset_iff, set.mem_set_of_eq],
  simp_rw tendsto_at_top_nhds at h,
  have h' : ∀ (U : set C((zmod d)ˣ × ℤ_[p]ˣ, (zmod d)ˣ × ℤ_[p]ˣ)), is_open U → ∀ (x : (zmod d)ˣ × ℤ_[p]ˣ), f x ∈ U →
    (∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → (g n) x ∈ U),
  { rintros, apply h, assumption, assumption, },
  have h'a := h' a opena,
  simp only [set.image_subset_iff] at ha,
  have hf := (set.ext_iff.1 ha f).1 mems,
  simp only [set.mem_set_of_eq] at hf, -/
end

example (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) (g : ℕ → C((zmod d)ˣ × ℤ_[p]ˣ, (zmod d)ˣ × ℤ_[p]ˣ))
  -- (h : ∀ x : (zmod d)ˣ × ℤ_[p]ˣ, filter.tendsto (λ j : ℕ, g j x) filter.at_top (nhds (f x))) :
  : filter.tendsto (λ n : ℕ, continuous_map.comp f (g n)) filter.at_top (nhds f) :=
begin
  -- Approach 1
  apply topological_space.tendsto_nhds_generate_from,
  rintros s smem mems,
  -- convert_to (function.comp f (λ (n : ℕ), (g n).to_fun)) ⁻¹' s ∈ filter.at_top,
  simp only [exists_prop, set.mem_set_of_eq] at smem,
  rcases smem with ⟨t, compt, ⟨a, opena, ha⟩⟩,
  rw continuous_map.compact_open.gen at ha,
  simp only [filter.mem_at_top_sets, ge_iff_le, set.mem_preimage],
  set φ : C((zmod d)ˣ × ℤ_[p]ˣ, (zmod d)ˣ × ℤ_[p]ˣ) → C((zmod d)ˣ × ℤ_[p]ˣ, R) := λ g, f.comp g,
    change ∃ (a : ℕ), ∀ (b : ℕ), a ≤ b → φ (g b) ∈ s,
    simp_rw ← set.mem_preimage,
    rw ← filter.mem_at_top_sets,
    apply tendsto_nhds.1 _ _ _,
  simp_rw (set.ext_iff.1 ha _),
  simp only [set.image_subset_iff, set.mem_set_of_eq],
  -- simp_rw tendsto_at_top_nhds at h,
  -- have h' : ∀ (U : set R), is_open U → ∀ (x : (zmod d)ˣ × ℤ_[p]ˣ), f x ∈ U →
  --   (∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → (g n) x ∈ U),
  -- { rintros, apply h, assumption, assumption, },
  -- have h'a := h' a opena,
  -- simp only [set.image_subset_iff] at ha,
  have hf := (set.ext_iff.1 ha f).1 mems,
  simp only [set.mem_set_of_eq] at hf,
  suffices : ∃ (a_1 : ℕ), ∀ (b : ℕ), a_1 ≤ b → ⇑f⁻¹' a ⊆ ⇑(continuous_map.comp f (g b)) ⁻¹' a,
  { cases this with m this,
    refine ⟨m, λ b hb, _⟩,
    specialize this b hb, apply subset_trans (set.image_subset_iff.1 hf) this, },
  { simp only [continuous_map.coe_comp],
    change ∃ (a_1 : ℕ), ∀ (b : ℕ), a_1 ≤ b → ⇑f ⁻¹' a ⊆ ⇑(g b) ⁻¹' (f⁻¹' a),

    conv { congr, funext, conv { rw set.preimage_comp f _, }, },
    rw set.preimage_comp, simp_rw set.preimage_comp f _,

    rw ← filter.mem_at_top_sets,
    suffices : (∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → ∀ (x : (zmod d)ˣ × ℤ_[p]ˣ), f x ∈ a → (g n) x ∈ a),
    { cases this with N this,
      refine ⟨N, λ b hb, _⟩,
      specialize this b hb, apply this, },
    {
      rw ← filter.mem_at_top_sets,
      rw ← filter.tendsto_def,
      have openf := continuous.is_open_preimage (map_continuous f) _ opena,
      rw is_open_prod_iff at openf, }, },

  -- Approach 2
  rw tendsto_at_top_nhds,
  rintros U memU openU,
  rw topological_space.compact_opens,
  sorry
end

lemma locally_constant.inclusion_eq_coe (X : Type*) [topological_space X] (A : Type*) [normed_comm_ring A]
  (x : locally_constant X A) : (inclusion X A) x = ↑x := by { ext, refl, }

example {X Y Z : Type*} [topological_space X] [topological_space Y] [add_comm_monoid Y] (f g : C(ℤ_[p], R)) (x : ℤ_[p]) :
  f x = f.to_fun x := by { simp only [to_fun_eq_coe], }

lemma halp' {X Y Z : Type*} [topological_space X] [topological_space Y] [topological_space Z]
  (f : C(Y, Z)) (g : ℕ → C(X, Y)) : (λ (i : ℕ) (a : X), f.comp (g i) a) = (λ i : ℕ, f ∘ (g i)) :=
by { ext, refl, }

lemma halp {X Y Z : Type*} [topological_space X] [topological_space Y] [topological_space Z]
  (f : C(X, Y)) (g : ℕ → C(Y, Z)) : (λ (i : ℕ) (a : X), (g i).comp f a) = (λ i : ℕ, g i ∘ f) :=
by { ext, refl, }

lemma fn_eq_sum_char_fn [normed_algebra ℚ R] [norm_one_class R] (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) : filter.tendsto
  (λ j : ℕ, ∑ a : (zmod (d * (p^j)))ˣ, (f (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_right _ _)
     (zmod d) _ (zmod.char_p d)).to_monoid_hom a,
     rev_coe p d _ a) •
-- rev_coe p (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_left _ _) (zmod (p^j)) _ _).to_monoid_hom a)) •
     (locally_constant.char_fn R (is_clopen_units_clopen_from p d j
     ((units.chinese_remainder (nat.coprime_pow_spl p d j hd)) a)))  : C((zmod d)ˣ × ℤ_[p]ˣ, R)))
  (filter.at_top) (nhds f) :=
begin
  rw [shh' p d R hd],
  apply helper_char,
  apply topological_space.tendsto_nhds_generate_from,
  rintros s mems hs,
  rw filter.mem_at_top_sets,
  simp only [exists_prop, set.mem_set_of_eq] at mems,
  -- LC approach:
  /-rw [shh' p d R hd], rw tendsto_iff_tendsto_uniformly,
  rw halp',
  conv { congr, funext, skip, rw ← comp_id f, rw continuous_map.comp, rw coe_mk, skip, },
  apply tendsto_uniformly.comp',
  { sorry, },
  { --haveI : compact_space (units (zmod d) × units (ℤ_[p])) := sorry,
    refine @compact_space.uniform_continuous_of_continuous _ _ _ _ _ _ _ (map_continuous f), }, -/

  --rw [shh' p d R hd],
  conv { congr, funext, conv { apply_congr, skip,
    rw ← locally_constant.inclusion_eq_coe (units (zmod d) × units (ℤ_[p])) R,
    rw ← linear_map.map_smul, },
  rw ← linear_map.map_sum, rw locally_constant.inclusion_eq_coe _ _,
  rw [cont_ind_fn_eq_fun p d R (↑∑ (i : (zmod (d * p ^ j))ˣ),
        f ((units.map (zmod.cast_hom (dvd_mul_right d (p^j)) (zmod d)).to_monoid_hom) i, rev_coe p d j i) •
          (locally_constant.char_fn R _))], skip, skip,
  rw [cont_ind_fn_eq_fun p d R f], },
  --apply filter.tendsto.comp,
  rw tendsto_iff_tendsto_uniformly, simp_rw [halp], --simp,
  apply tendsto_uniformly.comp _ _,
  rw ← tendsto_iff_tendsto_uniformly,


  rw metric.tendsto_at_top, rintros ε hε,
  haveI : fact (0 < ε / 4) := fact_iff.2 (by { linarith }),
  obtain ⟨f', mem_f', distff'⟩ := loc_const_dense' (ε / 4) (cont_ind_fn p d R f),
  obtain ⟨incf, hincf⟩ := set.mem_range.1 mem_f',
  /-have := dense_inducing.tendsto_comap_nhds_nhds (measure.dense_ind_inclusion ((zmod d) × ℤ_[p]) R),
  swap 5, { exact id, },
  swap 4, { exact (inclusion _ R), },
  swap 3, { exact id, },
  swap 3, { exact (cont_ind_fn p d R f), },
  swap 3, { exact incf, },
  swap, { apply_instance, },
  simp only [locally_constant.to_continuous_map_linear_map_apply, function.comp.left_id,
    function.comp.right_id, eq_self_iff_true, forall_true_left] at this,-/
  rw ← hincf at distff', rw dist_comm at distff',
  set N : ℕ := classical.some (loc_const_eq_sum_char_fn p d R incf hd),
  refine ⟨N, λ n hn, _⟩,
  apply lt_of_le_of_lt (dist_triangle _ ((inclusion (zmod d × ℤ_[p]) R) incf) _) _,
  rw ← half_add_self ε, rw add_div,
  have div_four_lt_div_two : ε / 4 < ε / 2 := by { linarith, },
  rw dist_eq_norm, rw norm_eq_supr_norm,
  apply add_lt_add _ (lt_trans distff' div_four_lt_div_two),
  apply lt_of_le_of_lt _ div_four_lt_div_two,
  apply cSup_le _ (λ b hb, _),
  { refine set.range_nonempty _, },
  rw set.mem_range at hb,
  obtain ⟨a, ha⟩ := hb,
  rw ← ha, clear ha,
  rw cont_ind_fn, rw continuous_map.coe_sub, rw pi.sub_apply, rw coe_mk,
  rw ind_fn'', simp only,
  by_cases is_unit a.fst ∧ is_unit a.snd,
  { rw [dif_pos],
    { --conv { congr, congr, apply_congr, skip, rw is_unit.unit_spec, },
      --rw [is_unit.unit_spec],

      rw [finset.sum_eq_single_of_mem],
      sorry, },
    { apply h, }, },
  { sorry, },

  apply lt_of_le_of_lt (dist_triangle _ ((inclusion (zmod d × ℤ_[p]) R) incf) _) _,
  rw ← half_add_self ε, rw add_div,
  have div_four_lt_div_two : ε / 4 < ε / 2 := by { linarith, },
  apply add_lt_add _ (lt_trans distff' div_four_lt_div_two),
  --rw cont_ind_fn,
  rw classical.some_spec (loc_const_eq_sum_char_fn p d R incf hd),
  rw dist_eq_norm, rw norm_eq_supr_norm,
  apply lt_of_le_of_lt _ div_four_lt_div_two,
  apply cSup_le _ (λ b hb, _),
  { refine set.range_nonempty _, },
  rw set.mem_range at hb,
  obtain ⟨a, ha⟩ := hb,
  rw ← ha, clear ha,
  rw cont_ind_fn, rw continuous_map.coe_sub, rw pi.sub_apply, rw coe_mk,
  rw ind_fn'', simp only,
  by_cases is_unit a.fst ∧ is_unit a.snd,
  { rw [dif_pos],
    { --conv { congr, congr, apply_congr, skip, rw is_unit.unit_spec, },
      --rw [is_unit.unit_spec],

      rw [finset.sum_eq_single_of_mem],
      sorry, },
    { apply h, }, },
  { sorry, },

  rw filter.tendsto_def,
  have := dense_inducing.tendsto_comap_nhds_nhds,

  -- A1 :
  apply helper_char,
  -- rw uniform_continuous,
  -- rw continuous_map.tendsto_compact_open_iff_forall,
    -- simp_rw continuous_map.restrict,
    -- simp_rw continuous_map.coe_restrict,
--  apply filter.tendsto.congr_dist,
--  simp_rw [shh p d R f],
  -- A2 :
  rw continuous_map.tendsto_iff_tendsto_uniformly,

  delta tendsto_uniformly,
  intros u hu,
  -- rw metric.mem_uniformity_dist at hu,
  have cont_f := (continuous.tendsto (continuous_map.continuous f)),
  rw filter.eventually_at_top,
  simp_rw filter.tendsto_iff_forall_eventually_mem at cont_f,
  simp_rw filter.eventually at cont_f,
  have h'u : ∀ z : R, {y : R | (z, y) ∈ u} ∈ (nhds z),
  { intro z, apply mem_nhds_left z hu, },
  have cont'_f : ∀ (x : (zmod d)ˣ × ℤ_[p]ˣ), {x' : (zmod d)ˣ × ℤ_[p]ˣ | f x' ∈ {y : R | (f x, y) ∈ u}} ∈ nhds x,
  { intro x, apply cont_f x _ (h'u (f x)), },
  simp only [set.mem_set_of_eq] at cont'_f,
  simp_rw mem_nhds_iff at cont'_f,

  refine ⟨_, λ b hb, λ x, _⟩,
  swap,
  specialize cont_f x,
  have h'u := mem_nhds_left (f x) hu,
  have h2u := uniform_space.ball_mem_nhds (f x) hu,
  have cont_f' := cont_f _ h2u,
  specialize cont_f _ h'u, simp only [set.mem_set_of_eq] at cont_f,
  rw mem_nhds_iff at cont_f,
  rw mem_nhds_iff at h'u,
  rcases cont_f with ⟨t, ht, open_t, memx⟩,
  convert ht _,
  swap 2, { apply (((units.map (zmod.cast_hom (dvd_mul_right d (p^b)) (zmod d)).to_monoid_hom)
    ((units.chinese_remainder (nat.coprime_pow_spl p d b hd)).inv_fun
    ((x.1, units.map (@padic_int.to_zmod_pow p _ b).to_monoid_hom x.2))),
    rev_coe p d b ((units.chinese_remainder (nat.coprime_pow_spl p d b hd)).inv_fun
    ((x.1, units.map (@padic_int.to_zmod_pow p _ b).to_monoid_hom x.2))) )), },
  { simp only, rw continuous_map.sum_apply,
    simp_rw continuous_map.coe_smul, simp_rw pi.smul_apply,
    rw finset.sum_eq_single_of_mem,
    swap 4, { apply (units.chinese_remainder (nat.coprime_pow_spl p d b hd)).inv_fun,
      apply (x.1, units.map (@padic_int.to_zmod_pow p _ b).to_monoid_hom x.2), },
    { rw smul_eq_mul, rw locally_constant.coe_continuous_map,
      conv_rhs { rw ← mul_one (f _), },
      apply congr_arg2 _ rfl _,
      rw ← locally_constant.char_fn_one R _ (is_clopen_units_clopen_from p d b _),
      sorry, },
    { apply finset.mem_univ _, },
    { sorry, }, },
  { rw is_open_prod_iff at open_t,
    rw ← @prod.mk.eta _ _ x at memx,
    specialize open_t _ _ memx,
    rcases open_t with ⟨u, v, openu, openv, memu, memv, prod⟩,
    apply prod,
    rw is_open_induced_iff at openv,
    rcases openv with ⟨s, hs, hv⟩,
    rw is_open_prod_iff at hs,
    rw set.mem_prod,
    split,
    { sorry, },
    { simp only, rw set.ext_iff at hv,
      have hv' := (hv x.snd).2 memv,
      rw set.mem_preimage at hv',
      rw units.embed_product at hv', simp only [monoid_hom.coe_mk] at hv',
      obtain ⟨u₁, v₁, openu₁, openv₁, memu₁, memv₁, prod₁⟩ := hs _ _ hv',
      delta rev_coe, rw dif_pos,
      { apply (hv _).1, rw set.mem_preimage,
        rw units.embed_product, simp only [monoid_hom.coe_mk],
        apply prod₁, rw set.mem_prod, simp only, rw metric.is_open_iff at openu₁,
        obtain ⟨ε₁, hε₁, h₁⟩ := openu₁ _ memu₁,
        rw metric.is_open_iff at openv₁,
        obtain ⟨ε₂, hε₂, h₂⟩ := openv₁ _ memv₁, },
      sorry, }, },
  refine mem_of_mem_nhds _,
--  rw filter.has_basis.mem_uniformity_iff at hu,
  rw metric.mem_uniformity_dist at cont_f,

  rw filter.tendsto_def, intros s hs,

  -- have cont_f := (continuous.tendsto (continuous_map.continuous f)),
  -- simp_rw filter.tendsto_def at cont_f,
  -- simp_rw mem_nhds_iff at cont_f, simp_rw mem_nhds_iff at hs,
  -- cases hs with t ht, rcases ht with ⟨ht, h1, h2⟩,
  rw filter.mem_at_top_sets, simp_rw set.mem_preimage,
  simp_rw mem_nhds_iff at hs,
  cases hs with t ht, rcases ht with ⟨ht, h1, h2⟩,
  have cont_f := (continuous.tendsto (continuous_map.continuous f)),
  simp_rw filter.tendsto_def at cont_f,
  simp_rw mem_nhds_iff at cont_f,
  simp, simp_rw [mem_nhds_iff],
--  have : ∀ n : ℕ, ∀ x : zmod (d * p^n), dist x ((units.map (@zmod.cast_hom (d * p^n) _ (dvd_mul_right _ _)
 --    (zmod d) _ (zmod.char_p d)).to_monoid_hom x, rev_coe p d _ x)) < 1,
  rw metric.tendsto_at_top,
  rintros ε hε,
  simp only [ring_hom.to_monoid_hom_eq_coe],
  refine ⟨1, λ n hn, _⟩,
  rw dist_comm,
  haveI : fact (0 < ε) := fact_iff.2 hε,
  haveI : fact (0 < ε/2) := fact_iff.2 (half_pos hε),
  haveI : fact (0 < ε/4), apply fact_iff.2 _, sorry,
  have h1 : ε/4 + ε/4 = ε/2, sorry,
  rw dist_eq_norm,
  --rw ← half_add_self ε,
  --rw add_div,
  have cont_f : @continuous ((zmod d)ˣ × ℤ_[p]ˣ) R uniform_space.to_topological_space _ f,
  { refine (@continuous_def _ _ uniform_space.to_topological_space _ _).mpr _,
    intros s hs,
    sorry, },
  have f1 := (@metric.continuous_iff ((zmod d)ˣ × ℤ_[p]ˣ) R _ _ _).1 cont_f,
  rw continuous_map.norm_eq_supr_norm,
  have cont_f := (continuous.tendsto (continuous_map.continuous f)),
  have cont_f' := (continuous.tendsto' (continuous_map.continuous f)),
  --rw continuous_map.complete_space,
--  have f1 := (@metric.continuous_iff ((zmod d)ˣ × ℤ_[p]ˣ) R _ _ _).1
--    (@continuous_map_class.map_continuous _ _ _ _ _ continuous_map.continuous_map_class f),
  simp_rw filter.tendsto_def at cont_f, -- simp_rw mem_nhds_iff at cont_f,
  -- (@metric.continuous_iff ((zmod d)ˣ × ℤ_[p]ˣ) R _ _ _).1 (continuous_map.continuous f),
  -- rw continuous_map.norm_eq_supr_norm,
  have h3 : ε/2 < ε, linarith,
  apply lt_of_le_of_lt _ h3,
  refine cSup_le _ (λ m hm, _),
  { rw set.range_nonempty_iff_nonempty, apply_instance, },
  simp only [set.mem_range, continuous_map.coe_sub, locally_constant.coe_continuous_map,
    locally_constant.coe_mk, pi.sub_apply, function.comp_app, prod_map, id.def] at hm,
  cases hm with y hy,
  rw ← hy,
  simp_rw mem_nhds_iff at cont_f, specialize cont_f y,

  contrapose cont_f, push_neg, push_neg at cont_f,
  apply lt_of_le_of_lt (dist_triangle _ (inclusion ((zmod d)ˣ × ℤ_[p]ˣ) R
    ⟨c2 (ε/4) f, loc_const (ε/4) f⟩) _) _,
  have cal : ε/4 < ε/2, linarith,
  apply add_lt_add (lt_trans (real_secret p d R f (ε/4)) cal) _,
  rw dist_eq_norm,
  simp only [locally_constant.to_continuous_map_linear_map_apply],
  rw ← sub_add_sub_cancel _ f _,
  rw ← h1, apply lt_of_le_of_lt (norm_add_le _ _) _,
  rw continuous_map.norm_eq_supr_norm,
  apply lt_of_le_of_lt _ cal,
  have := real_secret p d R f (ε/4),
  rw dist_eq_norm at this,
  simp only [locally_constant.to_continuous_map_linear_map_apply] at this,
  rw continuous_map.norm_eq_supr_norm at this,
  -- apply le_of_lt,
  refine cSup_le _ (λ m hm, _),
  { rw set.range_nonempty_iff_nonempty, apply_instance, },
  simp only [set.mem_range, continuous_map.coe_sub, locally_constant.coe_continuous_map,
    locally_constant.coe_mk, pi.sub_apply, function.comp_app, prod_map, id.def] at hm,
  cases hm with y hy,
  rw ← hy,

  convert this, ext, rw ← norm_neg, apply congr_arg,
  rw continuous_map.coe_sub, rw continuous_map.coe_sub, rw pi.sub_apply, rw pi.sub_apply,
  rw neg_sub, apply congr_arg2 _ _,
  { refl, },
  rw continuous_map.coe_sum,
  rw finset.sum_eq_single_of_mem,
  swap 4, { apply (units.chinese_remainder (nat.coprime_pow_spl p d n hd)).inv_fun,
    refine (x.1, (units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom) x.2), },
  swap 2, { apply finset.mem_univ, },
  { rw continuous_map.coe_smul, rw pi.smul_apply, rw smul_eq_mul, rw ← mul_one (f x),
    apply congr_arg2,
    { apply congr_arg, apply prod.ext,
      { sorry, },
      { simp only, delta rev_coe, rw dif_pos,
        { ext, rw is_unit.unit_spec, },
        sorry, }, },
    { simp only [ring_hom.to_monoid_hom_eq_coe, mul_equiv.inv_fun_eq_symm,
      mul_equiv.symm_trans_apply, ring_equiv.to_mul_equiv_eq_coe, mul_equiv.trans_apply,
      mul_equiv.apply_symm_apply, locally_constant.coe_continuous_map],
      rw ← locally_constant.char_fn_one, delta units_clopen_from,
      simp only [ring_hom.to_monoid_hom_eq_coe, set.singleton_prod, set.mem_image,
        set.mem_preimage, set.mem_singleton_iff],
      refine ⟨x.snd, rfl, _⟩, sorry, }, },

  refine cSup_le _ (λ m hm, _),
  { rw set.range_nonempty_iff_nonempty, apply_instance, },
  simp only [set.mem_range, continuous_map.coe_sub, locally_constant.coe_continuous_map,
    locally_constant.coe_mk, pi.sub_apply, function.comp_app, prod_map, id.def] at hm,
  cases hm with y hy,
  rw ← hy, rw continuous_map.coe_sum, rw finset.sum_eq_single_of_mem,
  swap 4, { apply (units.chinese_remainder (nat.coprime_pow_spl p d n hd)).inv_fun,
    refine (y.1, (units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom) y.2), },
  { -- rw ← dist_eq_norm,
    have := real_secret p d R f (ε/4),
    rw dist_eq_norm at this,
    simp only [locally_constant.to_continuous_map_linear_map_apply] at this,
    rw continuous_map.norm_eq_supr_norm at this, },
  apply real_secret,
  conv { congr, congr, congr, skip, rw finset.sum_apply, apply_congr, skip, },
  sorry,

  -- reduced to proving ∥f(y) - c2(y)∥ ≤ ε/2
  obtain ⟨w, wT, hw⟩ := @finset_clopen_prop _ _ _ _ _ ε f infer_instance _ _ y,
  -- `w` is the unique element of `finset_clopen` to which `y` belongs
  simp only [exists_prop, exists_unique_iff_exists] at wT,
    simp only [and_imp, exists_prop, exists_unique_iff_exists] at hw,
    --have : c2 (ε/2) f y = f (c' ε f w ⟨wT.1, ⟨⟨y, wT.2⟩⟩⟩),
    obtain ⟨U, hU, wU⟩ := exists_sub_S ε f wT.1,
    -- `U` is a set of `A` which is an element of `S` and contains `f(w)`
    cases hU with z hz,
end

    { delta c2, congr',
      any_goals
      { have := classical.some_spec (exists_of_exists_unique (finset_clopen_prop (ε/2) f y)),
        simp only [exists_prop, exists_unique_iff_exists] at *,
        apply hw _ (this.1) (this.2), }, },
    --rw this,
end

  convert real_secret p d R f ε,
  ext,
  { delta c', simp only [prod_map, id.def], },

  rw [dist_eq_norm, continuous_map.norm_eq_supr_norm],
  apply gt_of_gt_of_ge (half_lt_self hε),
  refine cSup_le _ (λ m hm, _),
  { rw set.range_nonempty_iff_nonempty, apply_instance, },
  { cases hm with y hy,
    simp only [continuous_map.coe_sub, locally_constant.coe_mk,
      locally_constant.to_continuous_map_linear_map_apply, pi.sub_apply,
      locally_constant.coe_continuous_map] at hy,
    rw ←hy,
    obtain ⟨w, wT, hw⟩ := finset_clopen_prop ε f y, },
  --simp only [ring_hom.to_monoid_hom_eq_coe, ge_iff_le,
  --  locally_constant.to_continuous_map_linear_map_apply],

  simp_rw [shh' p d R f],

  simp only [ring_hom.to_monoid_hom_eq_coe],

  --simp only [ring_hom.to_monoid_hom_eq_coe],
  apply filter.tendsto.comp _ _,
  { exact (nhds (continuous_map.prod_map (continuous_map.id _) (continuous_map.id _))), },
  { apply h1, },
  { delta filter.tendsto,
    --convert filter.tendsto.prod_map _ _,
    sorry, },

  swap, { exact C((zmod d)ˣ × ℤ_[p]ˣ, (zmod d)ˣ × ℤ_[p]ˣ), },
  swap 2, { refine (λ n : ℕ, ⟨prod.map id (rev_coe p ∘
    (units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom )), hmm p d n⟩), },
  swap 2, { refine (λ g, continuous_map.comp f g), },
  { ext, simp, },
  { refine (nhds (continuous_map.prod_map (continuous_map.id _) (continuous_map.id _))), },
  { have : f.comp (continuous_map.prod_map (continuous_map.id _) (continuous_map.id _)) = f, sorry,
    conv { congr, skip, skip, rw ←this, },

    sorry, },/-have : f.comp (continuous_map.prod_map (continuous_map.id _) (continuous_map.id _)) = f,
    { ext, simp only [continuous_map.comp_apply], congr, rw continuous_map.prod_eval,
      sorry, },
    rw ← this, }, -/
  {
    sorry, },
  rw padic_int.lim_nth_hom_one,
  rw @metric.tendsto_at_top _ _ _ _ _ _ _,
  simp_rw [dist_eq_norm],
  rintros ε hε,
  have cont := (@metric.continuous_iff _ _ _ _ f).1 (continuous_map.continuous f) _ ε hε,
  intros s hs,
  rw filter.mem_map,
end

  have : ∀ (x : (zmod d)ˣ × ℤ_[p]ˣ) (n : ℕ), ∑ (a : (zmod d)ˣ × (zmod (p ^ n))ˣ), f (a.fst, rev_coe p a.snd) •
    (locally_constant.char_fn R (is_clopen_units_clopen_from p d n a)) x =
    f (x.1, (rev_coe p ((units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom) x.2))),
  sorry,
  have f2 : ∀ n : ℕ, ∑ (a : (zmod d)ˣ × (zmod (p ^ n))ˣ), f (a.fst, rev_coe p a.snd) •
    (locally_constant.char_fn R (is_clopen_units_clopen_from p d n a) : C((zmod d)ˣ × ℤ_[p]ˣ, R)) =
    ⟨f ∘ (prod.map id ((rev_coe p) ∘ (units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom ))), _⟩,
  swap 3, { simp only [ring_hom.to_monoid_hom_eq_coe, auto_param_eq], continuity,
      apply continuous.prod_mk _ _,
    { simp only [id.def],  apply continuous_fst, },
    { continuity,
      sorry,
      sorry, }, },
  sorry,
  conv { congr, funext, rw f2 n, },
  simp only [ring_hom.to_monoid_hom_eq_coe],
  -- convert_to filter.tendsto (λ (n : ℕ), f ∘ prod.map id (rev_coe p ∘ (units.map
  --   ↑(padic_int.to_zmod_pow n)))) filter.at_top (nhds f),
  convert filter.tendsto.comp _ _,
  swap, { exact C((zmod d)ˣ × ℤ_[p]ˣ, (zmod d)ˣ × ℤ_[p]ˣ), },
  swap 2, { refine (λ n : ℕ, ⟨prod.map id (rev_coe p ∘
    (units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom )), _⟩), sorry, },
  swap 2, { refine (λ g, continuous_map.comp f g), },
  { ext, simp, },
  { refine (nhds (⟨prod.map id id, _⟩)), sorry, },

  --convert continuous.tendsto (continuous_map.continuous f) _,
  swap, {  },
  rw padic_int.lift_self,
  ext,
  rw f2,
  rw filter.tendsto_def,
  rintros s hs,
  simp only [filter.mem_at_top_sets, ge_iff_le, set.mem_preimage],
  have := continuous.tendsto (continuous_map.continuous f),
  rw @metric.tendsto_at_top _ _ _ _ _ _ _, -- can use top' if you want n > N
  intros ε hε,
  simp_rw [dist_eq_norm', continuous_map.norm_eq_supr_norm],
  rw continuous_iff
  have cont := (@metric.continuous_iff _ _ _ _ f).1 (continuous_map.continuous f) _ ε hε,
  -- convert_to ∃ (N : ℕ), ∀ (n : ℕ), n > N → ∥f - (∑ (a : (zmod d)ˣ × (zmod (p ^ n))ˣ),
  --   f (a.fst, rev_coe p _ a.snd) • (locally_constant.char_fn R (is_clopen_units_clopen_from p d n a))) ∥ < ε,
  --simp_rw dif_pos _,
  -- conv { congr, funext, find ∥f - dite (_ ≠ 0) (λ (h : _ ≠ 0), ∑ (a : (zmod d)ˣ × (zmod (p ^ _))ˣ),
  --         f (a.fst, rev_coe p h a.snd) • ↑(locally_constant.char_fn R _)) (λ (h : ¬_ ≠ 0), 0)∥ {apply_congr dif_pos _}, },
  sorry,
end
-- work with tendsto instead of lim, it is easier because the other implication in the iff
-- statement is hard

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
  ((r • f : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) : C((zmod d)ˣ × ℤ_[p]ˣ, R)) = r • (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) :=
begin
  ext,
  simp only [locally_constant.coe_continuous_map, locally_constant.coe_smul,
    continuous_map.coe_smul],
end

--v imp, make a lemma!
example (f : (zmod d) → locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) (a : ((zmod d)ˣ × ℤ_[p]ˣ)) :
  (∑ (i : zmod d), f i) a = (∑ (i : zmod d), f i a) :=
begin
  rw [← locally_constant.coe_fn_add_monoid_hom_apply, add_monoid_hom.map_sum
    (@locally_constant.coe_fn_add_monoid_hom ((zmod d)ˣ × ℤ_[p]ˣ) R _ _) f (finset.univ),
    finset.sum_apply],
  simp_rw locally_constant.coe_fn_add_monoid_hom_apply,
end

example (f : (zmod d) → locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) :
  ∑ (i : zmod d), (f i : C(((zmod d)ˣ × ℤ_[p]ˣ), R)) = (∑ (i : zmod d), f i : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) :=
begin
  symmetry,
  ext,
  rw continuous_map.coe_sum,
  rw locally_constant.coe_continuous_map,
  rw finset.sum_apply,
  conv_rhs { congr, skip, funext, rw locally_constant.coe_continuous_map, },
  rw [← locally_constant.coe_fn_add_monoid_hom_apply, add_monoid_hom.map_sum
    (@locally_constant.coe_fn_add_monoid_hom ((zmod d)ˣ × ℤ_[p]ˣ) R _ _) f (finset.univ),
    finset.sum_apply],
  simp_rw locally_constant.coe_fn_add_monoid_hom_apply,
end

variables [normed_algebra ℚ_[p] R] [fact (0 < m)]

noncomputable abbreviation used_map (n : ℕ) : C((zmod d)ˣ × ℤ_[p]ˣ, R) :=
⟨(units.coe_hom R) ∘ (χ * teichmuller_character_mod_p_change_level p d R m) ∘
  ((units.map (zmod.chinese_remainder (nat.coprime_pow_spl p d m hd)).symm.to_monoid_hom) ∘
  (mul_equiv.prod_units.symm)) ∘ prod.map (monoid_hom.id (zmod d)ˣ)
  (units.map ↑(@padic_int.to_zmod_pow p _ m)) * ((neg_pow' p d R (n - 1)).to_monoid_hom),
  by { simp, apply cont_paLf', }⟩

lemma bernoulli_measure'_eval_char_fn [normed_algebra ℚ R] [norm_one_class R] (n : ℕ)
  (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  (bernoulli_measure' p d R hc hc' hd na).val (locally_constant.char_fn R
  (is_clopen_units_clopen_from p d n a)) =
  (algebra_map ℚ R (E_c p d hc n ((zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).inv_fun
  ((a.1 : zmod d), (a.2 : zmod (p^n))))) ) := sorry

/-example {X : Type*} [topological_space X] [t2_space X] [add_comm_monoid X] [has_continuous_add X]
  (f g : ℕ → X) :
  lim filter.at_top (λ x : ℕ, f x + g x) = lim filter.at_top (λ x : ℕ, f x) + lim filter.at_top (λ x : ℕ, g x) :=
by { --change lim filter.at_top ((λ (x : ℕ), f x) + (λ x : ℕ, g x)) = _, simp only,
  rw @filter.tendsto.lim_eq _ _ _ _ (lim filter.at_top f + lim filter.at_top g) filter.at_top _ _ _,
  { exact filter.at_top_ne_bot, },
  { apply filter.tendsto.add,
    any_goals { simp, apply tendsto_nhds_lim, sorry, }, }, } -/

lemma nat_spec' (p : ℕ → Prop) (h : ({n : ℕ | ∀ (x : ℕ), x ≥ n → p x}).nonempty) (x : ℕ)
  (hx : x ≥ Inf {n : ℕ | ∀ (x : ℕ) (hx : x ≥ n), p x}) : p x := nat.Inf_mem h x hx

noncomputable def U_def [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (j : ℕ) :=
  ∑ (x : (zmod (d * p ^ j))ˣ),
  (used_map p d R m hd χ n) ((units.map (zmod.cast_hom (dvd_mul_right d (p^j)) (zmod d)).to_monoid_hom) x,
  rev_coe p d _ x) •
  -- rev_coe p ((units.map (zmod.cast_hom (dvd_mul_left (p^j) d) (zmod (p ^ j))).to_monoid_hom) x)) •
  (algebra_map ℚ R) (int.fract (↑x / (↑d * ↑p ^ j)))

lemma U [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) :
  filter.tendsto (λ j : ℕ, U_def p d R m hd χ n j)
  /-∑ (x : (zmod (d * p ^ j))ˣ),
  (used_map p d R m hd χ n) ((units.map (zmod.cast_hom (dvd_mul_right d (p^j)) (zmod d)).to_monoid_hom) x,
  rev_coe p ((units.map (zmod.cast_hom (dvd_mul_left (p^j) d) (zmod (p ^ j))).to_monoid_hom) x)) •
  (algebra_map ℚ R) (int.fract (↑(((zmod.chinese_remainder (nat.coprime_pow_spl p d j hd)).inv_fun
  (↑(((units.chinese_remainder (nat.coprime_pow_spl p d j hd)) x).fst), ↑(((units.chinese_remainder
  (nat.coprime_pow_spl p d j hd)) x).snd))).val) / (↑d * ↑p ^ j))))-/
  -- ∑ (x : (zmod d)ˣ × (zmod (p ^ j))ˣ),
  -- (used_map p d R m hd χ n) (x.fst, rev_coe p x.snd) • (algebra_map ℚ R)
  -- (int.fract (↑(((zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).inv_fun
  -- (↑(x.fst), ↑(x.snd))).val) / (↑d * ↑p ^ j))))
  filter.at_top (nhds ((1 - asso_dirichlet_character (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) n)) ) := sorry

noncomputable def M2 [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (ε : ℝ) (hε : 0 < ε) : ℕ :=
Inf {z : ℕ | ∀ k ≥ z, ∥(U_def p d R m hd χ n k) - ((1 - asso_dirichlet_character (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) n))∥ < ε}

lemma M2_spec [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (ε : ℝ) (hε : 0 < ε) (k : ℕ)
  (hk : M2 p d R m hd χ n ε hε ≤ k) :
  ∥(U_def p d R m hd χ n k) - ((1 - asso_dirichlet_character (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) n))∥ < ε :=
begin
  delta M2 at hk,
  apply nat_spec' _ _ k hk,
  have := metric.tendsto_at_top.1 (U p d R m hd χ n) ε hε,
  simp_rw dist_eq_norm at this,
  refine ⟨classical.some this, classical.some_spec this⟩,
end

/-lemma V_1 [normed_algebra ℚ R] [norm_one_class R] (n j : ℕ) : ∑ (x : (zmod d)ˣ × (zmod (p ^ j))ˣ),
  (used_map p d R m hd χ n) (x.fst, rev_coe p x.snd) • (algebra_map ℚ R) (↑c * int.fract
  (↑((((c : zmod (d * p^(2 * n))) : zmod (d * p^n)))⁻¹ * (zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).inv_fun
  (↑(x.fst), ↑(x.snd))) / (↑d * ↑p ^ j)))-/

example (k : ℕ) (hk : m ≤ k) : d * p^m ∣ d * p^k := mul_dvd_mul_left d (pow_dvd_pow p hk)
example (a b c : ℚ) : a * (b * c) = a * c * b := by rw [mul_comm b c, mul_assoc]
lemma monoid_hom.mul {X Y : Type*} [mul_one_class X] [comm_monoid Y] (f g : X →* Y) :
  ((f * g : X →* Y) : X → Y) = (f * g : X → Y) := by { ext, rw monoid_hom.mul_apply,
  simp only [pi.mul_apply], }

lemma weight_space.to_monoid_hom_apply {X A : Type*} [mul_one_class X] [topological_space X]
  [topological_space A] [mul_one_class A] (w : weight_space X A) :
  (w.to_monoid_hom : X → A) = w.to_fun := rfl

lemma zmod.cast_cast {n : ℕ} [fact (0 < n)] (l m : ℕ) (a : zmod n) (h1 : l ∣ m) :
  ((a : zmod m) : zmod l) = (a : zmod l) :=
begin
  rw ← zmod.nat_cast_val a, rw zmod.cast_nat_cast h1,
  { rw zmod.nat_cast_val, },
  { refine zmod.char_p _, },
end

lemma used_map_ext_h1 [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (k : ℕ) (hk : m ≤ k)
  (a : (zmod (d * p ^ k))ˣ) : (((a : zmod (d * p^k)) : zmod d), (@padic_int.to_zmod_pow p _ m)
  (zmod.cast_hom (dvd_mul_left (p^k) d) (zmod (p^k)) (a : zmod (d * p^k)))) =
  ((zmod.chinese_remainder (nat.coprime_pow_spl p d m hd)) ((a : zmod (d * p^k)) : zmod (d * p^m))) :=
begin
  apply prod.ext,
  { rw zmod.chinese_remainder, simp only [ring_equiv.coe_mk, zmod.cast_hom_apply,
      prod.fst_zmod_cast],
    rw zmod.cast_cast _ _ (a : zmod (d * p^k)) (dvd_mul_right d (p^m)), },
  { rw zmod.chinese_remainder,
    simp only [zmod.cast_hom_apply, ring_equiv.coe_mk, prod.snd_zmod_cast],
    rw ← padic_int.zmod_cast_comp_to_zmod_pow m k hk,
    rw ring_hom.comp_apply,
    simp only [zmod.nat_cast_val, zmod.ring_hom_map_cast, zmod.cast_hom_apply],
    rw zmod.cast_cast _ _ (a : zmod (d * p^k)) (pow_dvd_pow p hk),
    rw zmod.cast_cast _ _ (a : zmod (d * p^k)) (dvd_mul_left (p^m) d), },
end

lemma used_map_ext_1 [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (k : ℕ) (hk : m ≤ k) (a : (zmod (d * p ^ k))ˣ) :
  (units.map (zmod.chinese_remainder (nat.coprime_pow_spl p d m hd)).symm.to_monoid_hom)
  ((mul_equiv.prod_units.symm)
  (prod.map (monoid_hom.id (zmod d)ˣ) (units.map ↑(@padic_int.to_zmod_pow p _ m))
  ((units.map ↑(zmod.cast_hom (dvd_mul_right d (p^k)) (zmod d))) a, rev_coe p d _ a))) =
  -- ((units.map (zmod.cast_hom (dvd_mul_left (p^k) d) (zmod (p ^ k))).to_monoid_hom) a)))) =
  (units.map (zmod.cast_hom (show d * p^m ∣ d * p^k, from mul_dvd_mul_left d (pow_dvd_pow p hk))
  (zmod (d * p ^ m))).to_monoid_hom) a :=
begin
  simp only [ring_hom.to_monoid_hom_eq_coe, prod.map_mk, monoid_hom.id_apply],
  delta rev_coe,
  simp only [zmod.cast_hom_apply, ring_hom.coe_monoid_hom, units.coe_map, ne.def, coe_coe, dite_not],
  rw dif_neg, ext,
  rw units.coe_map, simp_rw units.coe_map _ a,
  { delta ring_equiv.to_monoid_hom, rw ring_hom.to_monoid_hom_eq_coe,
    simp only [zmod.cast_hom_apply, ring_hom.coe_monoid_hom],
    rw mul_equiv.prod_units, simp,
    rw ring_equiv.to_ring_hom_eq_coe,
    rw ring_equiv.coe_to_ring_hom,
    rw ← ring_equiv.symm_apply_apply (zmod.chinese_remainder (nat.coprime_pow_spl p d m hd))
      ((a : zmod (d* p^k)) : zmod (d * p^m)),
    apply congr_arg (zmod.chinese_remainder (nat.coprime_pow_spl p d m hd)).symm,
    rw is_unit.unit_spec,
    apply used_map_ext_h1 p d R m hd n k hk, },
  { intro h, rw h at hk, rw nat.le_zero_iff at hk, revert hk,
      apply ne_zero_of_lt (fact.out _), exact 0, apply_instance, apply_instance, },
end
.
example {R S T : Type*} [semiring R] [semiring S] [semiring T] (f : R →+* S) (g : S →+* T) : (ring_hom.comp g  f).to_monoid_hom = g.to_monoid_hom.comp f.to_monoid_hom := rfl

lemma h3 {M N : Type*} [mul_one_class M] [comm_group N] (f : M →*N) (n : ℕ) (a : M) : (f^n) a = (f a)^n := rfl

-- this should already be somewhere ; also not needed
lemma h2 (k : ℕ) (χ : dirichlet_character R k) (n : ℕ) (a : (zmod k)ˣ) : (χ^n) a = (χ a)^n :=
begin
  induction n with d hd,
  { simp only [pow_zero, monoid_hom.one_apply], },
  { rw pow_succ', rw pow_succ', simp only [monoid_hom.mul_apply, mul_left_inj], rw hd, },
end

lemma teichmuller_character_mod_p_change_level_def :
  teichmuller_character_mod_p_change_level p d R m = dirichlet_character.change_level (((units.map ((algebra_map ℚ_[p] R).comp
  (padic_int.coe.ring_hom)).to_monoid_hom).comp (teichmuller_character_mod_p p) : dirichlet_character R p)⁻¹ )
  (begin apply dvd_mul_of_dvd_right (dvd_pow_self p (ne_of_gt (fact.out _))), apply_instance, end) := rfl

lemma h4 {R S T : Type*} [non_assoc_semiring R] [non_assoc_semiring S] [non_assoc_semiring T]
  (f : R →+* S) (g : S →+* T) : (g.comp f).to_monoid_hom = monoid_hom.comp g.to_monoid_hom f.to_monoid_hom :=
  by { ext, simp, }

lemma h5 [normed_algebra ℚ R] [norm_one_class R] (n k : ℕ) (hn : 1 ≤ n) (hk : m ≤ k)
  (a : (zmod (d * p ^ k))ˣ) : ((units.map (@padic_int.to_zmod p _).to_monoid_hom)
  (rev_coe p ((units.map (zmod.cast_hom (dvd_mul_left (p^k) d) (zmod (p ^ k))).to_monoid_hom) a))) =
  (units.map ↑(zmod.cast_hom (dvd_mul_of_dvd_right (@dvd_pow_self _ _ p m (ne_of_gt (fact.out _))) d) (zmod p)))
  ((units.map (zmod.cast_hom (show d * p ^ m ∣ d * p ^ k, from mul_dvd_mul_left d (pow_dvd_pow p hk))
  (zmod (d * p ^ m))).to_monoid_hom) a) :=
begin
  delta rev_coe,
  simp only [zmod.cast_hom_apply, ring_hom.coe_monoid_hom, units.coe_map, ne.def, coe_coe, dite_not],
  rw dif_neg,
  { ext, rw units.coe_map, rw is_unit.unit_spec,
    conv_rhs { rw ← monoid_hom.comp_apply, },
    rw ← units.map_comp,
    simp_rw units.coe_map _ a, simp,
    rw ←zmod.int_cast_cast,
    change (ring_hom.comp padic_int.to_zmod (int.cast_ring_hom ℤ_[p]))
      (((a : zmod (d * p^k)) : zmod (p^k)) : ℤ) = _,
    rw ring_hom.eq_int_cast _ (((a : zmod (d * p^k)) : zmod (p^k)) : ℤ),
    rw zmod.int_cast_cast,
    haveI : fact (0 < d * p^k) := fact_iff.2 (mul_prime_pow_pos p d k),
    rw zmod.cast_cast p (p^k) _ (dvd_pow_self p (ne_of_gt (lt_of_lt_of_le (fact.out _) hk))),
    rw zmod.cast_cast p (d * p^m) _ (dvd_mul_of_dvd_right (dvd_pow_self p (ne_of_gt (fact.out _))) d),
    { apply_instance, },
    { apply_instance, }, },
  { intro h, rw h at hk, rw nat.le_zero_iff at hk, revert hk,
    apply ne_zero_of_lt (fact.out _), exact 0, apply_instance, apply_instance, },
end

lemma used_map_ext_2 [normed_algebra ℚ R] [norm_one_class R] (n k : ℕ) (hn : 1 ≤ n) (hk : m ≤ k)
  (a : (zmod (d * p ^ k))ˣ) :
  ↑((teichmuller_character_mod_p_change_level p d R m) ((units.map (zmod.chinese_remainder (nat.coprime_pow_spl p d m hd)).symm.to_monoid_hom)
  ((mul_equiv.prod_units.symm) (prod.map (monoid_hom.id (zmod d)ˣ) (units.map ↑(@padic_int.to_zmod_pow p _ m))
  ((units.map (zmod.cast_hom (dvd_mul_right d (p^k)) (zmod d)).to_monoid_hom) a,
  rev_coe p d _ a))))) *
  -- rev_coe p ((units.map (zmod.cast_hom (dvd_mul_left (p^k) d) (zmod (p ^ k))).to_monoid_hom) a)))))) *
  ((algebra_map ℚ_[p] R).to_monoid_hom).comp (padic_int.coe.ring_hom.to_monoid_hom.comp ((units.coe_hom ℤ_[p]).comp
  (monoid_hom.comp (monoid_hom.comp (teichmuller_character_mod_p p)⁻¹ (units.map (@padic_int.to_zmod p _).to_monoid_hom))
    (monoid_hom.snd (zmod d)ˣ ℤ_[p]ˣ)^(n - 1))))
  ((units.map (zmod.cast_hom (dvd_mul_right d (p^k)) (zmod d)).to_monoid_hom) a,
  rev_coe p d _ a) =
-- rev_coe p ((units.map (zmod.cast_hom (dvd_mul_left (p^k) d) (zmod (p ^ k))).to_monoid_hom) a)) =
  ((teichmuller_character_mod_p_change_level p d R m ^ n) ((units.map (zmod.cast_hom (show d * p ^ m ∣ d * p ^ k, from mul_dvd_mul_left d (pow_dvd_pow p hk)) (zmod (d * p ^ m))).to_monoid_hom) a)).val :=
begin
  conv_rhs { rw [← nat.add_sub_cancel_left 1 n, nat.add_sub_assoc hn _, pow_add, pow_one,
    monoid_hom.mul_apply], },
  rw units.val_eq_coe, rw units.coe_mul,
  apply congr_arg2 _ _ _,
  { apply congr_arg, apply congr_arg, rw ring_hom.to_monoid_hom_eq_coe  (zmod.cast_hom _ (zmod d)),
    apply used_map_ext_1 p d R m hd n k hk a, },
  { rw teichmuller_character_mod_p_change_level_def,
    -- simp,
    -- delta does not work without the simp above, for which squeeze_simp does not work; lot of work needs to be repeated because of simp
    rw dirichlet_character.change_level,
    rw h2,
    conv_rhs { rw monoid_hom.comp_apply, }, rw monoid_hom.inv_apply, -- rw inv_pow,
    rw ← monoid_hom.comp_assoc, rw ← h4,
    rw monoid_hom.comp_apply, rw monoid_hom.comp_apply, rw units.coe_hom_apply,
    rw ← units.coe_map, rw h3, rw monoid_hom.map_pow, congr,
    apply eq_inv_of_mul_eq_one_left,
    simp_rw monoid_hom.comp_apply,
    rw ← monoid_hom.map_mul,
    convert monoid_hom.map_one (units.map ((algebra_map ℚ_[p] R).comp padic_int.coe.ring_hom).to_monoid_hom),
    rw monoid_hom.inv_apply, rw ← monoid_hom.map_inv, rw ← monoid_hom.map_mul,
    convert monoid_hom.map_one _,
    rw monoid_hom.coe_snd, rw h5 p d R m n k hn hk a, rw inv_mul_eq_one, },
end

lemma used_map_ext_3 [normed_algebra ℚ R] [norm_one_class R] (n k : ℕ) (hn : 1 ≤ n) (hk : m ≤ k) (a : (zmod (d * p ^ k))ˣ) :
  ((algebra_map ℚ_[p] R).to_monoid_hom.comp (padic_int.coe.ring_hom.to_monoid_hom.comp
  ((units.coe_hom ℤ_[p]).comp(monoid_hom.snd (zmod d)ˣ ℤ_[p]ˣ ^ (n - 1)))))
  ((units.map (zmod.cast_hom (dvd_mul_right d (p^k)) (zmod d)).to_monoid_hom) a,
  rev_coe p d _ a) =
-- rev_coe p ((units.map (zmod.cast_hom (dvd_mul_left (p^k) d) (zmod (p ^ k))).to_monoid_hom) a)) =
  ↑((a : zmod (d * p^k)).val) ^ (n - 1) :=
begin
  simp only [ring_hom.to_monoid_hom_eq_coe, monoid_hom.coe_comp, ring_hom.coe_monoid_hom,
    function.comp_app, units.coe_hom_apply],
  rw h3, rw units.coe_pow, rw ring_hom.map_pow, rw ring_hom.map_pow, congr,
  rw monoid_hom.coe_snd, delta rev_coe, rw dif_pos,
  { rw ← map_nat_cast ((algebra_map ℚ_[p] R).comp (padic_int.coe.ring_hom)),
    rw ring_hom.comp_apply, apply congr_arg, apply congr_arg,
    rw is_unit.unit_spec,
    simp only [coe_coe, units.coe_map, ring_hom.coe_monoid_hom, zmod.cast_hom_apply,
      zmod.nat_cast_val],
    rw ←zmod.int_cast_cast, conv_rhs { rw ←zmod.int_cast_cast },
    apply congr_arg, apply congr_arg,
    rw ring_hom.eq_int_cast _ (((a : zmod (d * p^k)) : zmod (p^k)) : ℤ),
    rw zmod.int_cast_cast,
    sorry, },
  { intro h, rw h at hk, rw nat.le_zero_iff at hk, revert hk,
    apply ne_zero_of_lt (fact.out _), exact 0, apply_instance, apply_instance, },
end

lemma used_map_ext [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (k : ℕ) (hn : 1 ≤ n) (hk : m ≤ k)
  (a : (zmod (d * p^k))ˣ) :
  (used_map p d R m hd χ n) ((units.map (zmod.cast_hom (dvd_mul_right d (p^k)) (zmod d)).to_monoid_hom) a,
  rev_coe p d _ a) =
-- rev_coe p ((units.map (zmod.cast_hom (dvd_mul_left (p^k) d) (zmod (p ^ k))).to_monoid_hom) a)) =
  ((χ * (teichmuller_character_mod_p_change_level p d R m)^n)
  (units.map (zmod.cast_hom (show d * p^m ∣ d * p^k, from mul_dvd_mul_left d (pow_dvd_pow p hk))
  (zmod (d * p^m))).to_monoid_hom a)) * (((a : zmod (d * p^k)).val)^(n - 1) : R) :=
  -- ((algebra_map ℚ_[p] R)) (((@padic_int.coe.ring_hom p _)) ((units.coe_hom ℤ_[p])
  -- (rev_coe p ((units.map (zmod.cast_hom (dvd_mul_left (p^k) d) (zmod (p^k))).to_monoid_hom) a^(n - 1))))) :=
begin
  delta used_map, delta neg_pow', delta neg_pow'_to_hom, rw ← continuous_map.to_fun_eq_coe,
  simp_rw weight_space.to_monoid_hom_apply _,
  rw monoid_hom.to_fun_eq_coe,
  rw mul_pow,
  --rw monoid_hom.map_mul,
  --rw function.mul_comp,
  repeat { rw monoid_hom.comp_mul, },
  repeat { rw monoid_hom.mul_apply, },
  rw mul_comm ((algebra_map ℚ_[p] R).to_monoid_hom.comp
  (padic_int.coe.ring_hom.to_monoid_hom.comp
     ((units.coe_hom ℤ_[p]).comp (monoid_hom.snd (zmod d)ˣ ℤ_[p]ˣ ^ (n - 1)))))  _,
  simp only [monoid_hom.mul, pi.mul_apply, function.comp_apply],
  rw [monoid_hom.map_mul, units.coe_hom_apply, units.coe_hom_apply],
  rw ← mul_assoc,
  rw mul_assoc _ (↑((teichmuller_character_mod_p_change_level p d R m) _)) _,
  congr,
  { apply used_map_ext_1 p d R m hd n k hk _, },
  { -- hn used here
    apply used_map_ext_2 p d R m hd n k hn hk _, },
  { apply used_map_ext_3 p d R m n k hn hk a, },
  --conv_lhs { congr, rw mul_comm, },
  --rw mul_comm ((algebra_map ℚ_[p] R).to_monoid_hom.comp _) _,
  /-simp only [monoid_hom.mul, pi.mul_apply, function.comp_apply],
  rw [monoid_hom.map_mul, units.coe_hom_apply, units.coe_hom_apply],
  rw ← mul_assoc,
  rw monoid_hom.comp_apply,
  rw ring_hom.to_monoid_hom_eq_coe _,
  simp only,
  --rw used_map_ext_1 p d R m hd n k hk _,
  rw mul_assoc _ (↑((teichmuller_character_mod_p_change_level p d R m)
    ((units.map (zmod.chinese_remainder (nat.coprime_pow_spl p d m hd)).symm.to_monoid_hom)
    ((mul_equiv.prod_units.symm) (prod.map (monoid_hom.id (zmod d)ˣ) (units.map ↑(padic_int.to_zmod_pow m))
    ((units.map ↑(zmod.cast_hom _ (zmod d))) a, rev_coe p ((units.map
    (zmod.cast_hom (dvd_mul_left (p^k) d) (zmod (p ^ k))).to_monoid_hom) a))))))) _,
  congr,
  { apply used_map_ext_1 p d R m hd n k hk _, },
  { -- hn used here
    apply used_map_ext_2, apply hn, },
  { sorry, },   -/
end
-- #exit
variable (c)
noncomputable def V_def [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (j : ℕ) :=
∑ (x : (zmod (d * p ^ j))ˣ), (used_map p d R m hd χ n)
  ((units.map (zmod.cast_hom (dvd_mul_right d (p^j)) (zmod d)).to_monoid_hom) x,
  rev_coe p d _ x) •
-- rev_coe p ((units.map (zmod.cast_hom (dvd_mul_left (p^j) d) (zmod (p ^ j))).to_monoid_hom) x)) •
  (algebra_map ℚ R) (↑c * int.fract (((((c : zmod (d * p^(2 * j))))⁻¹ : zmod (d * p^(2 * j))) * x : ℚ) / (↑d * ↑p ^ j)))

lemma zmod.cast_le_self (a n : ℕ) [fact (0 < n)] : (a : zmod n).val ≤ a :=
begin
  by_cases a < n,
  { apply le_of_eq, rw zmod.val_cast_of_lt h, },
  { simp at h,
    apply le_of_lt, apply lt_of_lt_of_le _ h, apply zmod.val_lt, },
end

lemma coprime_mul_pow (hc : c.gcd p = 1) (hc' : c.gcd d = 1) (n : ℕ) : c.coprime (d * p^n) :=
nat.coprime.mul_right hc' (nat.coprime_pow_spl p c n hc)

variables (hc) (hc')

noncomputable def V_h_def [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (k : ℕ) :=
dite (m ≤ k) (λ hk, ∑ (x : (zmod (d * p ^ k))ˣ), ↑((χ * teichmuller_character_mod_p_change_level p d R m ^ n)
((units.map (zmod.cast_hom (show d * p ^ m ∣ d * p ^ k, from mul_dvd_mul_left d (pow_dvd_pow p hk)) (zmod (d * p ^ m))).to_monoid_hom) x)) *
(↑(c ^ (n - 1)) * (algebra_map ℚ R) (↑(n - 1) * (↑d * (↑p ^ k *
(↑⌊↑((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val) / ((d : ℚ) * ↑p ^ k)⌋ *
(↑d * (↑p ^ k * int.fract (((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val : ℕ) /
((d : ℚ) * ↑p ^ k))))^(n - 1 - 1)))) * (↑c * int.fract ((((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k)))
* (x : ℚ)) / ((d : ℚ) * ↑p ^ k))))))
(λ hk, 0)
-- ∑ (a : (zmod (d * p ^ k))ˣ), (units.coe_hom R ((χ * (teichmuller_character_mod_p_change_level p d R m)^n)
--   (units.map (zmod.cast_hom (show d * p^m ∣ d * p^k, by sorry) (zmod (d * p^m))).to_monoid_hom a))) *
--   ((algebra_map ℚ_[p] R)) (((@padic_int.coe.ring_hom p _)) ((units.coe_hom ℤ_[p])
--   (rev_coe p ((units.map (zmod.cast_hom (dvd_mul_left (p^k) d) (zmod (p^k))).to_monoid_hom) a^n))))
--   * (↑(((zmod.chinese_remainder (nat.coprime_pow_spl p d k hd)).inv_fun
--   (↑(((units.chinese_remainder (nat.coprime_pow_spl p d k hd)) ((zmod.unit_of_coprime c sorry)⁻¹ * a)).fst),
--   ↑(((units.chinese_remainder (nat.coprime_pow_spl p d k hd)) ((zmod.unit_of_coprime c sorry)⁻¹ * a)).snd))).val))^(n - 1) *
--   ((algebra_map ℚ R) (int.floor (((zmod.unit_of_coprime c (coprime_mul_pow p d c hc hc' (2 * k)))⁻¹.val * a.val : ℚ) / (d * p^k) : ℚ)))

noncomputable def M4 : ℕ := Inf { k : ℕ | c < d * p^k }

lemma M4_spec : c < d * p^(M4 p d c) := sorry

lemma exists_V_h1_1 [normed_algebra ℚ R] [norm_one_class R] (k : ℕ)
  (x : (zmod (d * p^k))ˣ) : ∃ z : ℕ,
  c * ((c : zmod (d * p^(2 * k)))⁻¹.val) = 1 + z * (d * p^(2 * k)) :=
begin
  by_cases (d * p^(2 * k)) = 1,
  { rw h, simp_rw mul_one, simp_rw add_comm, sorry, },
  have h' : d * p^(2 * k) > 1, sorry,
  have h : (1 : zmod (d * p^(2 * k))).val = 1,
  { have : ((1 : ℕ) : zmod (d * p^(2 * k))) = 1, simp,
    rw ← this,
    rw zmod.val_cast_of_lt h', },
  conv { congr, funext, find 1 {rw ← h}, },
  conv { congr, funext, rw mul_comm z _, },
--  simp_rw mul_comm _ (d * p^(2 * k)),
  apply (zmod.nat_coe_zmod_eq_iff _ _ _).1 _,
  { apply imp p d _, },
  { rw nat.cast_mul, rw zmod.nat_cast_val, rw zmod.cast_inv _ _ _ _ _,
    rw zmod.cast_nat_cast _, apply zmod.coe_mul_inv_eq_one,
    swap 3, { refine zmod.char_p _, },
    any_goals { apply dvd_rfl, },
    sorry, sorry, },
  -- apply (zmod.nat_coe_zmod_eq_iff (d * p^(2 * k)) (c *
  --   ((c : zmod (d * p^(2 * k)))⁻¹.val : zmod (d * p^k)).val) 1).1 _,
  -- { rw nat.cast_mul, rw zmod.nat_cast_val, rw zmod.nat_cast_val,
  --   rw zmod.cast_inv _ _, },
end

lemma exists_V_h1_2 [normed_algebra ℚ R] [norm_one_class R] (k : ℕ) (x : (zmod (d * p^k))ˣ) :
  ∃ z : ℕ, (x : zmod (d * p^k)).val = (c * ((c : zmod (d * p^(2 * k))))⁻¹.val) *
  (x : zmod (d * p^k)).val - z * (d * p^k) * (x : zmod (d * p^k)).val :=
begin
  obtain ⟨z₁, hz₁⟩ := exists_V_h1_1 p d R c _ x,
  rw hz₁,
  refine ⟨z₁ * p^k, _⟩,
  rw add_mul, rw one_mul,
  have : p^(2 * k) = p^k * p^k,
  { rw pow_mul', rw pow_two, },
  rw this, rw ← mul_assoc d (p^k), rw mul_comm (d * p^k) (p^k), rw ← mul_assoc z₁ _ _,
  rw nat.add_sub_cancel,
end

lemma exists_V_h1_3 [normed_algebra ℚ R] [norm_one_class R] (n k : ℕ) (x : (zmod (d * p^k))ˣ) :
  ∃ z : ℕ, ((x : zmod (d * p^k)).val)^n = c^n * (((c : zmod (d * p^(2 * k))))⁻¹.val *
  (x : zmod (d * p^k)).val)^n - z * (d * p^(2 * k)) :=
begin
  rw mul_pow, rw ← mul_assoc, rw ← mul_pow,
  obtain ⟨z₁, hz₁⟩ := exists_V_h1_1 p d R c _ x,
  --obtain ⟨z₂, hz₂⟩ := exists_V_h1_2 p d R c _ x,
  rw hz₁,
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

lemma exists_V_h1_4 [normed_algebra ℚ R] [norm_one_class R] (n k : ℕ) (hk : k ≠ 0)
  (x : (zmod (d * p^k))ˣ) :
  c^n * (((c : zmod (d * p^(2 * k))))⁻¹.val * (x : zmod (d * p^k)).val)^n >
  (classical.some (exists_V_h1_3 p d R c n k x)) * (d * p^(2 * k)) :=
begin
  apply nat.lt_of_sub_eq_succ,
  rw ← classical.some_spec (exists_V_h1_3 p d R c _ _ x),
  swap, { apply ((x : zmod (d * p^k)).val^n).pred, },
  rw (nat.succ_pred_eq_of_pos _),
  apply pow_pos _, apply nat.pos_of_ne_zero,
  haveI : fact (1 < d * p^k), sorry,
  apply zmod.unit_ne_zero,
end

example (a b c d : ℕ) : ((a : ℤ) : ℚ) = (a : ℚ) := by simp only [int.cast_coe_nat]

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
end

lemma helper_1 (a b c d e f : R) : a + b + c + d - e - f = d - e + (c - f) + (a + b) := by ring

lemma helper_2 (a b c : R) (ε : ℝ) (hε : 0 < ε) (h1 : ∥a∥ < ε/3) (h2 : ∥b∥ < ε/3)
  (h3 : ∥c∥ < ε/3) : ∥a + b + c∥ < ε :=
begin
  have : ε/3 + ε/3 + ε/3 = ε, linarith,
  rw ← this,
  apply lt_of_le_of_lt (norm_add_le _ _) _,
  apply add_lt_add _ h3,
  apply lt_of_le_of_lt (norm_add_le _ _) _,
  apply add_lt_add h1 h2,
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

lemma helper_7 {k : ℕ} (a₁ a₂ : (zmod (d * p^k))ˣ)
  (h : (((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k))) : zmod (d * p^k)) *
  (a₁ : zmod (d * p^k)) = (((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k))) : zmod (d * p^k)) *
  (a₂ : zmod (d * p^k))) : a₁ = a₂ :=
begin
  rw units.ext_iff, rw zmod.cast_inv at h, rw zmod.cast_nat_cast _ at h,
  have := congr_arg2 has_mul.mul (eq.refl (c : zmod (d * p^k))) h,
  simp_rw ← mul_assoc at this,
  rw zmod.mul_inv_of_unit _ _ at this, simp_rw one_mul at this,
  exact this,
  sorry,
  swap, { refine zmod.char_p _, },
  sorry,
  sorry,
  sorry,
end

lemma helper_8 (a b c d : R) : a * b * (c * d) = a * c * (b * d) := by { ring, }

noncomputable def M5 [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (ε : ℝ) (hε : 0 < ε) : ℕ :=
Inf {z : ℕ | ∀ y ≥ z, ∥((p ^ y : ℕ) : R)∥ * (χ * teichmuller_character_mod_p_change_level p d R m ^ n).bound < ε}

lemma M5_spec [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (ε : ℝ) (hε : 0 < ε) (y : ℕ) (hy : M5 p d R m χ n ε hε ≤ y) :
  ∥((p ^ y : ℕ) : R)∥ * (χ * teichmuller_character_mod_p_change_level p d R m ^ n).bound < ε :=
begin
  apply nat_spec _ _ y hy,
  refine ⟨classical.some (norm_lim_eq_zero' 1 p hε (le_of_lt (dirichlet_character.bound_pos
    (χ * teichmuller_character_mod_p_change_level p d R m ^ n)))), λ x hx, _⟩,
  { exact R, },
  any_goals { apply_instance, },
  rw ← nat.one_mul (p^x),
  apply classical.some_spec (norm_lim_eq_zero' 1 p hε (le_of_lt (dirichlet_character.bound_pos
    (χ * teichmuller_character_mod_p_change_level p d R m ^ n)))) x hx,
end

--variable (na : ∀ (n : ℕ) (f : ℕ → R), ∥∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)

instance zmod.units_fintype (n : ℕ) : fintype (zmod n)ˣ :=
begin
  by_cases n = 0,
  { rw h, refine units_int.fintype, },
  { haveI : fact (0 < n),
    { apply fact_iff.2, apply nat.pos_of_ne_zero h, },
    apply_instance, },
end

lemma helper_10 (n : ℤ) : ∥((n : ℤ_[p]) : ℚ_[p])∥ ≤ 1 := sorry

lemma helper_9 (n : ℕ) (ε : ℝ) (k : ℕ) (hk : m ≤ k) [normed_algebra ℚ R] [norm_one_class R]
  (hn : 1 < n) (hε : 0 < ε) (h1 : (d : ℚ) * ↑p ^ k ≠ 0) (h2 : d * p ^ m ∣ d * p ^ k) (h3 : k ≠ 0)
  (h4 : n - 1 ≠ 0) (h' : d * p ^ k ∣ d * p ^ (2 * k))
  (hk' : k ≥ max m (M5 p d R m χ n (ε/6) (by linarith)))
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥) :
  ∥∑ (x : (zmod (d * p ^ k))ˣ), ↑((χ * teichmuller_character_mod_p_change_level p d R m ^ n)
  ((units.map (zmod.cast_hom (show d * p ^ m ∣ d * p ^ k, from mul_dvd_mul_left d (pow_dvd_pow p hk))
  (zmod (d * p ^ m))).to_monoid_hom) x)) * ((-↑(classical.some (exists_V_h1_3 p d R c (n - 1) k x)) +
  ↑(c ^ (n - 1)) * (algebra_map ℚ R) ↑(classical.some (exists_V_h1_5 p d R c (n - 1) k h4 x))) * (↑c * (algebra_map ℚ R)
  (int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k))) * ↑x / ↑(d * p ^ k))))) * ↑(d * p ^ (2 * k))∥ < ε / 3 :=
begin
  have : 0 < ε/3, linarith,
  simp_rw [nat.cast_mul d (p^k), nat.cast_pow, helper_4 p d R c k _],
  simp_rw [mul_assoc],
  conv { congr, congr, apply_congr, skip, conv { congr, skip, congr, skip,
    rw fract_eq_self (zero_le_and_lt_one p d k _).1 (zero_le_and_lt_one p d k _).2,
    rw ← map_nat_cast (algebra_map ℚ R) (d * p^(2 * k)), rw ← ring_hom.map_mul, rw two_mul,
    rw pow_add, rw ← mul_assoc d (p^k) _, rw nat.cast_mul _ (p^k), rw ← mul_assoc,
    rw nat.cast_mul d (p^k), rw nat.cast_pow, rw div_mul_cancel _ h1, rw ring_hom.map_mul,
    rw map_nat_cast, rw ← nat.cast_pow, rw map_nat_cast, }, },
  simp_rw [← mul_assoc], -- ← finset.sum_mul],
  --apply lt_of_le_of_lt (norm_mul_le _ _),
  apply lt_of_le_of_lt (na (d * p^k) _) _,
  have div_four_pos : 0 < ε/6, { linarith, },
  have div_four_lt_div_two : ε/6 < ε/3, { linarith, },
  apply lt_of_le_of_lt _ div_four_lt_div_two,
  apply cSup_le _ _,
  { apply set.range_nonempty _, apply_instance, },
  { intros b hb, cases hb with y hy, rw ← hy, simp only,
    apply le_trans (norm_mul_le _ _) _,
    simp_rw [mul_assoc],
    apply le_trans (mul_le_mul (norm_mul_le _ _) le_rfl (norm_nonneg _) _) _,
    { apply (mul_nonneg (norm_nonneg _) (norm_nonneg _)), },
    rw mul_assoc,
    rw ← asso_dirichlet_character_eq_char,
    apply le_trans (mul_le_mul (le_of_lt (dirichlet_character.lt_bound _ _)) le_rfl _ (le_of_lt (dirichlet_character.bound_pos _))) _,
    { apply (mul_nonneg (norm_nonneg _) (norm_nonneg _)), },
    rw mul_comm, rw mul_assoc, rw ring_hom.map_int_cast,
    simp_rw [← nat.cast_pow, ← nat.cast_mul, ← int.cast_coe_nat, ← int.cast_mul, ← int.cast_neg,
      ← int.cast_add, ← int.cast_mul],
      rw ← ring_hom.map_int_cast (algebra_map ℚ_[p] R),
      rw ← padic_int.coe_coe_int, rw norm_algebra_map, rw norm_one_class.norm_one, rw mul_one,
      apply le_trans (mul_le_mul (helper_10 _ _) le_rfl _ _) _,
      { apply (mul_nonneg (norm_nonneg _) (le_of_lt (dirichlet_character.bound_pos _))), },
      { apply zero_le_one, },
      { rw one_mul, apply le_of_lt, rw int.cast_coe_nat, apply M5_spec,
        apply (max_le_iff.1 hk').2, }, },
end

lemma V_h1 [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (ε : ℝ) (hε : 0 < ε) : ∃ z : ℕ, ∀ k ≥ z,
  ∥(V_def p d R m hd χ c n k) - ((((χ * ((teichmuller_character_mod_p_change_level p d R m)^n)) (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime_pow_spl p c m hc⟩))
   * (c : R)^n)) * U_def p d R m hd χ n k) - (V_h_def p d R m χ c n k)∥ < ε :=
begin
  have : ε/3 > 0, linarith,
  have div_six_pos : ε/6 > 0, linarith,
  refine ⟨max m (M5 p d R m χ n (ε / 6) div_six_pos), λ k hk, _⟩,
  delta V_def,
  have h1 : (d * p^k : ℚ) ≠ 0, sorry,
  have h2 : d * p^m ∣ d * p^k, sorry,
  have h3 : k ≠ 0, sorry,
  have h4 : n - 1 ≠ 0, sorry,
  have h' : d * p ^ k ∣ d * p ^ (2 * k), sorry,
  conv { congr, congr, congr, congr, apply_congr, skip, rw used_map_ext p d R m hd χ n k (le_of_lt hn) (max_le_iff.1 hk).1,
    conv { congr, congr, skip, --rw rev_coe, rw classical.some_spec (exists_V_h1_3 p d R c _ _ x),
      rw ← nat.cast_pow, rw classical.some_spec (exists_V_h1_3 p d R c _ _ x),
      rw nat.cast_sub (le_of_lt (exists_V_h1_4 p d R c _ _ h3 x)),
      rw sub_eq_neg_add _ _,
      rw nat.cast_mul (c^(n - 1)) _, rw ← map_nat_cast (algebra_map ℚ R) (((c : zmod (d * p^(2 * k)))⁻¹.val *
        (x : zmod (d * p^k)).val) ^ (n - 1)),
      rw nat.cast_pow ((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val) _,
      rw classical.some_spec (exists_V_h1_5 p d R c _ _ h4 x), }, },
  simp_rw [smul_eq_mul, mul_assoc,
    ring_hom.map_add, mul_add, ← add_assoc, add_mul, mul_add, finset.sum_add_distrib,
    mul_assoc ((c^(n - 1) : ℕ) : R), ← ring_hom.map_mul],
  simp_rw [helper_1 R],
  apply helper_2 R _ _ _ ε hε _ _ _,
  { rw U_def,
    conv { congr, congr, congr, skip, congr, skip, congr, skip, apply_congr, skip, rw used_map_ext p d R m hd χ n k (le_of_lt hn) (max_le_iff.1 hk).1, },
    convert this,
    rw norm_eq_zero,
    rw sub_eq_zero,
    simp_rw [helper_3 p d R, helper_4 p d R, finset.mul_sum, ← mul_assoc, smul_eq_mul, ← mul_assoc],
    apply finset.sum_bij,
    { intros a ha, apply finset.mem_univ _, },
    swap 4, { intros a ha, apply is_unit.unit,
      swap, { exact (c : zmod (d * p^(2 * k)))⁻¹.val * (a : zmod (d * p^k)).val, },
      sorry, },
    { intros a ha, conv_rhs { rw helper_5 R _ (c^n : R) _, rw mul_assoc, rw mul_assoc, },
      rw mul_assoc, apply congr_arg2,
      { simp_rw ← units.coe_hom_apply,
        rw ← monoid_hom.map_mul (units.coe_hom R), rw ← monoid_hom.map_mul, congr,
        rw units.ext_iff, simp only [units.coe_hom_apply, zmod.nat_cast_val, zmod.cast_id', id.def,
          ring_hom.to_monoid_hom_eq_coe, units.coe_map,
          ring_hom.coe_monoid_hom, zmod.cast_hom_apply, units.coe_mul, zmod.coe_unit_of_coprime],
        rw is_unit.unit_spec, rw zmod.cast_mul h2, rw zmod.cast_inv _ _ _ _ h',
        rw zmod.cast_nat_cast h' _, rw zmod.cast_inv _ _ _ _ h2, rw zmod.cast_nat_cast h2 _,
        rw ← mul_assoc, rw zmod.mul_inv_of_unit _, rw one_mul,
        sorry,
        any_goals { refine zmod.char_p _, },
        any_goals { apply nat.coprime.mul_right hc' (nat.coprime_pow_spl p c _ hc), }, },
      { rw ring_hom.map_mul, rw fract_eq_self _, rw mul_div_cancel' _,
        rw ← mul_assoc, rw ring_hom.map_mul, rw ← mul_assoc, rw map_nat_cast,
        rw helper_5 R _ _ (c : R), rw mul_assoc, apply congr_arg2,
        { rw nat.cast_pow, rw ← pow_succ', rw nat.sub_add_cancel _, sorry, }, --might need change
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
      apply helper_7 p d c _ _ h, },
    { intros b hb, simp_rw [units.ext_iff, is_unit.unit_spec],
      refine ⟨is_unit.unit _, _, _⟩,
      { exact c * (b : zmod (d * p^k)), },
      { apply is_unit.mul _ (units.is_unit _), sorry, },
      { apply finset.mem_univ _, },
      { rw is_unit.unit_spec, simp_rw zmod.nat_cast_val, rw zmod.cast_id, rw ← mul_assoc,
        rw zmod.cast_inv _ _ _ _ h', rw zmod.cast_nat_cast h' _, rw zmod.inv_mul_of_unit _, rw one_mul,
        { sorry, },
        { refine zmod.char_p _, },
        { apply nat.coprime.mul_right hc' (nat.coprime_pow_spl p c (2 * k) hc), }, }, }, },
  { convert this, rw norm_eq_zero,
    rw sub_eq_zero, delta V_h_def, rw dif_pos, },
    -- { rw nat.cast_mul, apply finset.sum_congr rfl _,
    --   intros x hx, convert refl _,
    --   apply congr_arg, apply_instance, apply congr_arg2 _ rfl _, },
    -- apply hk,
    -- simp_rw [units.coe_hom_apply],
    -- apply finset.sum_congr rfl (λ x hx, _),
    -- simp_rw mul_assoc, apply congr_arg2 _ rfl _,
    --apply (max_le_iff.1 hk).1, },
  { simp_rw [← finset.sum_add_distrib, ← mul_add, ring_hom.map_mul, ← mul_assoc, ← add_mul,
      mul_assoc _ (algebra_map ℚ R (d : ℚ)) _, ← ring_hom.map_mul _ (d : ℚ) _, ← nat.cast_pow,
      ← nat.cast_mul d _, map_nat_cast, mul_assoc _ d _, nat.cast_mul _ (d * p^(2 * k)),
      mul_comm _ ((d * p^(2 * k) : ℕ) : R), neg_mul_eq_mul_neg, ← mul_add, mul_assoc _ (c : R) _,
      mul_assoc, mul_comm ((d * p^(2 * k) : ℕ) : R), ← mul_assoc _ _ ((d * p^(2 * k) : ℕ) : R)],
    convert helper_9 p d R m χ c n ε k (max_le_iff.1 hk).1 hn hε h1 h2 h3 h4 h' hk na,
    ext, congr, apply congr_arg, congr, ext, simp_rw [nat.cast_mul, nat.cast_pow, mul_assoc],
    simp only [nat.cast_mul], },
--  { refl, }, -- get a det timeout if i remove this
end

--variables (hc : c.gcd p = 1) (hc' : c.gcd d = 1)

noncomputable def M1 [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (ε : ℝ) (hε : 0 < ε) : ℕ :=
Inf {z : ℕ | ∀ k ≥ z, ∥(V_def p d R m hd χ c n k) - ((((χ * ((teichmuller_character_mod_p_change_level p d R m)^n)) (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime_pow_spl p c m hc⟩))
   * (c : R)^n)) * U_def p d R m hd χ n k) - (V_h_def p d R m χ c n k)∥ < ε}

lemma M1_spec [normed_algebra ℚ R] [norm_one_class R] --(hc : c.gcd p = 1) (hc' : c.gcd d = 1)
  (n : ℕ) (hn : 1 < n)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : M1 p d R m hd χ c hc hc' n ε hε ≤ k) :
  ∥(V_def p d R m hd χ c n k) - ((((χ * ((teichmuller_character_mod_p_change_level p d R m)^n)) (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime_pow_spl p c m hc⟩))
   * (c : R)^n)) * U_def p d R m hd χ n k) - (V_h_def p d R m χ c n k)∥ < ε :=
begin
  delta M1 at hk,
  apply nat_spec' _ _ k hk,
  refine ⟨classical.some (V_h1 p d R m hd χ c hc hc' n hn na ε hε),
    classical.some_spec (V_h1 p d R m hd χ c _ _ n hn na ε hε)⟩,
end
.

lemma helper_13 (a b c d e f : R) : a + b + c + (d - e - f) = a + b + (c - f) + (d - e) := by ring

lemma nat.le_two_mul_of_half_le (k n : ℕ) (hn : k/2 ≤ n) : k ≤ 2 * n := by { sorry }

lemma V_h2_1 (hd : d.gcd p = 1) [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : max m ((M5 p d R m χ n (ε / 6) (by linarith))/2) ≤ k) :
  ∥(algebra_map ℚ R) ((n - 1 : ℕ) * (d * p^k) : ℚ) * (U_def p d R m hd χ n k) -
  (∑ (x : (zmod (d * p ^ k))ˣ), ↑((χ * teichmuller_character_mod_p_change_level p d R m ^ n)
  ((units.map (zmod.cast_hom (show d * p ^ m ∣ d * p ^ k, from mul_dvd_mul_left d (pow_dvd_pow p (max_le_iff.1 hk).1))
  (zmod (d * p ^ m))).to_monoid_hom) x)) * (((n - 1 : ℕ) : R) * ((c^n : ℕ) : R) * ((algebra_map ℚ R)
  ((d * p^k : ℚ) * int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k))) * ↑x / ↑(d * p ^ k)))^n))) -
  (n * (d * p^k)) * (V_h_def p d R m χ c n k)∥ < ε :=
begin
  delta U_def,
  have div_four_pos : 0 < ε/6, { linarith, },
--  refine ⟨(M5 p d R m χ n (ε / 6) div_four_pos)/2, λ k hk, _⟩,
  have h1 : (d * p^k : ℚ) ≠ 0, sorry,
  have h2 : ∀ (x : (zmod (d * p^k))ˣ), (x : ℚ) = ((x : zmod (d * p^k)).val : ℚ), sorry,
  have h3 : k ≠ 0, sorry,
  have h4 : n ≠ 0, sorry,
  have h5 : ε = ε/3 + ε/3 + ε/3, linarith,
  have h6 : 0 < ε/3, linarith,
  conv { congr, congr, congr, congr, rw finset.mul_sum, apply_congr, skip,
    rw mul_smul_comm,
    rw h2,
    rw fract_eq_self (zero_le_and_lt_one p d k x).1 (zero_le_and_lt_one p d k x).2,
    rw ← ring_hom.map_mul, rw mul_assoc, rw mul_div_cancel' _ h1,
    rw ← nat.cast_mul (n - 1) _, rw map_nat_cast,
    rw used_map_ext p d R m hd χ n k (le_of_lt hn) (max_le_iff.1 hk).1 _, --skip,
    rw smul_eq_mul, rw mul_assoc, rw ← nat.cast_pow, rw ← nat.cast_mul, rw ← mul_assoc,
    rw mul_comm _ (n - 1), rw mul_assoc, rw ← pow_succ',
    rw nat.sub_add_cancel (le_of_lt hn),
    conv { congr, congr, skip, --rw rev_coe, rw classical.some_spec (exists_V_h1_3 p d R c _ _ x),
      --rw ← nat.cast_pow,
      rw classical.some_spec (exists_V_h1_3 p d R c _ _ x),
      rw nat.cast_mul,
      rw nat.cast_sub (le_of_lt (exists_V_h1_4 p d R c _ _ h3 x)),
      rw sub_eq_neg_add _ _,
      rw nat.cast_mul (c^n) _, rw ← map_nat_cast (algebra_map ℚ R) (((c : zmod (d * p^(2 * k)))⁻¹.val *
        (x : zmod (d * p^k)).val) ^ n),
      rw nat.cast_pow ((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val) _,
      rw classical.some_spec (exists_V_h1_5 p d R c _ _ h4 x), }, skip,
      rw ← zmod.nat_cast_val, apply_congr, skip, rw h2, rw nat.cast_mul, rw nat.cast_pow p,
      rw ← nat.cast_mul _ (x : zmod (d * p^k)).val, rw ← ring_hom.map_pow, },
      simp_rw [ring_hom.map_add, mul_add, finset.sum_add_distrib, ← add_assoc, ← add_sub, helper_13],
      conv { congr, skip, rw h5, },
      apply lt_of_le_of_lt (norm_add_le _ _) _,
      apply add_lt_add,
      { apply lt_of_le_of_lt (norm_add_le _ _) _,
        apply add_lt_add,
        { simp_rw [← finset.sum_add_distrib, ← mul_add], --nat.cast_mul, nat.cast_pow, ],
          convert lt_of_le_of_lt (na (d * p^k) _) _,
          have div_four_lt_div_two : ε/6 < ε/3, { linarith, },
          apply lt_of_le_of_lt _ div_four_lt_div_two,
          apply cSup_le _ _,
          { apply set.range_nonempty _, apply_instance, },
          { intros b hb, cases hb with y hy, rw ← hy, simp only,
            apply le_trans (norm_mul_le _ _) _,
            simp_rw [mul_assoc],

            conv { congr, congr, skip, congr, congr, skip, conv { rw ← mul_assoc, rw ← mul_assoc, --congr, skip, --rw mul_assoc _ d _,
              rw nat.cast_mul, rw ← neg_mul, --rw mul_assoc _ (d : ℚ) _,
              rw ring_hom.map_mul, --rw ring_hom.map_mul,
            --rw map_nat_cast,
            conv { congr, skip, congr, skip, congr, skip, rw ← nat.cast_pow, rw map_nat_cast, },
            rw ← mul_assoc, rw ← add_mul, }, },
            simp_rw [← mul_assoc], --rw ← finset.sum_mul,
            apply le_trans (mul_le_mul le_rfl (norm_mul_le _ _) _ (norm_nonneg _)) _,
            { apply norm_nonneg _, },
            rw ← asso_dirichlet_character_eq_char,
            apply le_trans (mul_le_mul (le_of_lt (dirichlet_character.lt_bound _ _)) le_rfl _
              (le_of_lt (dirichlet_character.bound_pos _))) _,
            { apply (mul_nonneg (norm_nonneg _) (norm_nonneg _)), },
            rw mul_comm, rw mul_assoc, rw ring_hom.map_mul, rw ring_hom.map_int_cast,
            rw map_nat_cast,
            simp_rw [← nat.cast_pow, ← nat.cast_mul, ← int.cast_coe_nat, ← int.cast_mul, ← int.cast_neg,
              ← int.cast_add, ← int.cast_mul],
            rw ← ring_hom.map_int_cast (algebra_map ℚ_[p] R),
            rw ← padic_int.coe_coe_int, rw norm_algebra_map, rw norm_one_class.norm_one, rw mul_one,
            apply le_trans (mul_le_mul (helper_10 _ _) le_rfl _ _) _,
            { apply (mul_nonneg (norm_nonneg _) (le_of_lt (dirichlet_character.bound_pos _))), },
            { apply zero_le_one, },
            { rw one_mul, apply le_of_lt, rw int.cast_coe_nat, apply M5_spec,
              apply nat.le_two_mul_of_half_le _ _ (max_le_iff.1 hk).2, }, }, },
--            ring_hom.map_mul _ _ _, ← mul_assoc (c^n : R) _ _, map_nat_cast], sorry, },
        { delta V_h_def, rw dif_pos (max_le_iff.1 hk).1,
          convert h6,
          rw norm_eq_zero,
          -- convert ← @norm_zero R _,
          -- apply congr_arg,
          rw sub_eq_zero, rw finset.mul_sum, apply finset.sum_congr rfl (λ x hx, _),
          rw mul_comm ((n : R) * _) _,
          rw mul_assoc _ _ ((n : R) * _), apply congr_arg2 _ rfl _,
          rw ← nat.pred_eq_sub_one,
          rw ← nat.succ_pred_eq_of_pos (nat.lt_pred_iff.2 hn),
          rw pow_succ _ (n.pred.pred),
          have : 0 < n, sorry,
          rw ← nat.succ_pred_eq_of_pos this,
          rw pow_succ' c n.pred,
          rw nat.cast_mul _ c,
          rw nat.succ_pred_eq_of_pos this,
          rw nat.succ_pred_eq_of_pos (nat.lt_pred_iff.2 hn),
          simp_rw [← mul_assoc (d : ℚ) _ _, ← nat.cast_pow p _, ← nat.cast_mul d _,
            mul_pow, ring_hom.map_mul, map_nat_cast, nat.pred_eq_sub_one],
          rw ← mul_assoc, rw ← mul_assoc _ _ (c : R), rw mul_comm ((n - 1 : ℕ) : R) _,
          rw mul_assoc, rw mul_assoc, rw mul_assoc _ _ (n * (d * p^k : ℕ) : R),
          apply congr_arg2 _ rfl _, simp_rw [mul_assoc], apply congr_arg2 _ rfl _,
          ring, repeat { apply congr_arg2 _ _ rfl },
          conv_rhs { rw mul_assoc, rw mul_comm, },
          simp_rw [← h2, ← zmod.nat_cast_val],
          conv_rhs { congr, skip, rw h2, rw ← nat.cast_mul, }, }, },
      { convert h6, rw norm_eq_zero,
        -- rw ← @norm_zero R _, apply congr_arg,
        rw sub_eq_zero,
        apply finset.sum_congr _ (λ x hx, _),
        { convert refl _, apply_instance, },
        { apply congr_arg2 _ rfl _, rw mul_assoc ((n - 1 : ℕ) : R) _ _, }, }, -- why does rw not solve this?
      --convert_to ∥_ + _ + _ + ((0 : R) - _)∥ < ε,
end
.

-- example (a b c : ℚ) : a - (b - c) = a + c - b := by library_search

lemma helper_11 (ε : ℝ) (hε : 0 < ε) : 0 < ε /2 / 6 :=
begin
  apply div_pos (half_pos hε) _,
  linarith,
end

lemma V_h2_2 [normed_algebra ℚ R] [norm_one_class R] (hc' : c.coprime d) (hc : c.coprime p) (n : ℕ) (hn : 1 < n)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : max m (M5 p d R m χ n (ε / 2 / 6) (helper_11 ε hε) / 2) ≤ k) :
  ∥(n * (d * p^k) : R) * (V_h_def p d R m χ c n k) -
  ((n - 1 : ℕ) * (d * p^k) : R) * (1 - (asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c *
  (algebra_map ℚ R) (c ^ n : ℚ)) * (U_def p d R m hd χ n k)∥ < ε :=
begin
  have div_two_div_six_pos : 0 < ε / 2 / 6, sorry,
  --refine ⟨max m (M5 p d R m χ n (ε / 2 / 6) div_two_div_six_pos / 2), λ k hk, _⟩,
  have h1 : (d * p^k : ℚ) ≠ 0, sorry,
  have h2 : d * p^m ∣ d * p^k, sorry,
  have h3 : k ≠ 0, sorry,
  have h4 : n - 1 ≠ 0, sorry,
  have h5 : ∀ (x : (zmod (d * p^k))ˣ), (x : ℚ) = ((x : zmod (d * p^k)) : ℚ), sorry,
  have h' : d * p ^ k ∣ d * p ^ (2 * k), sorry,
  rw norm_sub_rev,
  rw ← sub_add_sub_cancel,
  swap, { refine (algebra_map ℚ R) ((n - 1 : ℕ) * (d * p^k) : ℚ) * (U_def p d R m hd χ n k) -
    (∑ (x : (zmod (d * p ^ k))ˣ), ↑((χ * teichmuller_character_mod_p_change_level p d R m ^ n)
    ((units.map (zmod.cast_hom (show d * p ^ m ∣ d * p ^ k, from mul_dvd_mul_left d (pow_dvd_pow p (max_le_iff.1 hk).1))
    (zmod (d * p ^ m))).to_monoid_hom) x)) * (((n - 1 : ℕ) : R) * ((c^n : ℕ) : R) * ((algebra_map ℚ R)
    ((d * p^k : ℚ) * int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k))) * ↑x / ↑(d * p ^ k)))^n))), },
  conv { congr, skip, rw ← half_add_self ε, },
  rw add_div,
  apply lt_of_le_of_lt (norm_add_le _ _) _,
  apply add_lt_add _ (V_h2_1 p d R m χ c hd n hn na _ (half_pos hε) _ _),
  rw [mul_sub, mul_one, sub_mul, sub_sub, add_comm, ← sub_sub, ← sub_add, add_sub_assoc,
    ring_hom.map_mul, ← nat.cast_pow p _, ← nat.cast_mul d _, ← nat.cast_pow p _,
    ← nat.cast_mul d _, map_nat_cast, map_nat_cast, sub_self, zero_add],
  convert half_pos hε, rw norm_eq_zero, rw sub_eq_zero, delta U_def,
  conv_rhs { congr, skip, apply_congr, skip, rw used_map_ext p d R m hd χ n k (le_of_lt hn) (max_le_iff.1 hk).1 _, },
  rw finset.mul_sum,
  apply finset.sum_bij,
  { intros a ha, apply finset.mem_univ _, },
  swap 4, { intros a ha, apply is_unit.unit,
   swap, { exact (c : zmod (d * p^(2 * k)))⁻¹.val * (a : zmod (d * p^k)).val, },
   sorry, },
  { intros a ha,
    --rw ← asso_dirichlet_character_eq_char, rw ← asso_dirichlet_character_eq_char,
    rw smul_eq_mul, rw mul_comm _ ((algebra_map ℚ R) (c^n : ℚ)),
    rw ← mul_assoc ((n - 1 : ℕ) * (d * p^k : ℕ) : R) _ _,
    rw mul_assoc (((n - 1 : ℕ) * (d * p^k : ℕ) : R) * (algebra_map ℚ R) (c^n : ℚ)) _ _,
    conv_rhs { congr, skip, conv { congr, skip, rw mul_assoc, }, rw ← mul_assoc, },
    conv_rhs { rw ← mul_assoc, rw helper_5, rw mul_comm, rw ← asso_dirichlet_character_eq_char, },
    apply congr_arg2,
    { rw ← asso_dirichlet_character_eq_char,
      -- rw ← dirichlet_character.asso_dirichlet_character_mul,
      --simp_rw ← units.coe_hom_apply,
      rw ← monoid_hom.map_mul (asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m ^ n))) _ _,
      --rw ← monoid_hom.map_mul (units.coe_hom R), rw ← monoid_hom.map_mul,
      congr,
      --rw units.ext_iff,
      simp only [units.coe_hom_apply, zmod.nat_cast_val, zmod.cast_id', id.def,
        ring_hom.to_monoid_hom_eq_coe, units.coe_map,
        ring_hom.coe_monoid_hom, zmod.cast_hom_apply, units.coe_mul, zmod.coe_unit_of_coprime],
      rw is_unit.unit_spec, rw zmod.cast_mul h2, rw zmod.cast_inv _ _ _ _ h',
      rw zmod.cast_nat_cast h' _, rw zmod.cast_inv _ _ _ _ h2, rw zmod.cast_nat_cast h2 _,
      rw ← mul_assoc, rw zmod.mul_inv_of_unit _, rw one_mul,
      sorry,
      any_goals { refine zmod.char_p _, },
      -- { apply nat.coprime.mul_right hc' (nat.coprime_pow_spl p c _ hc), },
      any_goals { apply nat.coprime.mul_right hc' (nat.coprime_pow_spl p c _ hc), }, },
    { --rw ring_hom.map_mul,
      rw nat.cast_mul d _, rw nat.cast_pow p _,
      rw helper_4 p d R c k a, rw fract_eq_self _, rw mul_div_cancel' _,
      simp_rw [mul_assoc], apply congr_arg2 _ rfl _, rw ← nat.cast_pow c, rw map_nat_cast,
      rw map_nat_cast,
      rw ← mul_assoc, rw mul_comm _ ((c^n : ℕ) : R), rw mul_assoc, apply congr_arg2 _ rfl _,
      -- rw ring_hom.map_mul, -- rw ← mul_assoc,
      -- rw map_nat_cast,
      conv_rhs { rw h5, }, rw ← nat.cast_pow p _, rw ← nat.cast_mul d _, rw fract_eq_val,
      rw mul_comm (↑(d * p^k)) _, rw mul_assoc, rw ← map_nat_cast (algebra_map ℚ R) (d * p^k),
      rw ← ring_hom.map_mul, rw div_mul_cancel _, rw map_nat_cast, rw ← pow_succ',
      rw nat.sub_one, rw nat.add_one, rw nat.succ_pred_eq_of_pos _,
      rw ← map_nat_cast (algebra_map ℚ R) _, congr, rw ← map_nat_cast (algebra_map ℚ R) _,
      apply congr_arg,
      rw is_unit.unit_spec,
      { apply lt_trans _ hn, apply nat.zero_lt_one, },
--      rw helper_5 R _ _ (c : R), rw mul_assoc, apply congr_arg2,
      { rw nat.cast_mul, rw nat.cast_pow, apply h1, }, --might need change
      { apply h1, },
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
    apply helper_7 p d c _ _ h, },
  { intros b hb, simp_rw [units.ext_iff, is_unit.unit_spec],
    refine ⟨is_unit.unit _, _, _⟩,
    { exact c * (b : zmod (d * p^k)), },
    { apply is_unit.mul _ (units.is_unit _), sorry, },
    { apply finset.mem_univ _, },
    { rw is_unit.unit_spec, simp_rw zmod.nat_cast_val, rw zmod.cast_id, rw ← mul_assoc,
      rw zmod.cast_inv _ _ _ _ h', rw zmod.cast_nat_cast h' _, rw zmod.inv_mul_of_unit _, rw one_mul,
      { sorry, },
      { refine zmod.char_p _, },
      { apply nat.coprime.mul_right hc' (nat.coprime_pow_spl p c (2 * k) hc), }, }, },
--  simp_rw [← sub_add, sub_add_eq_add_sub], delta U_def, simp_rw [used_map_ext],
end

--variable (hd : d.gcd p = 1)

lemma V_h2_3 (hd : d.gcd p = 1) [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : max m ((M5 p d R m χ n (ε / 6) (by linarith))) ≤ k) :
  ∥(algebra_map ℚ R) ((n - 1 : ℕ) : ℚ) * (U_def p d R m hd χ n k) -
  (∑ (x : (zmod (d * p ^ k))ˣ), ↑((χ * teichmuller_character_mod_p_change_level p d R m ^ n)
  ((units.map (zmod.cast_hom (show d * p ^ m ∣ d * p ^ k, from mul_dvd_mul_left d (pow_dvd_pow p (max_le_iff.1 hk).1))
  (zmod (d * p ^ m))).to_monoid_hom) x)) * (((n - 1 : ℕ) : R) * ((c^n : ℕ) : R) * ((algebra_map ℚ R)
  ((d * p^k : ℚ) * int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k))) * ↑x / ↑(d * p ^ k)))^n) * (algebra_map ℚ R) (1 / (d * p^k)))) -
  n * (V_h_def p d R m χ c n k)∥ < ε :=
begin
  delta U_def,
  have div_four_pos : 0 < ε/6, { linarith, },
--  refine ⟨(M5 p d R m χ n (ε / 6) div_four_pos)/2, λ k hk, _⟩,
  have h1 : (d * p^k : ℚ) ≠ 0, sorry,
  have h2 : ∀ (x : (zmod (d * p^k))ˣ), (x : ℚ) = ((x : zmod (d * p^k)).val : ℚ), sorry,
  have h3 : k ≠ 0, sorry,
  have h4 : n ≠ 0, sorry,
  have h5 : ε = ε/3 + ε/3 + ε/3, linarith,
  have h6 : 0 < ε/3, linarith,
  have h7 : (d * p^(2 * k) : ℚ) / (d * p^k) = (p^k : ℚ), sorry,
  conv { congr, congr, congr, congr, rw finset.mul_sum, apply_congr, skip,
    rw smul_eq_mul, -- rw mul_smul_comm,
    rw h2,
    rw fract_eq_self (zero_le_and_lt_one p d k x).1 (zero_le_and_lt_one p d k x).2,
    -- rw ← ring_hom.map_mul, -- rw mul_assoc, rw mul_div_cancel' _ h1,
    -- rw ← nat.cast_mul (n - 1) _, rw map_nat_cast,
    rw used_map_ext p d R m hd χ n k (le_of_lt hn) (max_le_iff.1 hk).1 _, --skip,
    -- rw smul_eq_mul,
    rw mul_assoc, rw ← map_nat_cast (algebra_map ℚ R) _,
    rw ← ring_hom.map_pow, rw ← ring_hom.map_mul, rw mul_div _ _ (d * p^k : ℚ), rw ← pow_succ', -- rw ← nat.cast_pow, rw ← nat.cast_mul,
    rw ← mul_assoc,
    -- rw mul_comm _ (n - 1), rw mul_assoc, rw ← pow_succ',
    rw nat.sub_add_cancel (le_of_lt hn),
    conv { congr, congr, skip, skip, --rw rev_coe, rw classical.some_spec (exists_V_h1_3 p d R c _ _ x),
      rw ← nat.cast_pow,
      rw classical.some_spec (exists_V_h1_3 p d R c _ _ x),
      -- rw nat.cast_mul,
      rw nat.cast_sub (le_of_lt (exists_V_h1_4 p d R c _ _ h3 x)),
      rw sub_eq_neg_add _ _,
      rw nat.cast_mul (c^n) _,
      -- rw ← map_nat_cast (algebra_map ℚ R) (((c : zmod (d * p^(2 * k)))⁻¹.val *
      --   (x : zmod (d * p^k)).val) ^ n),
      rw nat.cast_pow ((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val) _,
      rw classical.some_spec (exists_V_h1_5 p d R c _ _ h4 x), }, skip,
      rw ← zmod.nat_cast_val, apply_congr, skip, rw h2, rw nat.cast_mul, rw nat.cast_pow p,
      rw ← nat.cast_mul _ (x : zmod (d * p^k)).val, rw ← ring_hom.map_pow, },
      simp_rw [add_div, ring_hom.map_add, mul_add, add_div, ring_hom.map_add, mul_add,
        finset.sum_add_distrib, ← add_assoc, ← add_sub, helper_13],
      conv { congr, skip, rw h5, },
      apply lt_of_le_of_lt (norm_add_le _ _) _,
      apply add_lt_add,
      { apply lt_of_le_of_lt (norm_add_le _ _) _,
        apply add_lt_add,
        { simp_rw [← finset.sum_add_distrib, ← mul_add], --nat.cast_mul, nat.cast_pow, ],
          convert lt_of_le_of_lt (na (d * p^k) _) _,
          have div_four_lt_div_two : ε/6 < ε/3, { linarith, },
          apply lt_of_le_of_lt _ div_four_lt_div_two,
          apply cSup_le _ _,
          { apply set.range_nonempty _, apply_instance, },
          { intros b hb, cases hb with y hy, rw ← hy, simp only,
            apply le_trans (norm_mul_le _ _) _,
            simp_rw [mul_assoc],

            conv { congr, congr, skip, congr, congr, skip, conv { rw ← mul_assoc, rw ← mul_assoc, --congr, skip, --rw mul_assoc _ d _,
              rw mul_assoc, rw ← mul_div, rw h7, rw ring_hom.map_mul, congr, skip, rw ← nat.cast_pow p k,
              rw map_nat_cast, }, },
            conv { congr, congr, congr, skip, congr, congr, rw nat.cast_mul, rw nat.cast_mul,
              rw nat.cast_pow, rw ← neg_mul, rw ← mul_div, rw h7, rw ring_hom.map_mul, rw ← nat.cast_pow, rw map_nat_cast, },
            --   rw nat.cast_mul, rw ← neg_mul, --rw mul_assoc _ (d : ℚ) _,
            --   rw ring_hom.map_mul, --rw ring_hom.map_mul,
            -- --rw map_nat_cast,
            -- conv { congr, skip, congr, skip, congr, skip, rw ← nat.cast_pow, rw map_nat_cast, },
            -- rw ← mul_assoc, rw ← add_mul, }, },
            simp_rw [← mul_assoc], --rw ← finset.sum_mul,
            apply le_trans (mul_le_mul (norm_mul_le _ _) le_rfl (norm_nonneg _) _) _,
            { apply mul_nonneg (norm_nonneg _) (norm_nonneg _), },
            rw ← asso_dirichlet_character_eq_char,
            rw mul_comm (∥(algebra_map ℚ R) ↑(n - 1)∥) _, rw mul_assoc,
            apply le_trans (mul_le_mul (le_of_lt (dirichlet_character.lt_bound _ _)) le_rfl _
              (le_of_lt (dirichlet_character.bound_pos _))) _,
            { apply (mul_nonneg (norm_nonneg _) (norm_nonneg _)), },
            rw mul_comm, rw mul_assoc, rw ring_hom.map_mul, rw ring_hom.map_int_cast,
            rw map_nat_cast, simp_rw [← add_mul],
            rw ← ring_hom.map_int_cast (algebra_map ℚ R), rw ← ring_hom.map_mul, rw ← ring_hom.map_add,
            --rw ← ring_hom.map_int_cast (algebra_map ℚ_[p] R), --rw ← ring_hom.map_mul, rw ← ring_hom.map_add,
            simp_rw [← int.cast_coe_nat, ← int.cast_mul, ← int.cast_neg, ← int.cast_add, ring_hom.map_int_cast],
            rw ← ring_hom.map_int_cast (algebra_map ℚ_[p] R),
            rw ← padic_int.coe_coe_int, rw norm_algebra_map, rw norm_one_class.norm_one, rw mul_one,
            apply le_trans (mul_le_mul (helper_10 _ _) le_rfl _ _) _,
            { apply (mul_nonneg (norm_nonneg _) (le_of_lt (dirichlet_character.bound_pos _))), },
            { apply zero_le_one, },
            { rw one_mul, -- apply le_of_lt,
              rw int.cast_coe_nat (p^k),
              apply le_trans (mul_le_mul (norm_mul_le _ _) le_rfl
                (le_of_lt (dirichlet_character.bound_pos _)) _) _,
              { apply mul_nonneg (norm_nonneg _) (norm_nonneg _), },
              rw ← ring_hom.map_int_cast (algebra_map ℚ_[p] R),
              rw ← padic_int.coe_coe_int, rw norm_algebra_map, rw norm_one_class.norm_one, rw mul_one,
              rw mul_assoc,
              apply le_trans (mul_le_mul (helper_10 _ _) le_rfl _ (zero_le_one)) _,
              { apply mul_nonneg (norm_nonneg _) (le_of_lt (dirichlet_character.bound_pos _)), },
              rw one_mul, apply le_of_lt,
              -- rw mul_comm _ ↑(p^k),
              apply M5_spec, apply (max_le_iff.1 hk).2, }, }, },
--            ring_hom.map_mul _ _ _, ← mul_assoc (c^n : R) _ _, map_nat_cast], sorry, },
        { delta V_h_def, rw dif_pos (max_le_iff.1 hk).1,
          convert h6,
          rw norm_eq_zero,
          -- convert ← @norm_zero R _,
          -- apply congr_arg,
          rw sub_eq_zero, rw finset.mul_sum, apply finset.sum_congr rfl (λ x hx, _),
          rw mul_comm (n : R) _,
          rw mul_assoc _ _ (n : R), rw mul_comm ((algebra_map ℚ R) ↑(n - 1)) _, rw mul_assoc,
          apply congr_arg2 _ rfl _,
          rw ← nat.pred_eq_sub_one,
          rw ← nat.succ_pred_eq_of_pos (nat.lt_pred_iff.2 hn),
          rw pow_succ _ (n.pred.pred),
          have : 0 < n, sorry,
          rw ← nat.succ_pred_eq_of_pos this,
          rw pow_succ' c n.pred,
          rw nat.cast_mul _ c,
          rw nat.succ_pred_eq_of_pos this,
          rw nat.succ_pred_eq_of_pos (nat.lt_pred_iff.2 hn),
          simp_rw [← mul_assoc (d : ℚ) _ _, ← nat.cast_pow p _, ← nat.cast_mul d _,
            mul_pow, ring_hom.map_mul, map_nat_cast, nat.pred_eq_sub_one],
          rw ← mul_assoc, rw ← mul_assoc ((c^(n - 1) : ℕ) : R) (((n - 1 : ℕ) : R) * _) _,
          rw ← mul_assoc ((c^(n - 1) : ℕ) : R) ((n - 1 : ℕ) : R) _,
          rw mul_comm _ ((n - 1 : ℕ) : R), rw mul_assoc ((n - 1 : ℕ) : R) _ _,
          rw mul_assoc ((n - 1 : ℕ) : R) _ _, rw mul_assoc ((n - 1 : ℕ) : R) _ _,
          apply congr_arg2 _ rfl _, rw ← mul_div,
          simp_rw [ring_hom.map_mul, map_nat_cast, mul_assoc], apply congr_arg2 _ rfl _,
          rw ← mul_div, rw mul_div_left_comm, rw div_self, rw mul_one,
          ring, simp_rw [nat.cast_mul _ (x : zmod (d * p^k)).val, ← h2, zmod.nat_cast_val],
          repeat { apply congr_arg2 _ _ rfl, },
          simp_rw [ring_hom.map_mul], rw mul_assoc, apply congr_arg2 _ rfl _, rw mul_comm,
          { rw nat.cast_mul, rw nat.cast_pow, apply h1, }, }, },
      { convert h6, rw norm_eq_zero,
        -- rw ← @norm_zero R _, apply congr_arg,
        rw sub_eq_zero,
        apply finset.sum_congr _ (λ x hx, _),
        { convert refl _, apply_instance, },
        { rw mul_comm ((algebra_map ℚ R) ↑(n - 1)) _, rw mul_assoc, apply congr_arg2 _ rfl _,
          rw ← mul_div, rw ring_hom.map_mul, rw map_nat_cast, rw map_nat_cast, rw ← mul_assoc,
          rw mul_assoc (↑(n - 1) * ↑(c ^ n)) _ _, apply congr_arg2 _ rfl _, rw ← ring_hom.map_mul,
          rw mul_one_div, }, }, -- why does rw not solve this?

end

lemma V_h2_4 [normed_algebra ℚ R] [norm_one_class R] (hc' : c.coprime d) (hc : c.coprime p) (n : ℕ) (hn : 1 < n)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : max m (M5 p d R m χ n (ε / 2 / 6) (helper_11 ε hε)) ≤ k) :
  ∥(n : R) * (V_h_def p d R m χ c n k) -
  ((n - 1 : ℕ) : R) * (1 - (asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c *
  (algebra_map ℚ R) (c ^ n : ℚ)) * (U_def p d R m hd χ n k)∥ < ε :=
begin
  -- have h1 := V_h2_2 p d R m hd χ c hc' hc n hn na (∥(d * p^k : R)∥ * ε) _ k _,
  -- rw mul_comm ↑n _ at h1, rw mul_comm ↑(n - 1) _ at h1, rw mul_assoc at h1,
  -- rw mul_assoc (d * p^k : R) _ _ at h1, rw mul_assoc (d * p^k : R) _ _ at h1, rw ← mul_sub at h1,
  -- rw ← nat.cast_pow p _ at h1, rw ← nat.cast_mul d _ at h1, rw ← map_nat_cast (algebra_map ℚ R) at h1,
  -- rw ← smul_eq_mul at h1,
  -- rw @algebra_map_smul _ _ R _ _ _ _ _ _ _ ((d * p^k : ℕ) : ℚ) _ at h1, rw norm_smul at h1,
  -- rw map_nat_cast at h1,
  have div_two_div_six_pos : 0 < ε / 2 / 6, sorry,
  --refine ⟨max m (M5 p d R m χ n (ε / 2 / 6) div_two_div_six_pos / 2), λ k hk, _⟩,
  have h1 : (d * p^k : ℚ) ≠ 0, sorry,
  have h2 : d * p^m ∣ d * p^k, sorry,
  have h3 : k ≠ 0, sorry,
  have h4 : n - 1 ≠ 0, sorry,
  have h5 : ∀ (x : (zmod (d * p^k))ˣ), (x : ℚ) = ((x : zmod (d * p^k)) : ℚ), sorry,
  have h' : d * p ^ k ∣ d * p ^ (2 * k), sorry,
  rw norm_sub_rev,
  rw ← sub_add_sub_cancel,
  swap, { refine (algebra_map ℚ R) ((n - 1 : ℕ) : ℚ) * (U_def p d R m hd χ n k) -
  (∑ (x : (zmod (d * p ^ k))ˣ), ↑((χ * teichmuller_character_mod_p_change_level p d R m ^ n)
  ((units.map (zmod.cast_hom (show d * p ^ m ∣ d * p ^ k, from mul_dvd_mul_left d (pow_dvd_pow p (max_le_iff.1 hk).1))
  (zmod (d * p ^ m))).to_monoid_hom) x)) * (((n - 1 : ℕ) : R) * ((c^n : ℕ) : R) * ((algebra_map ℚ R)
  ((d * p^k : ℚ) * int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k))) * ↑x / ↑(d * p ^ k)))^n) * (algebra_map ℚ R) (1 / (d * p^k)))), },
  conv { congr, skip, rw ← half_add_self ε, },
  rw add_div,
  apply lt_of_le_of_lt (norm_add_le _ _) _,
  apply add_lt_add _ (V_h2_3 p d R m χ c hd n hn na _ (half_pos hε) _ _),
  rw [mul_sub, mul_one, sub_mul, sub_sub, add_comm, ← sub_sub, ← sub_add, add_sub_assoc, map_nat_cast, sub_self, zero_add],
  -- rw [ring_hom.map_mul, ← nat.cast_pow p _, ← nat.cast_mul d _, ← nat.cast_pow p _,
  --   ← nat.cast_mul d _, map_nat_cast],
  convert half_pos hε, rw norm_eq_zero, rw sub_eq_zero, delta U_def,
  conv_rhs { congr, skip, apply_congr, skip, rw used_map_ext p d R m hd χ n k (le_of_lt hn) (max_le_iff.1 hk).1 _, },
  rw finset.mul_sum,
  apply finset.sum_bij,
  { intros a ha, apply finset.mem_univ _, },
  swap 4, { intros a ha, apply is_unit.unit,
   swap, { exact (c : zmod (d * p^(2 * k)))⁻¹.val * (a : zmod (d * p^k)).val, },
   sorry, },
  { intros a ha,
    --rw ← asso_dirichlet_character_eq_char, rw ← asso_dirichlet_character_eq_char,
    rw smul_eq_mul, rw mul_comm _ ((algebra_map ℚ R) (c^n : ℚ)),
    rw ← mul_assoc ((n - 1 : ℕ) : R) _ _,
    rw mul_assoc (((n - 1 : ℕ) : R) * (algebra_map ℚ R) (c^n : ℚ)) _ _,
    conv_rhs { congr, skip, conv { congr, skip, rw mul_assoc, }, rw ← mul_assoc, },
    conv_rhs { rw ← mul_assoc, rw helper_5, rw mul_comm, rw ← asso_dirichlet_character_eq_char, },
    apply congr_arg2,
    { rw ← asso_dirichlet_character_eq_char,
      -- rw ← dirichlet_character.asso_dirichlet_character_mul,
      --simp_rw ← units.coe_hom_apply,
      rw ← monoid_hom.map_mul (asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m ^ n))) _ _,
      --rw ← monoid_hom.map_mul (units.coe_hom R), rw ← monoid_hom.map_mul,
      congr,
      --rw units.ext_iff,
      simp only [units.coe_hom_apply, zmod.nat_cast_val, zmod.cast_id', id.def,
        ring_hom.to_monoid_hom_eq_coe, units.coe_map,
        ring_hom.coe_monoid_hom, zmod.cast_hom_apply, units.coe_mul, zmod.coe_unit_of_coprime],
      rw is_unit.unit_spec, rw zmod.cast_mul h2, rw zmod.cast_inv _ _ _ _ h',
      rw zmod.cast_nat_cast h' _, rw zmod.cast_inv _ _ _ _ h2, rw zmod.cast_nat_cast h2 _,
      rw ← mul_assoc, rw zmod.mul_inv_of_unit _, rw one_mul,
      sorry,
      any_goals { refine zmod.char_p _, },
      -- { apply nat.coprime.mul_right hc' (nat.coprime_pow_spl p c _ hc), },
      any_goals { apply nat.coprime.mul_right hc' (nat.coprime_pow_spl p c _ hc), }, },
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
    apply helper_7 p d c _ _ h, },
  { intros b hb, simp_rw [units.ext_iff, is_unit.unit_spec],
    refine ⟨is_unit.unit _, _, _⟩,
    { exact c * (b : zmod (d * p^k)), },
    { apply is_unit.mul _ (units.is_unit _), sorry, },
    { apply finset.mem_univ _, },
    { rw is_unit.unit_spec, simp_rw zmod.nat_cast_val, rw zmod.cast_id, rw ← mul_assoc,
      rw zmod.cast_inv _ _ _ _ h', rw zmod.cast_nat_cast h' _, rw zmod.inv_mul_of_unit _, rw one_mul,
      { sorry, },
      { refine zmod.char_p _, },
      { apply nat.coprime.mul_right hc' (nat.coprime_pow_spl p c (2 * k) hc), }, }, },
end

lemma V_h2 (hd : d.gcd p = 1) [normed_algebra ℚ R] [norm_one_class R] (hc' : c.coprime d)
  (hc : c.coprime p) (n : ℕ) (hn : 1 < n)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (ε : ℝ) (hε : 0 < ε) : ∃ z : ℕ, ∀ k ≥ z,
  ∥(V_h_def p d R m χ c n k) - (algebra_map ℚ R) (1 / (n : ℚ)) * ((algebra_map ℚ R) (n - 1 : ℕ) *
  (1 - (asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c * ↑c ^ n) *
  ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑p *
    ↑p ^ (n - 1)) * general_bernoulli_number (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)) n))∥ < ε :=
begin
  refine ⟨max m (M5 p d R m χ n (ε / 2 / 6) (helper_11 ε hε) / 2), λ k hk, _⟩,
  have h : (algebra_map ℚ R) (1 / (n : ℚ)) * (algebra_map ℚ R) (n : ℚ) = 1, sorry,
  rw ← one_mul (V_h_def p d R m χ c n k),
  conv { congr, congr, congr, rw ← h, rw mul_assoc, },
  rw ← mul_sub,
  rw ← sub_add_sub_cancel _ ((algebra_map ℚ R) ((n - 1 : ℕ) : ℚ) * (1 - (asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c *
  (algebra_map ℚ R) (c ^ n : ℚ)) * (U_def p d R m hd χ n k)) _,
  -- rw ← sub_add_sub_cancel (V_h_def p d R m χ c n _) _ _,
  rw mul_add,
  apply lt_of_le_of_lt (norm_add_le _ _) _,
  rw ← add_halves ε, apply add_lt_add,
  { apply lt_of_le_of_lt (norm_mul_le _ _) _,
    rw ← lt_div_iff' _,
    { convert V_h2_4 p d R m hd χ c hc' hc n hn na (ε / 2 / ∥(algebra_map ℚ R) (1 / ↑n)∥) _ k _,
      rw map_nat_cast, rw map_nat_cast,
      sorry,
      sorry, },
    { rw norm_pos_iff, sorry, }, },
  --apply classical.some_spec (helper_12 p d R m hd χ c n (ε/2) (half_pos hε)) k _,

  { simp_rw [← nat.cast_pow c _, map_nat_cast],
    conv { congr, congr, congr, skip, -- rw mul_assoc, rw mul_assoc ↑(n - 1) _ _,
      rw ← mul_sub (((n - 1 : ℕ) : R) * _), },
    sorry, },
end

noncomputable def N3' [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (ε : ℝ) (hε : 0 < ε) : ℕ :=
Inf {z : ℕ | ∀ k ≥ z, ∥(V_h_def p d R m χ c n k) + ((algebra_map ℚ R) (1 / ↑n) *
  (1 - (asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c * ↑c ^ n) *
  ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑p *
    ↑p ^ (n - 1)) * general_bernoulli_number (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)) n))∥ < ε }

lemma N3_spec (hd : d.gcd p = 1) [normed_algebra ℚ R] [norm_one_class R] (hc' : c.coprime d)
  (hc : c.coprime p) (n : ℕ) (hn : 1 < n)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (ε : ℝ) (hε : 0 < ε) (k : ℕ)
  (hk : N3' p d R m χ c n ε hε ≤ k) :
  ∥(V_h_def p d R m χ c n k) + ((algebra_map ℚ R) (1 / ↑n) *
  (1 - (asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c * ↑c ^ n) *
  ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑p *
    ↑p ^ (n - 1)) * general_bernoulli_number (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)) n))∥ < ε :=
begin
  delta N3' at hk,
  apply nat_spec' _ _ k hk,
  refine ⟨_, _⟩,
  { refine classical.some (V_h2 p d R m χ c hd hc' hc n hn na ε hε), },
  { rw set.mem_set_of_eq,
    --simp only [ge_iff_le, map_nat_cast, monoid_hom.coe_mk, set.mem_set_of_eq],
    refine classical.some_spec (V_h2 p d R m χ c hd hc' hc n hn na ε hε), },
  refine ⟨classical.some (V_h2 p d R m χ c hd hc' hc n hn na ε hε),
    classical.some_spec (V_h2 p d R m χ c hd hc' hc n hn na ε hε)⟩,
end

lemma V [normed_algebra ℚ R] [norm_one_class R] (hc' : c.coprime d) (hc : c.coprime p) (n : ℕ)
  (hn : 1 < n) (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥) :
  filter.tendsto (λ j : ℕ, V_def p d R m hd χ c n j)
  /-∑ (x : (zmod (d * p ^ j))ˣ), (used_map p d R m hd χ n)
  ((units.map (zmod.cast_hom (dvd_mul_right d (p^j)) (zmod d)).to_monoid_hom) x,
  rev_coe p ((units.map (zmod.cast_hom (dvd_mul_left (p^j) d) (zmod (p ^ j))).to_monoid_hom) x)) •
  (algebra_map ℚ R) (int.fract (↑(((zmod.chinese_remainder (nat.coprime_pow_spl p d j hd)).inv_fun
  (↑(((units.chinese_remainder (nat.coprime_pow_spl p d j hd)) x).fst),
  ↑(((units.chinese_remainder (nat.coprime_pow_spl p d j hd)) x).snd))).val) / (↑d * ↑p ^ j))))-/
  -- ∑ (x : (zmod d)ˣ × (zmod (p ^ j))ˣ),
  -- (used_map p d R m hd χ n) (x.fst, rev_coe p x.snd) • (algebra_map ℚ R) (↑c * int.fract
  -- (↑((((c : zmod (d * p^(2 * n))) : zmod (d * p^n)))⁻¹ * (zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).inv_fun
  -- (↑(x.fst), ↑(x.snd))) / (↑d * ↑p ^ j))))
  filter.at_top (nhds (( algebra_map ℚ R ((n + 1) / n) - (algebra_map ℚ R (1 / n)) *
  asso_dirichlet_character (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) (c) * c^n ) * ((1 -
  asso_dirichlet_character (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) n))) ) :=
begin
  rw metric.tendsto_at_top,
  intros ε hε,
  have four_pos : 0 < ε/4, linarith,
  simp_rw dist_eq_norm,
  set s : set ℕ := {m, (M1 p d R m hd χ c hc hc' n (ε/2) (half_pos hε)),
    (M2 p d R m hd χ n (ε/4) four_pos), (N3' p d R m χ c n (ε/4) four_pos)} with hs,
  refine ⟨Sup s, λ x hx, _⟩,
--  conv { congr, congr, conv { congr, apply_congr, skip, rw int.fract_eq_self.2 _,
--  rw [used_map_ext p d R m hd χ _ _ _ _], skip, apply_congr (le_of_max_le_left hx),
--  apply_congr zero_le_and_lt_one, }, },
  --delta used_map, delta neg_pow', delta neg_pow'_to_hom,
  conv { congr, congr, rw ← sub_add_sub_cancel _ (((((χ * ((teichmuller_character_mod_p_change_level p d R m)^n)) (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime_pow_spl p c m hc⟩))
   * (c : R)^n)) * U_def p d R m hd χ n x : R) + (V_h_def p d R m χ c n x)), },
  -- conv { congr, congr, rw ← sub_add_sub_cancel _ ((U_def p d R m hd χ n x) -
  --   (V_h_def p d R m χ c n x)) _, },
  apply lt_of_le_of_lt (norm_add_le _ _) _,
  rw ← sub_sub,
  rw ← half_add_self ε, rw add_div, rw add_div,
  have hx' : ∀ y ∈ s, y ≤ x,
  { intros y hy, apply le_trans _ hx,
    apply le_cSup _ hy,
    { apply set.finite.bdd_above,
      simp only [set.finite_singleton, set.finite.insert], }, },
  apply add_lt_add (M1_spec p d R m hd χ c hc hc' n hn na (ε/2) (half_pos hε) x _) _,
  { apply hx', rw hs,
    simp only [set.mem_insert_iff, eq_self_iff_true, true_or, or_true], },
  rw div_self _,
  { rw ring_hom.map_add, rw ring_hom.map_one, rw ← add_sub (1 : R) _ _,
    rw add_mul, rw one_mul,
    rw [-- ← sub_sub,
    add_sub_right_comm _ (V_h_def p d R m χ c n x) _],-- sub_sub],
    apply lt_of_le_of_lt (norm_sub_le _ _) _,
    rw ← half_add_self (ε/2), rw add_div,
    have : ε/2/2 = ε/4, linarith,
    rw this,
    apply add_lt_add (M2_spec p d R m hd χ n (ε/4) four_pos x _) _,
    { apply hx', rw hs, simp only [set.mem_insert_iff, eq_self_iff_true, true_or, or_true], },
    conv { congr, congr, congr, skip, congr,
    conv { congr, rw ← mul_one ((algebra_map ℚ R) (1 / ↑n)), }, rw mul_assoc, rw ← mul_sub, },
    apply N3_spec p d R m hd χ c n (ε/4) four_pos x _,
    { apply hx', rw hs,
      simp only [set.mem_insert_iff, eq_self_iff_true, true_or, or_true],
      simp only [set.mem_singleton, or_true], }, },
  { rw nat.cast_ne_zero, apply hn, },
end

lemma W [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) :
  filter.tendsto (λ j : ℕ, ∑ (x : (zmod (d * p ^ j))ˣ), (used_map p d R m hd χ n)
  ((units.map (zmod.cast_hom (dvd_mul_right d (p^j)) (zmod d)).to_monoid_hom) x,
  rev_coe p d _ x) •
-- rev_coe p ((units.map (zmod.cast_hom (dvd_mul_left (p^j) d) (zmod (p ^ j))).to_monoid_hom) x)) •
  (algebra_map ℚ R) ((↑c - 1) / 2))
  -- ∑ (x : (zmod d)ˣ × (zmod (p ^ j))ˣ),
  -- (used_map p d R m hd χ n) (x.fst, rev_coe p x.snd) • (algebra_map ℚ R) ((↑c - 1) / 2))
  filter.at_top (nhds 0) :=
begin
  rw metric.tendsto_at_top, intros ε hε,
  refine ⟨1, λ n hn, _⟩,
  rw dist_eq_norm,
  rw sub_zero, simp_rw smul_eq_mul R, simp_rw ← finset.sum_mul,

  sorry
end

theorem p_adic_L_function_eval_neg_int [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) :
   (n : R) * (p_adic_L_function' p d R m hd χ hc hc' na (neg_pow' p d R (n - 1))) =
   -(1 - (χ (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime_pow_spl p c m hc⟩))
   * (neg_pow' p d R n (zmod.unit_of_coprime c hc', is_unit.unit ((is_unit_iff_not_dvd p c)
   ((nat.prime.coprime_iff_not_dvd (fact.out _)).1 (nat.coprime.symm hc))
     )) ))) * (1 - ((asso_dirichlet_character (dirichlet_character.mul χ
     ((teichmuller_character_mod_p_change_level p d R m)^n))) p * p^(n - 1)) ) *
   (general_bernoulli_number (dirichlet_character.mul χ
     ((teichmuller_character_mod_p_change_level p d R m)^n)) n) :=
begin
  --symmetry,
--  rw ← eq_div_iff_mul_eq',
  delta p_adic_L_function',
  --change (n : R) * (measure.integral (bernoulli_measure' p d R hc hc' hd na))
   --(used_map p d R m hd χ n) = _, --simp,
  delta measure.integral,
  simp only [monoid_hom.coe_comp, ring_hom.to_monoid_hom_eq_coe, mul_equiv.coe_to_monoid_hom,
    monoid_hom.coe_prod_map, continuous_linear_map.coe_mk', linear_map.coe_mk, neg_sub,
    monoid_hom.coe_mk],
  delta dense_inducing.extend,
  --change (n : R) * lim (filter.comap (inclusion ((zmod d)ˣ × ℤ_[p]ˣ) R)
  --  (nhds (used_map p d R m hd χ n))) ((bernoulli_measure' p d R hc hc' hd na).val).to_fun = _,
  have := (trying p d R hd hc hc' na (used_map p d R m hd χ n) _ _),
  -- add filter.tendsto.lim_eq later
  swap 2, { refine λ j : ℕ, ∑ (a : (zmod (d * p^j))ˣ),
     (used_map p d R m hd χ n) (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_right _ _)
     (zmod d) _ (zmod.char_p d)).to_monoid_hom a,
     rev_coe p d _ a) •
-- rev_coe p (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_left _ _) (zmod (p^j)) _ _).to_monoid_hom a)) •
     (locally_constant.char_fn R (is_clopen_units_clopen_from p d j
     ((units.chinese_remainder (nat.coprime_pow_spl p d j hd)) a))), },
    -- refine λ j : ℕ, ∑ (a : (zmod d)ˣ × (zmod (p ^ j))ˣ),
    -- (used_map p d R m hd χ n) (a.fst, rev_coe p a.snd) • (locally_constant.char_fn R
    -- (is_clopen_units_clopen_from p d j a)), },
  swap, { convert fn_eq_sum_char_fn p d R hd _, ext,
  --rw locally_constant.coe_continuous_map,
  --convert finset.sum_apply' a,
  simp_rw ← locally_constant.to_continuous_map_smul p d R _ _,
  rw continuous_map.coe_sum,
  rw locally_constant.coe_continuous_map,
  rw finset.sum_apply,
  conv_rhs { congr, skip, funext, rw locally_constant.coe_continuous_map, },
  rw [← locally_constant.coe_fn_add_monoid_hom_apply, add_monoid_hom.map_sum
    (@locally_constant.coe_fn_add_monoid_hom ((zmod d)ˣ × ℤ_[p]ˣ) R _ _) _ (finset.univ),
    finset.sum_apply],
  simp_rw locally_constant.coe_fn_add_monoid_hom_apply,
  apply finset.sum_congr _ _,
  { ext, simp, },
  intros y hy, refl, },
  --rw filter.lim_eq_iff _,
  conv at this { congr, funext, rw linear_map.map_sum,
    conv { apply_congr, skip, rw linear_map.map_smul, rw bernoulli_measure'_eval_char_fn, rw E_c,
    simp only, --rw alg_hom.map_add,
    rw map_add, rw map_sub, rw smul_add, rw smul_sub, }, rw finset.sum_add_distrib,
    rw finset.sum_sub_distrib, },


  sorry,
end

-- don't really need to change level to d*p^m for ω, right?
