/-
# order.complete_lattice (after Sup_eq_supr)

-- Unfortunately `ι : Sort u_4` doesn't work with `set ι`
theorem bsupr_eq_supr {ι : Type*} {s : ι → α}
  {p : set ι} : (⨆ i (H : p i), s i) = ⨆ (i : p), s i :=
begin
  refine le_antisymm (bsupr_le (λ i hi, _)) _,
  { change s (⟨i, hi⟩ : p) ≤ supr (λ (i : p), s i),
    apply le_supr (λ (i : p), s i) _, },
  simp only [supr_le_iff, set_coe.forall],
  intros i hi,
  rw subtype.coe_mk,
  exact le_bsupr i hi,
end

-/

/-
# linear_algebra.basic (after mem_supr')

-- this is **definitely** going to be atrocious
lemma mem_bsupr {p : ι → Prop} (f : ι → submodule R M) (x : M) :
  x ∈ (⨆ i (H : p i), f i) ↔
  ∃ v : ι →₀ M, (∀ i, v i ∈ f i) ∧ ∑ i in v.support, v i = x ∧ (∀ i, ¬ p i → v i = 0) :=
begin
  classical,
  change set ι at p,
  refine ⟨λ h, _, λ h, _⟩,
  { rw bsupr_eq_supr at h,
    rcases (mem_supr' _).mp h with ⟨v', hv', hsum⟩,
    change p →₀ M at v',
    -- define `v = v'` where `p i` is true and zero otherwise
    let v : ι →₀ M :=
      ⟨v'.support.map (function.embedding.subtype p),
       λ (i : ι), dite (p i) (λ hi, v' ⟨i, hi⟩) (λ _, 0), _⟩,
    refine ⟨v, _, _, _⟩,
    { intros i,
      simp only [finsupp.coe_mk],
      split_ifs with hi,
      { exact hv' ⟨i, hi⟩ },
      exact zero_mem _ },
    { simp only [finsupp.coe_mk, dite_eq_ite, function.embedding.coe_subtype, finset.sum_map,
        subtype.coe_eta],
      convert hsum,
      ext i, split_ifs with hi, refl,
      exfalso, apply hi, exact i.2 },
    { intros i hi,
      simp only [finsupp.coe_mk, dif_neg hi], },
    intros i,
    simp only [exists_prop, function.embedding.coe_subtype, set_coe.exists, finset.mem_map,
      exists_and_distrib_right, exists_eq_right, finsupp.mem_support_iff, ne.def, subtype.coe_mk],
    split_ifs with hi,
    { refine ⟨λ hh, _, λ hh, ⟨hi, hh⟩⟩,
      cases hh with _ key, exact key },
    refine ⟨λ hh _, _, λ hh, _⟩,
    { cases hh with key _,
      exact hi key },
    exfalso, exact hh rfl },
  rcases h with ⟨v, hv, hsum, hzero⟩,
  have hle: (⨆ i ∈ v.support, f i) ≤ ⨆ (i : ι) (H : p i), f i,
  { refine bsupr_le_bsupr' (λ i hi, _),
    revert hi, contrapose!,
    refine λ h, finsupp.not_mem_support_iff.mpr (hzero i h), },
  have key: x ∈ ⨆ i ∈ v.support, f i,
  { rw ← hsum, exact sum_mem_bsupr (λ i hi, hv i), },
  exact hle key,
end
-/

/-
# linear_algebra.direct_sum_module (after submodule_is_internal.to_add_subgroup)

lemma submodule_is_internal.apply
  {R M : Type*} [ring R] [add_comm_group M] [module R M]
  (A : ι → submodule R M) [Π i (x : A i), decidable (x ≠ 0)] (x : ⨁ i, A i) :
  direct_sum.to_module R ι M (λ i, (A i).subtype) x = ∑ i in x.support, x i :=
begin
  simp only [direct_sum.to_module, dfinsupp.sum_add_hom_apply, linear_map.to_add_monoid_hom_coe,
    linear_map.coe_mk, dfinsupp.lsum_apply, submodule.subtype],
  refine finset.sum_congr rfl (λ x hx, rfl),
end

noncomputable def submodule_is_internal.to_equiv
  {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M]
  (A : ι → submodule R M) (hA : submodule_is_internal A) :
  (⨁ i, A i) ≃ₗ[R] M :=
begin
  letI : add_comm_group (⨁ (i : ι), (A i)) := direct_sum.add_comm_group (λ i, A i),
  exact linear_equiv.of_bijective (direct_sum.to_module R ι M (λ i, (A i).subtype))
    (linear_map.ker_eq_bot_of_injective hA.injective)
    (linear_map.range_eq_top.mpr hA.surjective),
end

@[simp] lemma submodule_is_internal.to_equiv_apply
  {R M : Type*} [ring R] [add_comm_group M] [module R M]
  (A : ι → submodule R M) (hA : submodule_is_internal A) (x : ⨁ i, A i) :
  submodule_is_internal.to_equiv A hA x = to_module R ι M (λ i, (A i).subtype) x :=
rfl

lemma equiv_of_is_internal_symm_single_apply
  {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M]
  (A : ι → submodule R M) [Π i (x : A i), decidable (x ≠ 0)]
  (hA : submodule_is_internal A) (i : ι) (x : M) (hx : x ∈ A i) :
  (submodule_is_internal.to_equiv A hA).symm x = dfinsupp.single i ⟨x, hx⟩ :=
begin
  apply_fun submodule_is_internal.to_equiv A hA using linear_equiv.injective _,
  rw linear_equiv.apply_symm_apply, dsimp, rw submodule_is_internal.apply,
  by_cases h : x = 0,
  { rw dfinsupp.support_single_eq_zero,
    rwa finset.sum_empty,
    rwa ← submodule.coe_eq_zero },
  rw [dfinsupp.support_single_ne_zero, finset.sum_singleton,
    dfinsupp.single_eq_same, submodule.coe_mk],
  refine λ h', h _,
  rw [← submodule.coe_eq_zero.mpr h', submodule.coe_mk]
end

-/
