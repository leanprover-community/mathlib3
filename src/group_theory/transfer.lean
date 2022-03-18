import group_theory.complement
import group_theory.group_action.basic

open_locale big_operators

namespace subgroup

variables {G : Type*} [group G] {H : subgroup G}

@[to_additive] instance : mul_action G (left_transversals (H : set G)) :=
{ smul := λ g T, ⟨left_coset g T, mem_left_transversals_iff_exists_unique_inv_mul_mem.mpr (λ g', by
  { obtain ⟨t, ht1, ht2⟩ := mem_left_transversals_iff_exists_unique_inv_mul_mem.mp T.2 (g⁻¹ * g'),
    simp_rw [←mul_assoc, ←mul_inv_rev] at ht1 ht2,
    refine ⟨⟨g * t, mem_left_coset g t.2⟩, ht1, _⟩,
    rintros ⟨_, t', ht', rfl⟩ h,
    exact subtype.ext ((mul_right_inj g).mpr (subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ h))) })⟩,
  one_smul := λ T, subtype.ext (one_left_coset T),
  mul_smul := λ g g' T, subtype.ext (left_coset_assoc ↑T g g').symm }

lemma smul_symm_apply_eq_mul_symm_apply_inv_smul
  (g : G) (α : left_transversals (H : set G)) (q : G ⧸ H) :
  ↑((equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp (g • α).2)).symm q) =
    g * ((equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp α.2)).symm
      (g⁻¹ • q : G ⧸ H)) :=
begin
  let w := (equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp α.2)),
  let y := (equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp (g • α).2)),
  change ↑(y.symm q) = ↑(⟨_, mem_left_coset g (subtype.mem _)⟩ : (g • α).1),
  refine subtype.ext_iff.mp (y.symm_apply_eq.mpr _),
  change q = g • (w (w.symm (g⁻¹ • q : G ⧸ H))),
  rw [equiv.apply_symm_apply, ←mul_smul, mul_inv_self, one_smul],
end

variables [fintype (G ⧸ H)] {A : Type*} [comm_group A] (ϕ : H →* A)
  (α β γ : left_transversals (H : set G))

/-- The difference of two left transversals -/
@[to_additive "The difference of two left transversals"]
noncomputable def diff : A :=
let α' := (equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp α.2)).symm,
    β' := (equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp β.2)).symm in
∏ (q : G ⧸ H), ϕ ⟨(α' q)⁻¹ * (β' q),
  (quotient.exact' ((α'.symm_apply_apply q).trans (β'.symm_apply_apply q).symm))⟩

@[to_additive] lemma diff_mul_diff : diff ϕ α β * diff ϕ β γ = diff ϕ α γ :=
finset.prod_mul_distrib.symm.trans (finset.prod_congr rfl (λ q hq, (ϕ.map_mul _ _).symm.trans
  (congr_arg ϕ (subtype.ext (by rw [coe_mul, coe_mk, coe_mk, coe_mk, mul_assoc, mul_inv_cancel_left])))))

@[to_additive] lemma diff_self : diff ϕ α α = 1 :=
mul_right_eq_self.mp (diff_mul_diff ϕ α α α)

@[to_additive] lemma diff_inv : (diff ϕ α β)⁻¹ = diff ϕ β α :=
inv_eq_of_mul_eq_one ((diff_mul_diff ϕ α β α).trans (diff_self ϕ α))

lemma smul_diff_smul (g : G) :
  diff ϕ (g • α) (g • β) = diff ϕ α β :=
finset.prod_bij' (λ q hq, g⁻¹ • q) (λ q hq, finset.mem_univ (g⁻¹ • q))
    (λ q hq, congr_arg ϕ (subtype.ext
      (by simp_rw [coe_mk, smul_symm_apply_eq_mul_symm_apply_inv_smul, mul_inv_rev, mul_assoc, inv_mul_cancel_left])))
    (λ q hq, g • q) (λ q hq, finset.mem_univ (g • q)) (λ q hq, smul_inv_smul g q)
      (λ q hq, inv_smul_smul g q)

lemma smul_diff_self_eq_smul_diff_self (g : G) : diff ϕ (g • α) α = diff ϕ (g • β) β :=
by rw [←diff_mul_diff, smul_diff_smul, mul_comm, diff_mul_diff]

lemma mul_smul_diff_self_eq_smul_diff_self_mul_smul_diff_self (g h : G) :
  diff ϕ ((g * h) • α) α = diff ϕ (g • α) α * diff ϕ (h • α) α :=
by rw [mul_smul, ←diff_mul_diff, smul_diff_smul, mul_comm]

-- hence, the transfer `g ↦ diff ϕ (g • α) α` is a well-defined homomorphism.

-- `https://web.ma.utexas.edu/users/vandyke/notes/257_notes/notes.pdf` (alternate Schur-Zassenhaus?)

lemma transfer (ϕ : H →* A) : G →* A :=
let key : inhabited (left_transversals (H : set G)) := left_transversals.inhabited in
{ to_fun := λ g, begin
  sorry
end }

end subgroup
