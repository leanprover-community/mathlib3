import .conj_class_count
import group_theory.group_action.conj_act
import group_theory.group_action.quotient
import .index_normal
import .equivariant_map

variables {G : Type*} [group G] (H : subgroup G)

lemma subgroup.relindex_swap {G : Type*} [group G] (H K : subgroup G) :
  H.relindex K * K.index = K.relindex H * H.index :=
begin
  rw [← subgroup.inf_relindex_right H, subgroup.relindex_mul_index (inf_le_right : H ⊓ K ≤ K)],
  rw [← subgroup.inf_relindex_right K, subgroup.relindex_mul_index (inf_le_right : K ⊓ H ≤ H)],
  rw inf_comm,
end

lemma subgroup.nat.card_eq_mul' (H K : subgroup G) (hK : 0 < K.index):
nat.card K = (H.relindex K) * nat.card (K.subgroup_of H)  :=
begin
--  haveI hnH : subgroup.normal H := subgroup.normal_of_index_eq_two hH,
  rw mul_comm,
  apply nat.eq_of_mul_eq_mul_right hK,
  rw subgroup.card_mul_index K,
  rw mul_assoc,
  rw ← subgroup.card_mul_index H,
  rw ← subgroup.card_mul_index (K.subgroup_of H),
  simp only [mul_assoc],
  apply congr_arg2 (*) rfl,
  apply subgroup.relindex_swap,
end



lemma conj_act.stabilizer_eq_comap (g : H) :
subgroup.comap
((conj_act.to_conj_act).to_monoid_hom.comp (H.subtype.comp (conj_act.of_conj_act).to_monoid_hom) : conj_act H →* conj_act G)
(mul_action.stabilizer (conj_act G) (g : G))
=
mul_action.stabilizer (conj_act H) g :=
begin
  ext k,
  induction k using conj_act.rec with k,
  simp only [subgroup.mem_comap, monoid_hom.coe_comp, mul_equiv.coe_to_monoid_hom, subgroup.coe_subtype, function.comp_app,
  mul_action.mem_stabilizer_iff],
  simp only [conj_act.of_conj_act_to_conj_act, conj_act.smul_def],
  rw ← subtype.coe_inj,
  simp only [subgroup.coe_mul, subgroup.coe_inv],
end

lemma mem_zpowers_centralizer_iff (h k : G) :
k ∈ (subgroup.zpowers h).centralizer ↔ h * k = k * h :=
begin
  rw subgroup.mem_centralizer_iff ,
  split,
  intro H,
  apply H h, exact subgroup.mem_zpowers h,
  intro H,
  intros g hg,
  rw subgroup.zpowers_eq_closure at hg,
  apply subgroup.closure_induction hg,
  { intros x hx, simp only [set.mem_singleton_iff] at hx, rw hx, exact H, },
  { rw [one_mul, mul_one], },
  { intros x y hx hy, rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc], },
  { intros x hx, rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hx, mul_assoc, mul_inv_self, mul_one], },
end

lemma subgroup.relindex_of_index_two (K : subgroup G) (hH : H.index = 2) :
  ¬ (K ≤ H) → H.relindex K = 2 :=
begin
  intro hK,
  haveI : subgroup.normal H := subgroup.normal_of_index_eq_two hH,
  suffices : H.relindex K = 1 ∨ H.relindex K = 2,
  cases this with h1 h2,
  { exfalso, apply hK, rw ← subgroup.relindex_eq_one, exact h1, },
  { exact h2, },
  apply nat.prime.eq_one_or_self_of_dvd nat.prime_two,
  rw ← subgroup.relindex_sup_left,
  rw ← hH,
  refine subgroup.relindex_dvd_index_of_normal H (H ⊔ K),
end

lemma mul_action.card_orbit_eq_stabilizer_index {G : Type*} [group G] [fintype G] {X : Type*} [fintype X] [mul_action G X] (x : X) :
  nat.card (mul_action.orbit G x) = (mul_action.stabilizer G x).index :=
begin
  classical,
  simp only [nat.card_eq_fintype_card],
  apply nat.eq_of_mul_eq_mul_right  (_ : 0 < fintype.card (mul_action.stabilizer G x)),
  rw mul_action.card_orbit_mul_card_stabilizer_eq_card_group,
  rw subgroup.index_mul_card,
  refine fintype.card_pos,
end

lemma mul_action.card_orbit_of_subgroup {G : Type*} [group G] [fintype G] {X : Type*} [fintype X] [mul_action G X]
  (H : subgroup G) (x : X) :
  (subgroup.map (subgroup.subtype H) (mul_action.stabilizer H x)).relindex (mul_action.stabilizer G x)
  * nat.card (mul_action.orbit G x)
    = H.index * nat.card (mul_action.orbit H x) :=
begin
  classical,
  simp only [mul_action.card_orbit_eq_stabilizer_index],
  rw subgroup.relindex_mul_index,
  rw mul_comm,
  rw subgroup.index_map,
  simp only [subgroup.ker_subtype, sup_bot_eq, subgroup.subtype_range],

  rw subgroup.map_le_iff_le_comap,
  intro h,
  rw subgroup.mem_comap, simp only [mul_action.mem_stabilizer_iff],
  exact id,
end

lemma mul_action.card_orbit_of_equivariant
  {G : Type*} [group G] [fintype G] {X : Type*} [fintype X] [mul_action G X]
  {H : Type*} [group H] [fintype H] {Y : Type*} [fintype Y][mul_action H Y]
  (φ : H →* G) (f : Y →ₑ[φ] X) (y : Y) (hy : φ.ker ≤ mul_action.stabilizer H y):
  (subgroup.map φ (mul_action.stabilizer H y)).relindex (mul_action.stabilizer G (f y))
  * nat.card (mul_action.orbit G (f y))
    = φ.range.index * nat.card (mul_action.orbit H y) :=
begin
  classical,
  simp only [mul_action.card_orbit_eq_stabilizer_index],
  rw subgroup.relindex_mul_index,
  rw mul_comm,
  rw subgroup.index_map,
  simp only [subgroup.ker_subtype, sup_bot_eq, subgroup.subtype_range, sup_of_le_left hy],
  rw subgroup.map_le_iff_le_comap,
  intro h,
  rw subgroup.mem_comap, simp only [mul_action.mem_stabilizer_iff],
  intro h', rw [← f.map_smul h y, h'],
end

example [fintype G] (hH : H.index = 2) (K : subgroup (conj_act G)) :
  (H.map (conj_act.to_conj_act.to_monoid_hom : G →* conj_act G)).relindex K = 1 :=
begin
  rw ←  subgroup.map_comap_eq_self_of_surjective _ K,
--  suffices : K = subgroup.map conj_act.to_conj_act.to_monoid_hom (subgroup.comap conj_act.of_conj_act.to_monoid_hom K),
  -- rw this,
  rw ← subgroup.relindex_comap,
  rw subgroup.comap_map_eq_self_of_injective,

  rw subgroup.relindex_eq_one,
  sorry,
  exact (conj_act.to_conj_act.injective),
  exact (conj_act.of_conj_act.surjective),
end

lemma subgroup.conj_class_card_of_index [fintype G] (g : H) :
  (H.map (conj_act.to_conj_act.to_monoid_hom : G →* conj_act G)).relindex
    (mul_action.stabilizer (conj_act G) (g : G))
    * nat.card (mul_action.orbit (conj_act G) (g : G))
  = H.index * nat.card (mul_action.orbit (conj_act H) g) :=
begin
  classical,
  let φ : conj_act H →* conj_act G := ((conj_act.to_conj_act.to_monoid_hom).comp H.subtype).comp (conj_act.of_conj_act.to_monoid_hom),
  let f : H →ₑ[φ] G := {
    to_fun := H.subtype.to_fun,
    map_smul' := λ m a, by simp [φ, conj_act.smul_def], },
  suffices hφ : φ.range.index = H.index,
  rw ← hφ, rw ← mul_action.card_orbit_of_equivariant φ f g _,
  apply congr_arg2 (*) _ rfl,
  dsimp [f],
  rw [← subgroup.inf_relindex_right],
  apply congr_arg2 subgroup.relindex _ rfl,
  { rw ← conj_act.stabilizer_eq_comap,
    dsimp only [φ],
    simp only [← subgroup.map_map, ← subgroup.comap_comap],

    rw [subgroup.map_comap_eq],
  apply le_antisymm,
    { intro k,
      rw subgroup.mem_inf,
      rintro ⟨hk, hk'⟩,
      rw subgroup.mem_map at hk,
      obtain ⟨h, hH, rfl⟩ := hk,
      rw subgroup.mem_map,
      use h,
      rw subgroup.mem_map,
      use (⟨h, hH⟩ : H),
      split,
      rw subgroup.mem_inf,
      split,
      rw monoid_hom.mem_range,
      use conj_act.to_conj_act (⟨h, hH⟩ : H),
      simp only [mul_action.mem_stabilizer_iff] at hk' ⊢,
      simp only [mul_equiv.coe_to_monoid_hom, conj_act.of_conj_act_to_conj_act],
      simp only [subgroup.comap_subtype],
      rw subgroup.mem_subgroup_of,
      rw subgroup.mem_comap,
      exact hk',
      refl, },
    { intros k hk,
      rw subgroup.mem_map at hk,
      obtain ⟨h, hh, rfl⟩ := hk,
      rw subgroup.mem_map at hh,
      obtain ⟨k, hk, rfl⟩ := hh,
      rw subgroup.mem_inf at hk,
      simp only [subgroup.mem_comap] at hk,
      split,
      simp only [subgroup.coe_subtype, mul_equiv.coe_to_monoid_hom, subgroup.coe_to_submonoid, subgroup.coe_map, set.mem_image, set_like.mem_coe, mul_equiv.apply_eq_iff_eq, exists_eq_right, set_like.coe_mem],
      exact hk.2, }, },

  suffices : φ.ker = ⊥,
  rw this, exact bot_le,
  rw monoid_hom.ker_eq_bot_iff,
  simp only [φ, monoid_hom.coe_comp ],

  rw function.injective.of_comp_iff _,
  exact conj_act.of_conj_act.injective,
  rw function.injective.of_comp_iff _,
  exact H.subtype_injective,
  exact conj_act.to_conj_act.injective,

  dsimp only [φ],
  rw [monoid_hom.range_eq_map, ← subgroup.map_map , subgroup.index_map],
  rw subgroup.map_top_of_surjective _,
  simp only [top_sup_eq, subgroup.index_top, one_mul],
  rw [monoid_hom.range_eq_map, ← subgroup.map_map , subgroup.index_map],

  rw ← mul_one H.index,
  apply congr_arg2 (*),
  apply congr_arg,
  have : H = H ⊔ ⊥, by rw sup_bot_eq, conv_rhs {rw this,},
  apply congr_arg2 (⊔),
  rw ← monoid_hom.range_eq_map, exact subgroup.subtype_range H,
  rw monoid_hom.ker_eq_bot_iff, exact conj_act.to_conj_act.injective,
  rw subgroup.index_eq_one,
  rw monoid_hom.range_top_iff_surjective,
  exact conj_act.to_conj_act.surjective,
  exact conj_act.to_conj_act.surjective,
end


open_locale classical

example (hH: H.index = 2) [fintype G] (g : H) :
  (if ((mul_action.stabilizer (conj_act G) (g : G)) ≤ H) then 2 else 1)
  * fintype.card (mul_action.orbit (conj_act H) g)
  = fintype.card (mul_action.orbit (conj_act G) (g : G)) :=
begin
  suffices : fintype.card (mul_action.stabilizer (conj_act G) (g : G))
    = (ite ((mul_action.stabilizer (conj_act G) (g : G)) ≤ H) 1 2)
    * (fintype.card (mul_action.stabilizer (conj_act H) g)),

  apply nat.eq_of_mul_eq_mul_right  _,
  rw mul_assoc,
  rw mul_action.card_orbit_mul_card_stabilizer_eq_card_group _ (g : G),
  rw this,
  simp only [mul_assoc], rw mul_comm, rw ← mul_assoc,
  rw conj_act.card,
  rw ← subgroup.index_mul_card H,
  rw hH,
  simp only [← mul_assoc], rw mul_comm,
  nth_rewrite 2 [mul_comm],
  simp only [mul_assoc],
      rw mul_action.card_orbit_mul_card_stabilizer_eq_card_group,
  simp only [← mul_assoc],
  rw conj_act.card,
  apply congr_arg2 _ _ rfl,
  by_cases hg : mul_action.stabilizer (conj_act G) (g : G) ≤ H,
  { simp only [if_pos hg, mul_one], },
  { simp only [if_neg hg, one_mul], },

  exact fintype.card_pos,

  simp_rw conj_act.stabilizer_eq_centralizer,
  rw ← nat.card_eq_fintype_card,
  rw subgroup.nat.card_eq_mul' H,
  apply congr_arg2,
  { split_ifs with hK,
    rw subgroup.relindex_eq_one, exact hK,
    exact subgroup.relindex_of_index_two _ _ hH hK, },
  { rw nat.card_eq_fintype_card,
    apply fintype.card_congr',
    apply congr_arg coe_sort,
    { ext k,
      rw subgroup.mem_subgroup_of,
      simp only [mem_zpowers_centralizer_iff],
      simp only [← subgroup.coe_mul],  rw subtype.coe_inj, }, },
  rw zero_lt_iff, exact subgroup.index_ne_zero_of_finite,
end

variables {α : Type*} [fintype α] [decidable_eq α]

variable (g : equiv.perm α)
#check on_cycle_factors.φ g
#check on_cycle_factors.ψ g

lemma on_cycle_factors.sign_ψ (g : equiv.perm α) (s : finset (equiv.perm α)) (hs : s ⊆ g.cycle_factors_finset)  (uv : equiv.perm (mul_action.fixed_by (equiv.perm α) α g)) (k : Π (c ∈ s), subgroup.zpowers (c : equiv.perm α)) :
  (on_cycle_factors.ψ_aux g s hs ⟨uv, k⟩).sign
  = uv.sign * s.prod (λi,
    equiv.perm.sign (dite (i ∈ s) (λ (hc : i ∈ s), ((k i hc) : equiv.perm α)) (λ (hc : i ∉ s), 1))
  ) :=
begin
  dsimp only [on_cycle_factors.ψ_aux],
  simp only [equiv.perm.sign_mul, equiv.perm.sign_of_subtype],
  rw finset.noncomm_prod_map,
  rw finset.noncomm_prod_eq_prod ,
end

lemma kerφ_le_alternating_iff
  (g : equiv.perm α) (m : multiset ℕ) (hg : g.cycle_type = m) :
(subgroup.map (mul_action.stabilizer (conj_act (equiv.perm α)) g).subtype (on_cycle_factors.φ g).ker ≤ alternating_group α)
↔ ((∀ i ∈ m, odd i) ∧ m.sum + 1 ≥ fintype.card α)  :=
begin
  rw set_like.le_def,
  simp_rw equiv.perm.mem_alternating_group,
  have hφ_ker_eq_ψ_range' := on_cycle_factors.hφ_ker_eq_ψ_range g,
  split,
  { intro h,
    split,
    { intros i hi,
      rw [← hg] at hi,
      rw [equiv.perm.cycle_type_def g, multiset.mem_map] at hi,
      obtain ⟨c, hc, rfl⟩ := hi,
      rw ← finset.mem_def at hc,
      have Hc_cycle : c.is_cycle,
      { rw equiv.perm.mem_cycle_factors_finset_iff at hc, exact hc.left, },

      let k := on_cycle_factors.ψ g ⟨1, λ d hd, ite (c = d) ⟨d, subgroup.mem_zpowers d⟩ 1⟩,
--      have hkψ: k ∈ set.range (on_cycle_factors.ψ g) := set.mem_range_self _,
      let hk := (on_cycle_factors.hφ_ker_eq_ψ_range g k).mpr (set.mem_range_self _),
      specialize h hk,
      suffices : c.sign = 1,
      { rw [equiv.perm.is_cycle.sign Hc_cycle] at this,
        rw nat.odd_iff_not_even,
        rw ← neg_one_pow_eq_one_iff_even _,
        intro this', rw this' at this,
        simpa [← units.eq_iff, units.coe_one, units.coe_neg_one] using this,
        intro h, simpa [← units.eq_iff, units.coe_one, units.coe_neg_one] using h, },
      suffices : k = c,
      { rw ← this, exact h, },

      simp only [k, on_cycle_factors.ψ, on_cycle_factors.ψ_aux],
      simp only [dite_eq_ite, map_one, one_mul],

      suffices h_eq : g.cycle_factors_finset = {c} ∪ (g.cycle_factors_finset \ {c}),
      rw @finset.noncomm_prod_congr _ _ _ _ _ _ (λ x, ite (x = c) c 1) h_eq,
      rw finset.noncomm_prod_union_of_disjoint (finset.disjoint_sdiff),
      conv_rhs {rw ← mul_one c},
      apply congr_arg2 (*),
      rw [finset.noncomm_prod_singleton, if_pos rfl],
      rw finset.noncomm_prod_eq_pow_card ,
      exact one_pow _,
      { intros i hi, rw if_neg,
        simp only [finset.mem_sdiff, finset.mem_singleton] at hi, exact hi.right, },
      { intros x hx,
        rw if_pos,
        { simp only [finset.union_sdiff_self_eq_union, finset.mem_union, finset.mem_singleton] at hx,
          by_cases hxc : c = x,
          rw if_pos hxc, dsimp only, rw if_pos hxc.symm, rw hxc, refl,
          rw if_neg hxc, dsimp only, simp only [if_neg (ne.symm hxc), subgroup.coe_one], },
        rw finset.union_sdiff_of_subset at hx, exact hx,
        simp only [finset.singleton_subset_iff], exact hc, },
      { rw [finset.union_sdiff_of_subset],
        rw [finset.singleton_subset_iff], exact hc, }, },
    { rw ge_iff_le, rw ← not_lt, intro hm,
      rw [nat.lt_iff_add_one_le] at hm,
      rw add_assoc at hm,
      change m.sum + 2 ≤ _ at hm,
      suffices : 1 < fintype.card (mul_action.fixed_by (equiv.perm α) α g),
      { obtain ⟨a, b, hab⟩ := fintype.exists_pair_of_one_lt_card this,
        let k := on_cycle_factors.ψ g ⟨equiv.swap a b, λ d hd, 1⟩,
        have hkψ : k ∈ set.range (on_cycle_factors.ψ g) := set.mem_range_self _,
        let hk := (on_cycle_factors.hφ_ker_eq_ψ_range g k).mpr (set.mem_range_self _),
         specialize h hk,
        suffices : k = equiv.swap a b,
        { change equiv.perm.sign k = 1 at h,
          rw [this, equiv.perm.sign_swap] at h,
          simpa only [← units.eq_iff] using h,
          intro hab', apply hab,
          rw ← subtype.coe_inj, exact hab', },
        { simp only [k, on_cycle_factors.ψ, on_cycle_factors.ψ_aux],
          simp only [subgroup.coe_one, dite_eq_ite, if_t_t, equiv.perm.of_subtype_swap_eq, mul_right_eq_self],
          rw finset.noncomm_prod_eq_pow_card, rw one_pow,
          intros x hx, refl, }, },
      { rw on_cycle_factors.equiv.perm.card_fixed_by g m hg,
        rw add_comm at hm,
        rw [nat.lt_iff_add_one_le, nat.le_sub_iff_right _],
        exact hm,
        rw [← hg, equiv.perm.sum_cycle_type], exact finset.card_le_univ _, } } },
  { intros h x hx,
    rw ← conj_act.to_conj_act_of_conj_act x at hx,
    rw on_cycle_factors.hφ_ker_eq_ψ_range at hx,
    change x ∈ set.range (on_cycle_factors.ψ g) at hx,
    rw set.mem_range at hx,
    obtain ⟨⟨y, uv⟩, rfl⟩ := hx,
    simp only [on_cycle_factors.ψ, on_cycle_factors.ψ_aux],
    simp only [equiv.perm.sign_mul, equiv.perm.sign_of_subtype],
    convert mul_one _,
    { rw finset.noncomm_prod_map,
      rw finset.noncomm_prod_eq_prod,
      apply finset.prod_eq_one,
      intros c hc,
      rw dif_pos hc,
      let hc' := (uv c hc).prop,
      rw subgroup.mem_zpowers_iff at hc',
      obtain ⟨k, hkc⟩ := hc',
      rw ← hkc,
      simp only [map_zpow],
      suffices : equiv.perm.sign c = 1, rw this, simp only [one_zpow],
      rw [equiv.perm.is_cycle.sign , odd.neg_one_pow, neg_neg],
      apply h.left, rw ← hg, rw equiv.perm.cycle_type_def,
      rw multiset.mem_map,
      use c, apply and.intro hc, refl,
      rw equiv.perm.mem_cycle_factors_finset_iff at hc,
      exact hc.left, },
    { apply symm,
      suffices : y = 1,
      rw this, exact equiv.perm.sign_one,
      rw ← equiv.perm.card_support_le_one ,
      apply le_trans (finset.card_le_univ _),
      rw on_cycle_factors.equiv.perm.card_fixed_by g m hg,
      rw tsub_le_iff_left , exact h.right, }, },
end

example (g : equiv.perm α) (τ: equiv.perm (g.cycle_factors_finset))
  (H : ∀ c : g.cycle_factors_finset, (c : equiv.perm α).support.card = ((τ c) : equiv.perm α).support.card)
  (a : g.cycle_factors_finset → α) (k : equiv.perm α)
    (ha : ∀ (c : g.cycle_factors_finset), a c ∈ (c : equiv.perm α).support)
    (hkg : g * k = k * g)
    (hkτ : ∀ (c : g.cycle_factors_finset), (conj_act.to_conj_act k) • (c : equiv.perm α) = τ c)
    (hka : k ∘ a = a ∘ τ) :
  k.sign = τ.cycle_factors_finset.prod (λ d, 1)
:= sorry

example (g : equiv.perm α) (τ: equiv.perm (g.cycle_factors_finset))
  (H : ∀ c : g.cycle_factors_finset, (c : equiv.perm α).support.card = ((τ c) : equiv.perm α).support.card) (d : τ.cycle_factors_finset) :
  ∃ (n : ℕ), ∀ c ∈ (d : equiv.perm (g.cycle_factors_finset)).support,
    n = (c : equiv.perm α).support.card :=
begin
  have hd := d.prop, rw equiv.perm.mem_cycle_factors_finset_iff at hd,
  have hd' : ∀ a ∈ d.val.support, τ.cycle_of a = d,
  { intros a ha, apply equiv.ext , intro x,
    rw equiv.perm.cycle_of_apply,
    by_cases hx : x ∈ d.val.support,
    rw if_pos, exact (hd.right x hx).symm,
    sorry,
    sorry },
  suffices hd_ne : d.val.support.nonempty,
  let c := Exists.some hd_ne,
  have hc  : c ∈ d.val.support := hd_ne.some_spec,
  use c.val.support.card,
  intros x hx,
  suffices : ∃ (k : ℕ), x = (τ ^ k) c,
  obtain ⟨k, rfl⟩ := this,
  induction k with k ih,
  { sorry },
  { sorry },
  suffices : (τ : equiv.perm (g.cycle_factors_finset)).same_cycle c x,
  obtain ⟨k, hk, hk', hk''⟩ := equiv.perm.same_cycle.nat τ this,
  exact ⟨k, hk''.symm⟩,

end



open_locale classical

/-

G → G/H
K
(K : H ∩ K) = (KH : H) =
-/
example {G : Type*} [group G] (H K : subgroup G) (hH : H.index = 2):
H.relindex K = ite (K ≤ H) 1 2 :=
begin
  haveI : subgroup.normal H := subgroup.normal_of_index_eq_two hH,
  suffices : H.relindex K = 1 ∨ H.relindex K = 2,
  cases this with h1 h2,
  { rw if_pos, exact h1, rw ← subgroup.relindex_eq_one, exact h1, },
  { rw if_neg, exact h2, rw ← subgroup.relindex_eq_one, rw h2, norm_num, },
  apply nat.prime.eq_one_or_self_of_dvd nat.prime_two,
  rw ← subgroup.relindex_sup_left,
  rw ← hH,
  refine subgroup.relindex_dvd_index_of_normal H (H ⊔ K),
end
