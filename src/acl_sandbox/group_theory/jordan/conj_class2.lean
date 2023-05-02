import .conj_class_count
import group_theory.group_action.conj_act
import group_theory.group_action.quotient
import algebra.group.semiconj
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

lemma kerφ_le_alternating_iff
  (g : equiv.perm α) (m : multiset ℕ) (hg : g.cycle_type = m) :
mul_action.stabilizer (conj_act (equiv.perm α)) g ≤ alternating_group α
↔ ((∀ i ∈ m, odd i) ∧ (m.sum + 1 ≥ fintype.card α) ∧ (∀ i, m.count i ≤ 1))  :=
begin
  rw set_like.le_def,
  simp_rw equiv.perm.mem_alternating_group,
  split,

  { intro h,
    suffices h_odd, suffices h_fixed, suffices h_count,
    split, exact h_odd,
    split, exact h_fixed, exact h_count,

    { -- ∀ i, m.count i ≤ 1
      rw [← multiset.nodup_iff_count_le_one, ← hg, equiv.perm.cycle_type_def],
      rw multiset.nodup_map_iff_inj_on (g.cycle_factors_finset.nodup),
      simp only [function.comp_app, ← finset.mem_def],
      by_contradiction hm,
      push_neg at hm,
      obtain ⟨c, hc, d, hd, hm, hm'⟩ := hm,
      let τ : equiv.perm (g.cycle_factors_finset) := equiv.swap ⟨c, hc⟩ ⟨d, hd⟩,
      obtain ⟨a, ha⟩ := on_cycle_factors.exists_base_points g,
      suffices hτ : τ ∈ on_cycle_factors.Iφ g,

      let kk := on_cycle_factors.φ' ha ⟨τ, hτ⟩,
      let k : equiv.perm α := conj_act.of_conj_act (↑kk),
      -- obtain ⟨a, k, ha, hk1, hk2, hka, hksup⟩ := is_surjective_aux g τ _,
      have hk1 : k * g = g * k,
      { rw ← equiv.coe_inj, exact on_cycle_factors.k_commute ha hτ, },
      have hk2 : ∀ (c : g.cycle_factors_finset), (conj_act.to_conj_act k) • (c : equiv.perm α) = τ c,
      { intro c,
        rw conj_act.smul_def ,
        simp only [conj_act.of_conj_act_to_conj_act],
        rw mul_inv_eq_iff_eq_mul,
        ext x,
        exact on_cycle_factors.k_cycle_apply ha hτ c x, },
      have hka : k ∘ a = a ∘ τ,
      { ext c, exact on_cycle_factors.k_apply ha c 0 hτ, },
      have hksup : k.support ≤ g.support ,
      { intros x,
        simp only [equiv.perm.mem_support],
        intros hx' hx, apply hx',
        rw ← equiv.perm.not_mem_support at hx,
        exact on_cycle_factors.k_apply_of_not_mem_support ha x hx, },
      suffices hsign_k : k.sign = -1,
      { rw [h _, ← units.eq_iff] at hsign_k, exact int.no_confusion hsign_k,
        exact kk.prop, },
      { /- prouver que k est le produit des transpositions à support disjoint
          [(g ^ n) (a c), (g ^ n) (a d)], pour 0 ≤ n < c.support.card
          mais il va suffire de remarquer que k ^ 2 = 1, et de contrôler son support -/
        suffices : k.cycle_type = multiset.repeat 2 (c.support.card),
        { rw equiv.perm.sign_of_cycle_type, rw this,
          simp only [multiset.sum_repeat, algebra.id.smul_eq_mul, multiset.card_repeat],
          rw odd.neg_one_pow,
          rw nat.odd_add',
          simp only [h_odd c.support.card (begin rw [← hg, equiv.perm.cycle_type_def, multiset.mem_map], exact ⟨c, hc, rfl⟩, end), true_iff],
          rw mul_comm, apply even_two_mul, },

        -- on_cycle_count.same_cycle_of_mem_support

        have hk_apply : ∀ (c : g.cycle_factors_finset) (m n : ℕ),
          (k ^ m) ((g ^ n : equiv.perm α) (a c)) = (g ^ n) (a ((τ ^ m) c)),
        { suffices : ∀ (m n: ℕ), commute (k ^ m) (g ^ n),
          intros c m n,
          simp only [commute, semiconj_by] at this,
          rw [← equiv.perm.mul_apply, this, equiv.perm.mul_apply, embedding_like.apply_eq_iff_eq],
          induction m with m hrec,
          { simp only [pow_zero, equiv.perm.coe_one, id.def], },
          { rw [pow_succ, equiv.perm.mul_apply],
            rw [hrec],
            rw on_cycle_factors.φ'_apply ha hτ,
            rw on_cycle_factors.k_apply_base ha _ hτ ,
            rw pow_succ, rw equiv.perm.coe_mul, },

          apply commute.pow_pow,
          rw [commute, semiconj_by, ← mul_inv_eq_iff_eq_mul],
          rw ← mul_action.conj_act.mem_stabilizer_iff,
          exact kk.prop, },

        suffices : ∀ i ∈ k.cycle_type, i = 2,
        { rw ← multiset.eq_repeat' at this,
          rw this,
          apply congr_arg2 _ rfl,
          have this' := equiv.perm.sum_cycle_type k,
          rw this at this',
          simp only [multiset.sum_repeat, algebra.id.smul_eq_mul] at this',
          rw ← mul_left_inj' , rw this',
          suffices this2 : k.support = c.support ∪ d.support,
          rw this2, rw finset.card_union_eq _,
          suffices this3 : d.support.card = c.support.card,
          rw this3, rw mul_two,
          exact hm.symm,
          rw ← equiv.perm.disjoint_iff_disjoint_support,
          by_contradiction hcd, apply hm',
          exact set.pairwise.eq g.cycle_factors_finset_pairwise_disjoint hc hd hcd,
          { -- k.support = c.support ∪ d.support
            ext x,
            split,
            { intro hx,
--              obtain ⟨cx, hcx, hcx'⟩ := hsame_cycle x (hksup hx),
              obtain ⟨cx, hcx⟩ := on_cycle_factors.same_cycle_of_mem_support ha x (hksup hx),
              -- have hcx' := (on_cycle_factors.same_cycle_of_mem_support' ha cx (hksup hx)).mpr hcx,
              have hxcx : x ∈ (cx : equiv.perm α).support,
              { rw ← on_cycle_factors.same_cycle.is_cycle_of ha cx hcx,
              -- rw ← (on_cycle_factors.same_cycle_of_mem_support' ha cx (hksup hx)).mpr hcx,
                rw equiv.perm.mem_support_cycle_of_iff,
                split, refl, exact hksup hx, },
              suffices : c = cx ∨ d = cx,
              rw finset.mem_union,
              cases this with hccx hdcx,
              { apply or.intro_left, rw hccx, exact hxcx, },
              { apply or.intro_right, rw hdcx, exact hxcx, },
              { obtain ⟨n, hn, hnx⟩ := hcx.nat',
                rw [equiv.perm.mem_support, ← hnx] at hx,
                specialize hk_apply cx 1,
                simp only [pow_one] at hk_apply,
                rw hk_apply at hx,
                rw function.injective.ne_iff (equiv.injective _) at hx,
                have hx' : τ cx ≠ cx := ne_of_apply_ne a hx,
                rw ← equiv.perm.mem_support at hx',
                simp only [τ] at hx',
                rw equiv.perm.support_swap _ at hx',
                simp only [finset.mem_insert, finset.mem_singleton] at hx',
                cases hx' with hx' hx',
                { apply or.intro_left, rw ← subtype.coe_inj at hx', rw hx', refl, },
                { apply or.intro_right, rw ← subtype.coe_inj at hx', rw hx', refl, },
                intro h, rw ← subtype.coe_inj at h, apply hm', exact h, }, },
            { intro hx,
              -- obtain ⟨cx, hcx, hcx'⟩ := hsame_cycle x _,
              obtain ⟨cx, hcx⟩ := on_cycle_factors.same_cycle_of_mem_support ha x _,
              have hcx' := on_cycle_factors.same_cycle.is_cycle_of ha cx hcx,
              obtain ⟨n, hn, hnx⟩ := hcx.nat',
              rw equiv.perm.mem_support,
              specialize hk_apply cx 1, simp only [pow_one] at hk_apply,
              rw [← hnx, hk_apply],
              rw function.injective.ne_iff (equiv.injective _),
              intro haτcx_eq_acx, dsimp at haτcx_eq_acx,
              have : ¬ equiv.perm.disjoint (cx : equiv.perm α) (τ cx : equiv.perm α),
              { rw equiv.perm.disjoint_iff_support_disjoint,
                rw finset.not_disjoint_iff,
                use a cx,
                apply and.intro (ha cx),
                rw ← haτcx_eq_acx, exact ha (τ cx), },
              have this' := (set.pairwise.eq g.cycle_factors_finset_pairwise_disjoint cx.prop (τ cx).prop this).symm,
              rw subtype.coe_inj at this',
              rw [← equiv.perm.not_mem_support] at this',
              rw [equiv.perm.support_swap _] at this',
              simp only [finset.mem_insert, finset.mem_singleton] at this',
              apply this',
              simp only [← subtype.coe_inj, subtype.coe_mk, ← hcx'],
              rw finset.mem_union at hx,
              cases hx with hx hx,
              { apply or.intro_left,
                exact (equiv.perm.cycle_is_cycle_of hx hc).symm, },
              { apply or.intro_right,
                exact (equiv.perm.cycle_is_cycle_of hx hd).symm, },

              { intro h, simp only [← subtype.coe_inj, subtype.coe_mk] at h,
                exact hm' h, },

              { rw finset.mem_union at hx, cases hx with hx hx,
                exact equiv.perm.mem_cycle_factors_finset_support_le hc hx,
                exact equiv.perm.mem_cycle_factors_finset_support_le hd hx, } }, },
          norm_num, },
        -- ∀ i ∈ k.cycle_type, i = 2
        suffices hk2 : order_of k = 2,
        { have hk2' : nat.prime (order_of k), rw hk2, exact nat.prime_two,
          obtain ⟨n, hn⟩ := equiv.perm.cycle_type_prime_order hk2',
          intros i hi,
          rw [hn, hk2, multiset.mem_repeat] at hi,
          exact hi.right, },
          apply order_of_eq_prime,
          { -- k ^ 2 = 1,
            ext x,
            simp only [equiv.perm.coe_one, id.def],
            by_cases hx : x ∈ g.support,
            { -- obtain ⟨cx, hcx, hcx'⟩ := hsame_cycle x hx,
              obtain ⟨cx, hcx⟩ := on_cycle_factors.same_cycle_of_mem_support ha x hx,
              -- have hcx' := on_cycle_factors.same_cycle.is_cycle_of ha cx hcx,
              obtain ⟨n, hn, rfl⟩ := hcx.nat',
              rw hk_apply cx 2 n,
              apply congr_arg,
              apply congr_arg,
              suffices hτ2 : τ ^ 2 = 1,
              rw [hτ2, equiv.perm.coe_one, id.def],
              rw pow_two, rw equiv.swap_mul_self, } ,
            { -- lorsque x ∉ g.support
              rw ← equiv.perm.not_mem_support,
              intro hx', apply hx,
              apply hksup,
              apply equiv.perm.support_pow_le k 2,
              exact hx', }, },
          intro hk,
          specialize hk2 ⟨c, hc⟩,
          simp only [hk, conj_act.to_conj_act_one, subtype.coe_mk, one_smul, equiv.swap_apply_left] at hk2,
          exact hm' hk2, },
      { simp only [τ],
        intro x,
        by_cases hx : x = ⟨c, hc⟩,
        { rw [hx, equiv.swap_apply_left], exact hm.symm, },
        by_cases hx' : x = ⟨d, hd⟩,
        { rw [hx', equiv.swap_apply_right], exact hm, },
        { rw [equiv.swap_apply_of_ne_of_ne hx hx'], }, }, },

    { -- m.sum + 1 ≥ fintype.card α
      rw ge_iff_le, rw ← not_lt, intro hm,
      rw [nat.lt_iff_add_one_le] at hm,
      rw add_assoc at hm,
      change m.sum + 2 ≤ _ at hm,
      suffices : 1 < fintype.card (mul_action.fixed_by (equiv.perm α) α g),
      { obtain ⟨a, b, hab⟩ := fintype.exists_pair_of_one_lt_card this,
        let k := on_cycle_factors.ψ g ⟨equiv.swap a b, λ d hd, 1⟩,
        suffices : k.sign ≠ 1,
        { apply this,
          apply h,
          change conj_act.to_conj_act k ∈ _,
          apply subgroup.map_subtype_le,
          rw on_cycle_factors.hφ_ker_eq_ψ_range,
          exact set.mem_range_self _, },
        suffices : k = equiv.swap a b,
        { rw [this, equiv.perm.sign_swap],
          intro h', rw ← units.eq_iff at h',
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
        rw [← hg, equiv.perm.sum_cycle_type], exact finset.card_le_univ _, } },
    { -- all cycle lengths are odd
      intros i hi,
      rw [← hg] at hi,
      rw [equiv.perm.cycle_type_def g, multiset.mem_map] at hi,
      obtain ⟨c, hc, rfl⟩ := hi,
      rw ← finset.mem_def at hc,
      have Hc_cycle : c.is_cycle,
      { rw equiv.perm.mem_cycle_factors_finset_iff at hc, exact hc.left, },

      let k := on_cycle_factors.ψ g ⟨1, λ d hd, ite (c = d) ⟨d, subgroup.mem_zpowers d⟩ 1⟩,
      suffices : c.sign = 1,
      { rw [equiv.perm.is_cycle.sign Hc_cycle] at this,
        rw nat.odd_iff_not_even,
        rw ← neg_one_pow_eq_one_iff_even _,
        intro this', rw this' at this,
        simpa [← units.eq_iff, units.coe_one, units.coe_neg_one] using this,
        intro h, simpa [← units.eq_iff, units.coe_one, units.coe_neg_one] using h, },
      suffices : k = c,
      { rw ← this, apply h,
        change conj_act.to_conj_act k ∈ _,
        apply subgroup.map_subtype_le,
        rw on_cycle_factors.hφ_ker_eq_ψ_range,
        exact set.mem_range_self _, },

      -- k = c
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
     },
  { rintros ⟨h_odd, h_fixed, h_count⟩ x hx,
    suffices hx' : x ∈ set.range (on_cycle_factors.ψ g),
    obtain ⟨⟨y, uv⟩, rfl⟩ := set.mem_range.mp hx',
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
      apply h_odd, rw ← hg, rw equiv.perm.cycle_type_def,
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
      rw tsub_le_iff_left , exact h_fixed, },

      -- x ∈ set.range (on_cycle_factors.ψ g)
      rw ← on_cycle_factors.hφ_ker_eq_ψ_range,
      suffices : (on_cycle_factors.φ g).ker = ⊤,
      rw [this],
      simp only [subgroup.mem_map, subgroup.mem_top, subgroup.coe_subtype, exists_true_left],
      exact ⟨⟨x, hx⟩, rfl⟩,

      -- (on_cycle_factors.φ g).ker = ⊤
      rw eq_top_iff,
      intros y _,
      suffices : (on_cycle_factors.φ g).range = ⊥,
      { rw [monoid_hom.mem_ker, ← subgroup.mem_bot, ← this, monoid_hom.mem_range],
        exact ⟨y, rfl⟩, },
      rw eq_bot_iff,
      intro z,
      rw ← on_cycle_factors.Iφ_eq_range, rw subgroup.mem_bot,
      intro hz,
      apply equiv.ext,
      intro c,
      rw [← multiset.nodup_iff_count_le_one, ← hg, equiv.perm.cycle_type_def, multiset.nodup_map_iff_inj_on (equiv.perm.cycle_factors_finset g).nodup] at h_count,
      rw [equiv.perm.coe_one, id.def, ← subtype.coe_inj],
      exact h_count (z c) (z c).prop c c.prop (hz c), },
end

lemma equiv.perm.is_cycle_eq_cycle_of_iff (g c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset) (x : α) :
  c = g.cycle_of x ↔ x ∈ c.support :=
begin
  split,
  { intro hcx,
    rw [equiv.perm.mem_support, hcx, equiv.perm.cycle_of_apply_self, ne.def, ← equiv.perm.cycle_of_eq_one_iff, ← hcx],
    exact equiv.perm.is_cycle.ne_one ((equiv.perm.mem_cycle_factors_finset_iff.mp hc).left), },
  { intro hx, exact equiv.perm.cycle_is_cycle_of hx hc, },
end

example (g c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset) (x y : α)
  (hx : x ∈ c.support) : g.same_cycle x y ↔ y ∈ c.support :=
begin
  rw (equiv.perm.is_cycle_eq_cycle_of_iff g c hc x).mpr hx,
  rw [equiv.perm.mem_support_cycle_of_iff, iff_self_and],
  intro _,
  exact equiv.perm.mem_cycle_factors_finset_support_le hc hx,
end
