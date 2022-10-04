import linear_algebra.finite_dimensional

lemma set.eq_empty_or_eq_insert {x : Type*} (s : set x) : s = ∅ ∨ ∃ t (x ∉ t), s = insert x t :=
begin
  rcases s.eq_empty_or_nonempty with (rfl|⟨x, hx⟩),
  { exact or.inl rfl },
  { refine or.inr ⟨s \ {x}, x, _, _⟩; simp [set.insert_eq_of_mem hx] }
end

lemma csupr_subtype {α : Type*} [conditionally_complete_linear_order_bot α]
  {ι : Sort*} {P : ι → Sort*} (f : Π i, P i → α) (hf : ∃ X, ∀ i h, f i h ≤ X) :
    (⨆ i h, f i h) = ⨆ i : {x // P x}, f i i.prop :=
begin
  obtain ⟨X, hf⟩ := hf,
  apply le_antisymm,
  { have : bdd_above (set.range (λ (i : {x // P x}), f _ i.prop)),
    { use X, rintro _ ⟨x, rfl⟩, exact hf _ _ },
    exact csupr_le' (λ i, csupr_le' $ λ h, le_csupr this ⟨i, h⟩) },
  { refine csupr_le' (λ i, le_trans _ (le_csupr _ i)),
    refine le_trans _ (le_csupr _ i.prop),
    { exact rfl.le },
    { use X, rintro _ ⟨x, rfl⟩, exact hf _ _ },
    { use X, rintro _ ⟨x, rfl⟩, exact csupr_le' (hf x) } }
end


lemma cardinal.le_of_add_one_le_add_one {α β : cardinal} (h : α + 1 ≤ β + 1) : α ≤ β :=
begin
  rw [← α.mk_out, ← β.mk_out] at h ⊢,
  rw [← cardinal.mk_option, ← cardinal.mk_option] at h,
  rw [cardinal.le_def] at h ⊢,
  obtain ⟨f⟩ := h,
  cases e : f none,
  { have : ∀ x : α.out, ∃ y : β.out, f x = y,
    { intro x, apply option.ne_none_iff_exists'.mp, intro e', apply option.some_ne_none x,
      apply f.injective, rw [e, ← e'], refl },
    choose y hy,
    refine ⟨⟨y, λ a b h, option.some_injective _ (f.injective _)⟩⟩,
    rw [← option.coe_def, hy, hy, h] },
  { refine ⟨⟨λ a, (f a).elim val id, λ a b (h : (f a).elim val id = (f b).elim val id), _⟩⟩,
    apply option.some_injective, apply f.injective,
    show f a = f b,
    cases ha : f a with a'; cases hb : f b with b',
    { refl },
    all_goals { rw [ha, hb] at h, dsimp at h, subst h },
    { cases f.injective (hb.trans e.symm) },
    { cases f.injective (ha.trans e.symm) } },
end

lemma cardinal.add_one_injective {α β : cardinal} (h : α + 1 = β + 1) : α = β :=
cardinal.eq_of_add_eq_add_right h cardinal.one_lt_aleph_0

lemma cardinal.exists_add_one_eq_iff {α : cardinal} :
  (∃ β, β + 1 = α) ↔ α ≠ 0 :=
begin
  split,
  { rintros ⟨β, rfl⟩ e, exact not_le_of_lt cardinal.zero_lt_one (le_add_self.trans_eq e) },
  { intro e,
    cases le_or_gt cardinal.aleph_0 α,
    { exact ⟨α, cardinal.add_one_eq h⟩ },
    { refine ⟨(α.to_nat - 1 : _), (_ : ↑(α.to_nat - 1 + 1) = α)⟩,
      rw [← bot_eq_zero, ← bot_lt_iff_ne_bot, bot_eq_zero,
        ← cardinal.to_nat_lt_iff_lt_of_lt_aleph_0 _ h, cardinal.zero_to_nat, zero_lt_iff,
        ← nat.one_le_iff_ne_zero] at e,
      rwa [tsub_add_cancel_of_le, cardinal.cast_to_nat_of_lt_aleph_0 h],
      exact e.trans h } }
end

lemma add_one_le_dim_iff_exists_submodule_rank_eq {R : Type*} {M : Type*} [field R]
  [add_comm_group M] [module R M] {c : cardinal} :
  c + 1 ≤ module.rank R M ↔ ∃ p : submodule R M, p ≠ ⊤ ∧ module.rank R p = c :=
begin
  rw le_dim_iff_exists_linear_independent,
  split,
  { rintros ⟨s, e, h⟩,
    obtain ⟨x, hx⟩ := cardinal.mk_ne_zero_iff.mp (show cardinal.mk s ≠ 0, by simp [e]),
    use submodule.span R (s \ {x}),
    split,
    { intro e,
      apply h.not_mem_span_image
        (set.not_mem_compl_iff.mpr (set.mem_singleton (⟨x, hx⟩ : s))),
      simp [set.compl_eq_univ_diff, set.image_diff subtype.coe_injective, e] },
    { have : x ∉ s \ {x} := λ e, e.2 rfl,
      apply cardinal.add_one_injective,
      rw [dim_span_set (h.mono (s.diff_subset {x})), ← e, ← cardinal.mk_insert this,
        set.insert_diff_singleton, set.insert_eq_of_mem hx] } },
  { rintros ⟨p, hp, rfl⟩,
    obtain ⟨x, hx⟩ : ∃ x, x ∉ p := by { revert hp, contrapose!, rw eq_top_iff, exact λ H x _, H x },
    obtain ⟨b, hb, e, h⟩ := exists_linear_independent R (p : set M),
    refine ⟨insert x b, _, h.insert ((e.trans p.span_eq).symm ▸ hx)⟩,
    rw [cardinal.mk_insert (λ e, hx (hb e)), ← e.trans p.span_eq, dim_span_set h] },
end

lemma rank_supr_ne_top_add_one {R : Type*} {M : Type*} [field R] [add_comm_group M] [module R M] :
  (⨆ (p : submodule R M) (h : p ≠ ⊤), module.rank R p + 1) = module.rank R M :=
begin
  rw csupr_subtype,
  swap, { exact ⟨module.rank R M + 1, λ _ _, add_le_add (dim_submodule_le _) rfl.le⟩ },
  apply le_antisymm,
  { exact csupr_le' (λ p, add_one_le_dim_iff_exists_submodule_rank_eq.mpr ⟨p.1, p.2, rfl⟩) },
  { by_cases module.rank R M = 0, { rw h, exact zero_le _ },
    obtain ⟨α, hα⟩ := cardinal.exists_add_one_eq_iff.mpr h,
    obtain ⟨p, hp, rfl⟩ := add_one_le_dim_iff_exists_submodule_rank_eq.mp hα.le,
    have : bdd_above (set.range (λ p : {x : submodule R M // x ≠ ⊤}, module.rank R p + 1)),
    { refine ⟨module.rank R M + 1, _⟩, rintros _ ⟨a, rfl⟩,
      exact add_le_add (dim_submodule_le _) rfl.le },
    exact hα.symm.le.trans (le_csupr this ⟨p, hp⟩) }
end

lemma rank_supr_lt_add_one {R : Type*} {M : Type*} [field R] [add_comm_group M] [module R M]
  (q : submodule R M) :
  (⨆ p < q, module.rank R p + 1) = module.rank R q :=
begin
  rw [← rank_supr_ne_top_add_one, csupr_subtype, csupr_subtype],
  have : ∀ p : { p : submodule R q // p ≠ ⊤ }, p.1.map q.subtype < q,
  { rintros ⟨p, hp⟩, convert q^.map_subtype.order_embedding^.strict_mono (lt_top_iff_ne_top.mpr hp),
    exact q.map_subtype_top.symm },
  let : {x // x < q} ≃ {x : submodule R q // x ≠ ⊤} :=
  { to_fun := λ p, ⟨_, submodule.comap_subtype_eq_top.not.mpr $ not_le_of_lt p.2⟩,
    inv_fun := λ p, ⟨p.1.map q.subtype, this p⟩,
    left_inv := λ p, subtype.ext ((submodule.map_comap_eq _ _).trans $ by simpa using p.2.le),
    right_inv := λ p, by { ext, simp } },
  apply equiv.supr_congr this,
  { rintros ⟨p, hp⟩, congr' 1,
    exact linear_equiv.dim_eq (submodule.comap_subtype_equiv_of_le hp.le) },
  { exact ⟨module.rank R q + 1, λ _ _, add_le_add (dim_submodule_le _) rfl.le⟩ },
  { exact ⟨module.rank R M + 1, λ _ _, add_le_add (dim_submodule_le _) rfl.le⟩ },
end
