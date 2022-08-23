import ring_theory.ideal.operations
import linear_algebra.finite_dimensional
import ring_theory.dimension.order_height

variables {R M M' M'' : Type*} [comm_ring R] [add_comm_group M] [module R M] (p : submodule R M)
variables [add_comm_group M'] [module R M'] [add_comm_group M''] [module R M'']

noncomputable
def submodule.length : with_top ℕ :=
(set.Iio p).chain_height

noncomputable
def module.length (R M : Type*) [comm_ring R] [add_comm_group M] [module R M] : with_top ℕ :=
(⊤ : submodule R M).length

def module.length_succ (R M : Type*) [comm_ring R] [add_comm_group M] [module R M] :
  module.length R M + 1 = (set.univ : set $ submodule R M).chain_height :=
begin
  convert (set.chain_height_insert_of_forall_ge _ ⊤ _).symm,
  { rw [set.Iio_insert, set.Iic_top] },
  { intros p e, exact e }
end

lemma set.dedup_mem_subchain {α : Type*} [partial_order α] [decidable_eq α] (s : set α) (l : list α)
  (h₁ : list.chain' (≤) l) (h₂ : ∀ x ∈ l, x ∈ s) : l.dedup ∈ s.subchain :=
begin
  refine ⟨_, λ i e, h₂ _ (list.mem_dedup.mp e)⟩,
  have := h₁.sublist l.dedup_sublist,
  rw [list.chain'_iff_pairwise] at this ⊢,
  exact (this.and l.nodup_dedup).imp (λ _ _ h, lt_of_le_of_ne h.1 h.2)
end

lemma list.sublist_pw_filter_cons {α : Type*} (x : α) (xs : list α) {r : α → α → Prop}
  [decidable_rel r] : xs.pw_filter r <+ (x :: xs).pw_filter r :=
begin
  by_cases ∀ (b : α), b ∈ list.pw_filter r xs → r x b,
  { rw list.pw_filter_cons_of_pos h, exact list.sublist.cons _ _ _ (list.sublist.refl _) },
  { rw list.pw_filter_cons_of_neg h },
end

lemma list.dedup_sublist_dedup_cons {α : Type*} (x : α) (xs : list α) [decidable_eq α] :
  xs.dedup <+ (x :: xs).dedup :=
list.sublist_pw_filter_cons x xs

lemma list.length_le_map_dedup_length_add {α β γ : Type*} [preorder α] [partial_order β] [partial_order γ]
  [decidable_eq β] [decidable_eq γ] (f : α → β) (g : α → γ)
  (hf : monotone f) (hg : monotone g)
  (H : ∀ x y, f x = f y → g x = g y → x ≤ y → x = y) (l : list α) (hl : l.chain' (<))
  (hl' : l ≠ []) :
  l.length + 1 ≤ (l.map f).dedup.length + (l.map g).dedup.length :=
begin
  induction l with x xs h,
  { exact (hl' rfl).elim },
  { cases xs with x' xs, { simp },
    cases hl with _ _ _ _ hx hl,
    refine (add_le_add (h hl (λ e, by cases e)) (le_refl 1)).trans _,
    by_cases e : f x = f x',
    { have : g x ∉ g x' :: xs.map g,
      { have : g x < g x' := lt_of_le_of_ne (hg hx.le) (λ e', hx.ne (H _ _ e e' hx.le)),
        cases list.chain_iff_pairwise.mp hl with _ _ hxs,
        rintros (e|e),
        { exact this.ne e },
        { obtain ⟨a, ha, ha'⟩ := list.mem_map.mp e,
          exact (this.trans_le (hg (hxs a ha).le)).ne ha'.symm } },
      rw add_assoc,
      apply add_le_add,
      { exact list.length_le_of_sublist (list.dedup_sublist_dedup_cons _ _) },
      { exact (congr_arg list.length (list.dedup_cons_of_not_mem this).symm).le } },
    { have : f x ∉ f x' :: xs.map f,
      { have : f x < f x' := lt_of_le_of_ne (hf hx.le) e,
        cases list.chain_iff_pairwise.mp hl with _ _ hxs,
        rintros (e|e),
        { exact this.ne e },
        { obtain ⟨a, ha, ha'⟩ := list.mem_map.mp e,
          exact (this.trans_le (hf (hxs a ha).le)).ne ha'.symm } },
      rw add_right_comm,
      apply add_le_add,
      { exact (congr_arg list.length (list.dedup_cons_of_not_mem this).symm).le },
      { exact list.length_le_of_sublist (list.dedup_sublist_dedup_cons _ _) } } },
end

lemma module.length_eq_add_of_exact (f : M' →ₗ[R] M) (g : M →ₗ[R] M'') (hf : function.injective f)
  (hg : function.surjective g) (e : f.range = g.ker) :
    module.length R M = module.length R M' + module.length R M'' :=
begin
  classical,
  suffices : module.length R M + 1 = (module.length R M' + module.length R M'') + 1,
  { apply le_antisymm;
      exact (with_top.add_le_add_iff_right with_top.one_ne_top).mp (by simp [this]) },
  rw [module.length_succ, add_assoc, module.length_succ],
  apply le_antisymm,
  { apply supr₂_le _,
    intros l hl,
    by_cases hl' : l = [], { subst hl', exact zero_le _ },
    have : l.length + 1 ≤
      (l.map $ submodule.comap f).dedup.length + (l.map $ submodule.map g).dedup.length,
    { apply list.length_le_map_dedup_length_add,
      { exact λ _ _ e, submodule.comap_mono e },
      { exact λ _ _ e, submodule.map_mono e },
      { intros p₁ p₂ e₁ e₂ e₃,
        apply e₃.antisymm,
        intros x hx,
        obtain ⟨y, hy, ey⟩ := (show _, from e₂.symm.le) (submodule.mem_map_of_mem hx),
        obtain ⟨z, hz⟩ : x - y ∈ f.range,
        { rw [e, linear_map.mem_ker, map_sub, ey, sub_self] },
        have : z ∈ p₁.comap f,
        { rw [e₁, submodule.mem_comap, hz], exact sub_mem hx (e₃ hy) },
        exact eq_sub_iff_add_eq.mp hz ▸ add_mem this hy },
      { exact hl.1 },
      { exact hl' } },
    rw [← with_top.coe_le_coe, with_top.coe_add, with_top.coe_add] at this,
    apply (with_top.add_le_add_iff_right with_top.one_ne_top).mp,
    rw [add_right_comm, module.length_succ],
    refine this.trans (add_le_add _ _); refine set.length_le_chain_height_of_mem_subchain _
      (set.dedup_mem_subchain _ _ ((list.chain'_map _).mpr $ (hl.1.imp _)) (λ _ _, trivial)),
    { intros _ _ e, exact submodule.comap_mono e.le },
    { intros _ _ e, exact submodule.map_mono e.le },
    all_goals { apply_instance } },
  rw [module.length, submodule.length, ← set.chain_height_image (submodule.map f),
    ← set.chain_height_image (submodule.comap g), ← set.chain_height_union_eq],
  { exact set.chain_height_le_of_subset (set.subset_univ _) },
  { rintros _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩,
    refine (submodule.map_strict_mono_of_injective hf ha).trans_le _,
    rw [submodule.map_top, e, ← submodule.comap_bot],
    exact submodule.comap_mono bot_le },
  { intros _ _,
    simp_rw [lt_iff_le_and_ne, submodule.comap_le_comap_iff_of_surjective hg,
      (submodule.comap_injective_of_surjective hg).ne_iff] },
  { intros _ _,
    simp_rw [lt_iff_le_and_ne, submodule.map_le_map_iff_of_injective hf,
      (submodule.map_injective_of_injective hf).ne_iff] },
end
.

section

open_locale classical

@[simps] noncomputable
def cardinal.to_with_top_nat : cardinal →+ with_top ℕ :=
{ to_fun := λ c, c.to_part_enat.to_with_top,
  map_zero' := by simp only [part_enat.to_with_top_zero', map_zero],
  map_add' := by simp }

end

lemma cardinal.coe_le_to_with_top_nat {c : cardinal} (n : ℕ) :
  ↑n ≤ c.to_with_top_nat ↔ ↑n ≤ c :=
begin
  classical,
  rw ← part_enat.to_with_top_coe,
  refine part_enat.to_with_top_le.trans _,
  change ↑n ≤ dite _ _ _ ↔ _,
  split_ifs,
  { rw [← cardinal.to_nat_cast n, part_enat.coe_le_coe, cardinal.to_nat_le_iff_le_of_lt_aleph_0 _ h,
      cardinal.to_nat_cast],
    exact cardinal.nat_lt_aleph_0 n },
  { simp only [le_top, true_iff], exact (cardinal.nat_lt_aleph_0 n).le.trans (not_lt.mp h) },
end

lemma cardinal.to_with_top_nat_cast (n : ℕ) : cardinal.to_with_top_nat n = n :=
by { rw [cardinal.to_with_top_nat_apply, cardinal.to_part_enat_cast, part_enat.to_with_top_coe] }

lemma module.length_le_rank {R M : Type*} [field R] [add_comm_group M] [module R M] :
  module.length R M ≤ (module.rank R M).to_with_top_nat :=
begin
  rw [← with_top.add_le_add_iff_right with_top.one_ne_top, module.length_succ],
  any_goals { apply_instance },
  by_cases finite_dimensional R M,
  swap,
  { have := is_noetherian.iff_dim_lt_aleph_0.mpr (show is_noetherian), },
  apply supr₂_le _,
  intros l hl,
  have : ∀ i < l.length, ↑i ≤ module.rank R (list.nth_le l i H : _),
  { intros i hi,
    induction i with i h₁ h₂,
    { exact zero_le _ },
    { have := h₁ (i.lt_succ_self.trans hi),
      conv_lhs { rw [nat.succ_eq_add_one, nat.cast_add, nat.cast_one] },

    }


  }
  -- rw [← with_top.coe_one, ← cardinal.to_with_top_nat_cast 1, ← map_add,
  --   cardinal.coe_le_to_with_top_nat],
  -- any_goals { apply_instance },
end
