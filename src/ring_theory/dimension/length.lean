import field_theory.finiteness
import ring_theory.artinian
import ring_theory.dimension.order_height
import ring_theory.dimension.rank
import ring_theory.dimension.min_generator_card

variables {R M M' M'' : Type*} [comm_ring R] [add_comm_group M] [module R M] (p : submodule R M)
variables [add_comm_group M'] [module R M'] [add_comm_group M''] [module R M'']

noncomputable
def submodule.length : with_top ℕ :=
(set.Iio p).chain_height

noncomputable
def module.length (R M : Type*) [comm_ring R] [add_comm_group M] [module R M] : with_top ℕ :=
(⊤ : submodule R M).length

lemma submodule.length_succ :
  p.length + 1 = (set.Iic p).chain_height  :=
begin
  convert (set.chain_height_insert_of_forall_ge _ p _).symm,
  { rw set.Iio_insert },
  { intros p e, exact e }
end

lemma module.length_succ (R M : Type*) [comm_ring R] [add_comm_group M] [module R M] :
  module.length R M + 1 = (set.univ : set $ submodule R M).chain_height :=
begin
  rw [module.length, submodule.length_succ, set.Iic_top],
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

lemma submodule.supr_lt_length_succ :
  (⨆ q < p, q.length + 1) = p.length :=
begin
  rw [submodule.length, set.chain_height_eq_supr_Iic, supr_subtype', supr_subtype'],
  congr,
  ext1 ⟨q, hq⟩,
  rw [submodule.length, subtype.coe_mk, ← set.chain_height_insert_of_forall_ge _ q,
    set.Iio_insert, set.inter_eq_right_iff_subset.mpr _],
  { intros x hx, exact has_le.le.trans_lt hx hq },
  { intros a ha, exact ha }
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

lemma cardinal.to_with_top_nat_apply' (c : cardinal) :
  c.to_with_top_nat = if c < cardinal.aleph_0 then c.to_nat else ⊤ :=
begin
  dsimp [cardinal.to_with_top_nat, cardinal.to_part_enat],
  split_ifs,
  { rw [if_pos h, part_enat.to_with_top_coe] },
  { rw part_enat.to_with_top_top }
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

lemma cardinal.coe_eq_to_with_top_nat_iff {c : cardinal} {n : ℕ} :
  ↑n = c.to_with_top_nat ↔ c = n ∧ c < cardinal.aleph_0 :=
begin
  rw cardinal.to_with_top_nat_apply',
  split_ifs with h,
  { rw [with_top.coe_eq_coe, and_iff_left h, ← cardinal.nat_cast_inj,
      cardinal.cast_to_nat_of_lt_aleph_0 h, eq_comm] },
  { simp [h] },
end

lemma cardinal.to_with_top_nat_eq_top_iff {c : cardinal} :
  c.to_with_top_nat = ⊤ ↔ cardinal.aleph_0 ≤ c :=
begin
  rw [cardinal.to_with_top_nat_apply'],
  dsimp,
  split_ifs,
  { simp [h] },
  { rw not_lt at h, simpa }
end

lemma cardinal.to_with_top_nat_cast (n : ℕ) : cardinal.to_with_top_nat n = n :=
by { rw [cardinal.to_with_top_nat_apply, cardinal.to_part_enat_cast, part_enat.to_with_top_coe] }

lemma cardinal.to_with_top_nat_one : cardinal.to_with_top_nat 1 = 1 :=
begin
  rw [cardinal.to_with_top_nat_apply', if_pos cardinal.one_lt_aleph_0, ← with_top.coe_one,
    with_top.coe_eq_coe, cardinal.to_nat_eq_one.mpr rfl],
end


lemma cardinal.to_with_top_nat_mono : monotone cardinal.to_with_top_nat :=
begin
  rintros a b e x (e' : _ = ↑x),
  rw [eq_comm, cardinal.coe_eq_to_with_top_nat_iff] at e',
  have := cardinal.cast_to_nat_of_lt_aleph_0 (e.trans_lt e'.2),
  rw ← this,
  rw [← this, e'.1, cardinal.nat_cast_le] at e,
  exact ⟨a.to_nat, cardinal.to_with_top_nat_cast _, e⟩
end

lemma cardinal.supr_to_with_top_nat {ι : Type*} {f : ι → cardinal} (hf : bdd_above $ set.range f) :
  (⨆ i, f i).to_with_top_nat = ⨆ i, (f i).to_with_top_nat :=
begin
  refine le_antisymm _ (supr_le (λ i, cardinal.to_with_top_nat_mono $ le_csupr hf i)),
  rw cardinal.to_with_top_nat_apply',
  split_ifs,
  { have : ∀ i, (f i).to_with_top_nat = (f i).to_nat :=
      λ i, (f i).to_with_top_nat_apply'.trans (if_pos $ (le_csupr hf i).trans_lt h),
    simp_rw this,
    rintros a (e : _ = (a : with_top ℕ)), refine ⟨_, rfl, _⟩,
    have : bdd_above (set.range (λ i, (f i).to_nat)),
    { rw [← with_top.supr_coe_lt_top, e], exact with_top.coe_lt_top _ },
    rw [← cardinal.to_nat_cast a,
      cardinal.to_nat_le_iff_le_of_lt_aleph_0 h (cardinal.nat_lt_aleph_0 _)],
    refine csupr_le' (λ i, _),
    rw [← with_top.coe_supr _ this, with_top.coe_eq_coe] at e,
    rw [← e, ← cardinal.cast_to_nat_of_lt_aleph_0 ((le_csupr hf i).trans_lt h),
      cardinal.nat_cast_le],
    exact le_csupr this i },
  { rintros a (e : _ = (a : with_top ℕ)),
    apply h.elim,
    refine (csupr_le' _).trans_lt (cardinal.nat_lt_aleph_0 a),
    intro i,
    have : (f i).to_with_top_nat ≤ a := ((le_supr _ _).trans_eq e : _),
    rw [cardinal.to_with_top_nat_apply'] at this,
    split_ifs at this with h',
    { rwa [with_top.coe_le_coe, ← cardinal.nat_cast_le,
        cardinal.cast_to_nat_of_lt_aleph_0 h'] at this },
    { exact (not_le_of_lt (with_top.coe_lt_top a) this).elim } }
end

@[simp]
lemma submodule.length_bot : (⊥ : submodule R M).length = 0 :=
by rw [submodule.length, set.chain_height_eq_zero_iff, set.Iio_bot]

lemma is_field_iff_ideal [nontrivial R] : is_field R ↔ @set.univ (ideal R) = {⊤, ⊥} :=
begin
  rw [← not_iff_not, ring.not_is_field_iff_exists_ideal_bot_lt_and_lt_top, iff_not_comm,
    set.insert_eq, eq_comm, set.eq_univ_iff_forall],
  push_neg,
  simp [bot_lt_iff_ne_bot, or_iff_not_imp_left],
end


instance {R} [field R] : finite (ideal R) :=
begin
  rw [← set.finite_univ_iff, is_field_iff_ideal.mp (field.to_is_field R)],
  simp
end

instance field.is_artinian_ring {R} [field R] : is_artinian_ring R :=
⟨finite.preorder.well_founded_lt⟩

lemma submodule.length_mono {p q : submodule R M} (h : p ≤ q) : p.length ≤ q.length :=
begin
  apply set.chain_height_le_of_subset,
  exact λ x, h.trans_lt',
end

lemma submodule.length_succ_le_of_lt {p q : submodule R M} (h : p < q) : p.length + 1 ≤ q.length :=
begin
  rw [submodule.length_succ],
  apply set.chain_height_le_of_subset,
  exact λ x, h.trans_le',
end

lemma submodule.length_succ_lt_of_lt {p q : submodule R M} (h : p < q) (h' : p.length ≠ ⊤) :
  p.length < q.length :=
begin
  obtain ⟨a, e⟩ := with_top.ne_top_iff_exists.mp h',
  simp_rw [← e, with_top.coe_lt_iff, ← nat.add_one_le_iff, ← with_top.coe_le_iff, with_top.coe_add,
    e, with_top.coe_one],
  exact submodule.length_succ_le_of_lt h,
end

lemma submodule.eq_of_le_of_length_le {p q : submodule R M}
  (h : p ≤ q) (h' : q.length ≤ p.length) (hp : p.length ≠ ⊤) :
  p = q :=
begin
  by_contra h'',
  apply not_lt_of_le rfl.le,
  exact h'.trans_lt (submodule.length_succ_lt_of_lt (lt_of_le_of_ne h h'') hp)
end

lemma is_noetherian_of_finite_length (h : module.length R M ≠ ⊤) : is_noetherian R M :=
begin
  rw is_noetherian_iff_well_founded,
  apply (@order_iso.set.univ (submodule R M) _).symm.to_order_embedding.dual.well_founded,
  rw ← is_well_founded_iff,
  apply set.well_founded_gt_of_chain_height_ne_top,
  rw [← module.length_succ, with_top.add_ne_top],
  exact ⟨h, with_top.one_ne_top⟩,
end

lemma is_artinian_of_finite_length (h : module.length R M ≠ ⊤) : is_artinian R M :=
begin
  rw is_artinian_iff_well_founded,
  apply (@order_iso.set.univ (submodule R M) _).symm.to_order_embedding.well_founded,
  rw ← is_well_founded_iff,
  apply set.well_founded_lt_of_chain_height_ne_top,
  rw [← module.length_succ, with_top.add_ne_top],
  exact ⟨h, with_top.one_ne_top⟩,
end

lemma module.length_eq_rank
  {R M : Type*} [field R] [add_comm_group M] [module R M] :
  module.length R M = (module.rank R M).to_with_top_nat :=
begin
  by_cases is_artinian R M,
  { resetI,
    rw [module.length, ← dim_top],
    generalize : ⊤ = N,
    apply is_artinian.induction _ N; clear N,
    intros N H,
    rw [← submodule.supr_lt_length_succ N, ← rank_supr_lt_add_one, supr_subtype', csupr_subtype,
      cardinal.supr_to_with_top_nat],
    simp_rw [map_add, cardinal.to_with_top_nat_one],
    congr,
    ext1 ⟨p, hp⟩,
    rw [subtype.coe_mk, H _ hp],
    { use module.rank R M + 1, rintros _ ⟨_, rfl⟩, exact add_le_add (dim_submodule_le _) rfl.le },
    { exact ⟨module.rank R M + 1, λ _ _, add_le_add (dim_submodule_le _) rfl.le⟩ } },
  { have : ¬ is_noetherian R M,
    { introI H, apply h, exact is_artinian_of_fg_of_artinian' module.finite.out },
    rw is_noetherian.iff_dim_lt_aleph_0 at this,
    rw [cardinal.to_with_top_nat_apply', if_neg this],
    revert h,
    rw not_imp_comm,
    exact is_artinian_of_finite_length }
end

lemma module.finite_length_tfae_of_field (R M : Type*) [field R] [add_comm_group M] [module R M] :
  tfae [finite_dimensional R M,
    is_noetherian R M,
    is_artinian R M,
    module.length R M ≠ ⊤] :=
begin
  tfae_have : 1 → 2,
  { rintro ⟨a⟩, exact is_noetherian_of_fg_of_noetherian' a, },
  tfae_have : 1 → 3,
  { rintro ⟨a⟩, exact is_artinian_of_fg_of_artinian' a, },
  tfae_have : 2 → 1,
  { introI _, apply_instance },
  tfae_have : 3 → 2,
  { introI H,
    suffices : ∀ p : submodule R M, module.rank R p < cardinal.aleph_0,
    { rw [is_noetherian.iff_dim_lt_aleph_0, ← dim_top], apply this },
    intro p,
    apply is_artinian.induction _ p; clear p,
    intros p H,
    by_contra h,
    push_neg at h,
    obtain ⟨q, hq, e⟩ := add_one_le_dim_iff_exists_submodule_rank_eq.mp (cardinal.add_one_eq h).le,
    refine not_lt_of_le h _,
    rw [← e, (submodule.equiv_map_of_injective _ p.injective_subtype q).dim_eq],
    apply H,
    convert submodule.map_strict_mono_of_injective p.injective_subtype (lt_top_iff_ne_top.mpr hq),
    exact p.map_subtype_top.symm },
  tfae_have : 2 ↔ 4,
  { rw [is_noetherian.iff_dim_lt_aleph_0, module.length_eq_rank, iff_not_comm, not_lt,
      cardinal.to_with_top_nat_eq_top_iff] },
  tfae_finish
end
