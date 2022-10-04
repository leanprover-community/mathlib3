import order.jordan_holder
import ring_theory.ideal.operations
import linear_algebra.isomorphisms
import ring_theory.artinian
import ring_theory.dimension.length
import order.minimal

section

-- variables

def is_maximal_lt {α : Type*} [preorder α] (x y : α) : Prop :=
x ∈ maximals (≤) (set.Iio y)

lemma is_maximal_lt.lt {α : Type*} [preorder α] {x y : α} (h : is_maximal_lt x y) : x < y :=
h.1

lemma is_maximal_lt.le {α : Type*} [preorder α] {x y : α} (h : is_maximal_lt x y) : x ≤ y :=
h.lt.le

lemma is_maximal_lt_iff_Ioo {α : Type*} [preorder α] {x y : α} :
  is_maximal_lt x y ↔ x < y ∧ set.Ioo x y = ∅ :=
begin
  apply and_congr iff.rfl,
  split,
  { rw set.eq_empty_iff_forall_not_mem, rintros H z ⟨h₁, h₂⟩, exact not_le_of_lt h₁ (H h₂ h₁.le) },
  { intros H b h₁ h₂, by_contra h,
    show b ∈ (∅ : set α), rw ← H, exact ⟨lt_iff_le_not_le.mpr ⟨h₂, h⟩, h₁⟩ },
end

lemma sup_eq_of_is_maximal_lt {α : Type*} [semilattice_sup α] {x y z : α}
  (h₁ : x ≤ z) (h₂ : is_maximal_lt y z) (e : ¬ x ≤ y) : x ⊔ y = z :=
eq_of_le_of_not_lt (sup_le h₁ h₂.le) (λ e', e (le_sup_left.trans (h₂.2 e' le_sup_right)))

lemma sup_eq_of_is_maximal_lt_of_is_maximal_lt {α : Type*} [semilattice_sup α] {x y z : α}
  (h₁ : is_maximal_lt x z) (h₂ : is_maximal_lt y z) (e : x ≠ y) : x ⊔ y = z :=
begin
  apply eq_of_le_of_not_lt (sup_le h₁.le h₂.le),
  intro e',
  apply e (eq_of_mem_maximals h₂ h₁.lt _).symm,
  rw [← sup_eq_left, ← le_sup_left.antisymm (h₁.2 e' le_sup_left)],
end


-- namespace is_modular_lattice

-- variables {α : Type*} [lattice α] [is_modular_lattice α]

-- def is_modular_lattice.inf_Ioo_order_iso_Ioo_sup (a b : α) :
--   set.Icc (a ⊓ b) a ≃o set.Icc b (a ⊔ b) := sorry

-- end is_modular_lattice

lemma is_maximal_lt_inf_left_of_is_maximal_lt_sup {α : Type*} [lattice α] [is_modular_lattice α]
  {x y : α} (h : is_maximal_lt y (x ⊔ y)) : is_maximal_lt (x ⊓ y) x :=
begin
  refine ⟨lt_of_le_of_ne inf_le_left _, _⟩,
  { rw [ne.def, inf_eq_left, ← sup_eq_right], exact h.lt.ne.symm },
  { rintros z (h₃ : z < x) h₄,
    refine le_inf h₃.le _,
    suffices : y ⊔ z ≤ y, { exact le_sup_right.trans this },
    apply h.2 (lt_of_le_of_ne _ _) le_sup_left,
    { exact sup_comm.trans_le (sup_le_sup_right h₃.le y) },
    { intro e,
      have : (y ⊔ z) ⊓ x = (x ⊔ y) ⊓ x := congr_arg (⊓ x) e,
      rw [sup_inf_assoc_of_le _ (le_refl x), sup_comm, sup_inf_assoc_of_le _ h₃.le,
        inf_comm, sup_inf_self, sup_eq_left.mpr h₄] at this,
      exact h₃.ne this } }
end

lemma is_maximal_lt_inf_left_of_is_maximal_lt_sup' {α : Type*} [lattice α] [is_modular_lattice α]
  {x y : α} (h : is_maximal_lt x (x ⊔ y)) : is_maximal_lt (x ⊓ y) y :=
begin
  rw inf_comm, apply is_maximal_lt_inf_left_of_is_maximal_lt_sup, rwa sup_comm
end

lemma le_or_is_maximal_of_is_maximal {α : Type*} [lattice α] [is_modular_lattice α]
  {x y z : α} (h₁ : is_maximal_lt x z) (h₂ : y ≤ z) : y ≤ x ∨ is_maximal_lt (x ⊓ y) y :=
begin
  rw or_iff_not_imp_left,
  intro h₃,
  apply is_maximal_lt_inf_left_of_is_maximal_lt_sup',
  convert h₁,
  rw sup_comm,
  apply sup_eq_of_is_maximal_lt h₂ h₁ h₃
end

section

variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]

instance : jordan_holder_lattice (submodule R M) :=
{ is_maximal := is_maximal_lt,
  lt_of_is_maximal := λ _ _ h, h.1,
  sup_eq_of_is_maximal := λ _ _ _, sup_eq_of_is_maximal_lt_of_is_maximal_lt,
  is_maximal_inf_left_of_is_maximal_sup := λ _ _ _, is_maximal_lt_inf_left_of_is_maximal_lt_sup,
  iso := λ p₁ p₂, nonempty ((p₁.2 ⧸ p₁.1.comap p₁.2.subtype) ≃ₗ[R] p₂.2 ⧸ p₂.1.comap p₂.2.subtype),
  iso_symm := λ x y e, ⟨e.some.symm⟩,
  iso_trans := λ x y z e₁ e₂, ⟨e₁.some.trans e₂.some⟩,
  second_iso := begin
    rintros x y _,
    rw [sup_comm, inf_comm],
    exact ⟨(linear_map.quotient_inf_equiv_sup_quotient y x).symm⟩
  end }
.

lemma submodule.exists_is_maximal_ge_of_le [h : is_noetherian R M] {p q : submodule R M}
  (e : q < p) :
  ∃ q' ≥ q, is_maximal_lt q' p :=
begin
  rw [is_noetherian_iff_well_founded, well_founded.well_founded_iff_has_max'] at h,
  obtain ⟨q', h₁, h₂⟩ := h (set.Ico q p) ⟨q, rfl.le, e⟩,
  exact ⟨q', h₁.1, h₁.2, λ x hx hx', (h₂ x ⟨h₁.1.trans hx', hx⟩ hx').le⟩
end

lemma submodule.exists_composition_series [is_noetherian R M] [h : is_artinian R M]
  {N N' : submodule R M} (e : N ≤ N') :
  ∃ s : composition_series (submodule R M), s.bot = N ∧ s.top = N' :=
begin
  rw is_artinian_iff_well_founded at h,
  revert e,
  apply well_founded.induction h N',
  clear N',
  intros N' H e,
  rcases eq_or_lt_of_le e with (rfl | e),
  { exact ⟨⟨0, ![N], λ e, fin_zero_elim e⟩, rfl, rfl⟩ },
  obtain ⟨N'', e', hN⟩ := submodule.exists_is_maximal_ge_of_le e,
  obtain ⟨s, h₁, h₂⟩ := H N'' hN.1 e',
  exact ⟨s.snoc N' (h₂.symm ▸ hN), h₁, composition_series.top_snoc _ _ _⟩
end

open composition_series

lemma exists_composition_series_length_lt
  (s : composition_series (submodule R M)) (x : submodule R M) (h₁ : s.bot ≤ x) (h₂ : x < s.top) :
  ∃ t : composition_series _, t.bot = s.bot ∧ t.top = x ∧ t.length < s.length :=
begin
  induction hle : s.length with n ih generalizing s x,
  { have h := forall_mem_eq_of_length_eq_zero hle s.bot_mem s.top_mem,
    exact (not_le_of_lt h₂ (h ▸ h₁)).elim },
  have htop := is_maximal_erase_top_top ((nat.zero_lt_succ _).trans_eq hle.symm),
  have hle' : s.erase_top.length = n := s.erase_top_length.trans (by rw [hle, nat.succ_sub_one]),
  cases le_or_is_maximal_of_is_maximal htop h₂.le,
  cases lt_or_eq_of_le h with h h,
  { obtain ⟨t, e₁, e₂, e₃⟩ := ih s.erase_top x h₁ h hle',
    exact ⟨t, e₁, e₂, e₃.trans (lt_add_one _)⟩ },
  { subst h, exact ⟨s.erase_top, rfl, rfl, hle'.trans_lt (lt_add_one _)⟩ },
  { have : ¬ s.erase_top.top ≤ x,
    { intro e,
      rw [← (htop.2 h₂ e).antisymm e, inf_idem] at h,
      exact @irrefl _ (<) _ x h.lt },
    rw [← inf_eq_right] at this,
    obtain ⟨t, e₁, e₂, e₃⟩ := ih s.erase_top (x ⊓ s.erase_top.top)
      (le_inf h₁ (bot_le_of_mem $ top_mem _)) (lt_of_le_of_ne inf_le_right this) hle',
    exact ⟨t.snoc x (by rwa [e₂, inf_comm]), e₁, t.top_snoc _ _, nat.add_lt_add_right e₃ 1⟩ }
end

lemma with_top.add_coe_right_injective
  {α : Type*} [add_cancel_monoid α] {a b : with_top α} (c : α) (h : a + c = b + c) : a = b :=
begin
  cases a; cases b; simp only [with_top.none_eq_top, with_top.some_eq_coe] at h ⊢,
  { simpa [← with_top.coe_add] using h },
  { simpa [← with_top.coe_add] using h },
  { rw [← with_top.coe_add, ← with_top.coe_add] at h,
    injection h with h', rw add_right_cancel h' }
end

lemma length_lt_composition_series_length (s : composition_series (submodule R M))
  (l : list (submodule R M)) (hbot : ∀ x ∈ l, s.bot ≤ x)
  (htop : l.head ≤ s.top) (hl' : l.chain' (>)) : l.length ≤ s.length + 1 :=
begin
  induction l with x l h generalizing s,
  { exact zero_le _ },
  { cases l with y l, { exact add_le_add (zero_le _) (le_refl 1) },
    obtain ⟨s', e₁, e₂, e₃⟩ := exists_composition_series_length_lt s y (hbot _ $ by simp)
      (lt_of_lt_of_le (list.chain'_cons.mp hl').1 htop),
    have := h (list.chain'_cons.mp hl').2 s' (λ z hz, e₁.symm ▸ hbot z (or.inr hz)) e₂.symm.le,
    apply add_le_add_right,
    exact this.trans (nat.lt_iff_add_one_le.mp e₃) }
end

lemma composition_series_length_succ_eq_chain_height (s : composition_series (submodule R M)) :
  ↑s.length + 1 = (set.Icc s.bot s.top).chain_height :=
begin
  apply le_antisymm,
  { apply set.le_chain_height_iff.mpr,
    refine ⟨s.to_list, ⟨_, _⟩, s.length_to_list⟩,
    { rw list.chain'_iff_pairwise, exact s.to_list_sorted },
    { intros i hi, rw mem_to_list at hi, exact ⟨bot_le_of_mem hi, le_top_of_mem hi⟩ } },
  { refine supr₂_le _,
    intros l hl,
    by_cases l = [], { subst h, exact zero_le _ },
    norm_cast,
    have := length_lt_composition_series_length s l.reverse _ _ _,
    { rwa [list.length_reverse] at this },
    { intros x hx, rw list.mem_reverse at hx, exact (hl.2 x hx).1 },
    { exact (hl.2 _ (list.mem_reverse.mp $ list.head_mem_self (list.reverse_eq_nil.not.mpr h))).2 },
    { rw list.chain'_reverse, exact hl.1 } }
end

lemma composition_series_length_eq_length (s : composition_series (submodule R M))
  (hbot : s.bot = ⊥) (htop : s.top = ⊤) :
  ↑s.length = module.length R M :=
begin
  apply with_top.add_coe_right_injective 1,
  rw [with_top.coe_one, composition_series_length_succ_eq_chain_height s, module.length_succ,
    htop, hbot, set.Icc_bot, set.Iic_top],
end

lemma finite_length_tfae :
  tfae [module.length R M ≠ ⊤,
    is_noetherian R M ∧ is_artinian R M,
    ∃ s : composition_series (submodule R M), s.bot = ⊥ ∧ s.top = ⊤] :=
begin
  tfae_have : 1 → 2,
  { exact λ h, ⟨is_noetherian_of_finite_length h, is_artinian_of_finite_length h⟩ },
  tfae_have : 2 → 3,
  { rintros ⟨h₁, h₂⟩, exactI submodule.exists_composition_series bot_le },
  tfae_have : 3 → 1,
  { rintro ⟨s, h, h'⟩, rw ← composition_series_length_eq_length s h h', exact with_top.coe_ne_top },
  tfae_finish
end

end

end
