import order.atoms
import order.bounded_order
import order.jordan_holder

open order
variables {α : Type*} [lattice α] [bounded_order α] [well_founded_lt α] [complemented_lattice α]

open_locale classical

instance is_atomic_of_well_founded_lt {α : Type*} [partial_order α] [order_bot α]
  [wf : well_founded_lt α] : is_atomic α :=
is_atomic_of_order_bot_well_founded_lt (@is_well_founded.wf _ _ wf)

lemma exists_atom_le (a : α) (h : a ≠ ⊥) : ∃ b, is_atom b ∧ b ≤ a :=
(or_iff_right h).mp (eq_bot_or_exists_atom_le a)

/-lemma exists_gt (a : α) (h : a ≠ ⊤) : ∃ b, b > a :=
begin
  by_contra h', apply h, push_neg at h',
  specialize h' ⊤,
  simp at h',
  exact h'
end-/

theorem complemented_Iic_of_complemented_and_modular {α : Type*} [lattice α] [bounded_order α]
  [complemented_lattice α] [is_modular_lattice α] (a : α) : complemented_lattice (set.Iic a) :=
⟨λ b, by
{ cases complemented_lattice.exists_is_compl (b : α) with c hc,
  use ⟨c ⊓ a, inf_le_right⟩,
  refine ⟨disjoint_iff.mpr (subtype.eq _), codisjoint_iff.mpr (subtype.eq _)⟩,
  simp only [set.Iic.coe_bot, subtype.coe_inf, subtype.coe_mk, subtype.val_eq_coe],
  rw [←inf_assoc, disjoint_iff.mp hc.disjoint, bot_inf_eq],
  simp only [set.Iic.coe_top, subtype.coe_sup, subtype.coe_mk, subtype.val_eq_coe],
  rw [←sup_inf_assoc_of_le _ b.prop, codisjoint_iff.mp hc.codisjoint, top_inf_eq], }⟩

lemma exists_complement {α : Type*} [lattice α] [bounded_order α] [complemented_lattice α]
  [is_modular_lattice α] {a c : α} (h : a ≤ c) : ∃ b : α, a ⊓ b = ⊥ ∧ a ⊔ b = c :=
begin
  haveI := complemented_Iic_of_complemented_and_modular c,
  cases complemented_lattice.exists_is_compl (⟨a,h⟩ : set.Iic c) with b hb,
  use ↑b,
  split,
    have := disjoint_iff.mp hb.disjoint,
    rw [←subtype.coe_inj, subtype.coe_inf] at this,
    exact this,
  have := codisjoint_iff.mp hb.codisjoint,
  rw [←subtype.coe_inj, subtype.coe_sup] at this,
  exact this,
end

lemma exists_basis [is_modular_lattice α] (a : α) : ∃ s : finset α, (∀ b ∈ s, is_atom b) ∧ s.sup id = a :=
begin
  let C := λ a, ∃ (s : finset α), (∀ (b : α), b ∈ s → is_atom b) ∧ s.sup id = a,
  exact @well_founded.induction α (<) (@is_well_founded.wf α (<) _) C a (λ a ha, by
  { by_cases h' : a = ⊥,
    refine ⟨∅, ⟨λ b hb, false.rec _ hb, by rw [finset.sup_empty, h']⟩⟩,
    have hc := classical.some_spec (exists_atom_le a h'),
    have hd := classical.some_spec (exists_complement hc.2),
    have hda : classical.some (exists_complement hc.2) < a,
      refine lt_of_le_of_ne _ (λ hda, (is_atom_iff.mp (hc.1)).1 _),
        convert le_sup_right,
        exact hd.2.symm,
      rw [hda, sup_eq_right, ←inf_eq_left] at hd,
      rw [←hd.1, hd.2],
    cases ha _ hda with s hs,
    refine ⟨insert (classical.some (exists_atom_le a h')) s, ⟨λ b hb, _, _⟩⟩,
      rw [finset.insert_eq, finset.mem_union, finset.mem_singleton] at hb,
      exact hb.by_cases (λ hb, hb.symm ▸ hc.1) (λ hb, hs.1 b hb),
    rw [finset.sup_insert, hs.2, id.def, hd.2]}),
end

lemma unique_basis [jordan_holder_lattice α] (a : α)
  (s₁ : finset α) (h₁ : ∀ b ∈ s₁, jordan_holder_lattice.is_maximal ⊥ b ∧ s₁.sup id = a)
  (s₂ : finset α) (h₂ : ∀ b ∈ s₂, jordan_holder_lattice.is_maximal ⊥ b ∧ s₂.sup id = a) :
  ∃ e : s₁ ≃ s₂, ∀ b : s₁, jordan_holder_lattice.iso ⟨(⊥ : α), ↑b⟩ ⟨⊥, e b⟩ :=
begin
  sorry,
end

--instance temp : @well_founded α (<) :=

/-| x y :=
  if h : 0 < y ∧ y ≤ x then
    have x - y < x,
      from sub_lt (lt_of_lt_of_le h.left h.right) h.left,
    div (x - y) y + 1
  else
    0-/
