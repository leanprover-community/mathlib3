/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import order.rel_iso
import order.lattice_intervals
import order.galois_connection

/-!
# Modular Lattices
This file defines Modular Lattices, a kind of lattice useful in algebra.
For examples, look to the subobject lattices of abelian groups, submodules, and ideals, or consider
any distributive lattice.

## Main Definitions
- `is_modular_lattice` defines a modular lattice to be one such that
  `x ≤ z → (x ⊔ y) ⊓ z ≤ x ⊔ (y ⊓ z)`
- `inf_Icc_order_iso_Icc_sup` gives an order isomorphism between the intervals
  `[a ⊓ b, a]` and `[b, a ⊔ b]`.
  This corresponds to the diamond (or second) isomorphism theorems of algebra.

## Main Results
- `is_modular_lattice_iff_inf_sup_inf_assoc`:
  Modularity is equivalent to the `inf_sup_inf_assoc`: `(x ⊓ z) ⊔ (y ⊓ z) = ((x ⊓ z) ⊔ y) ⊓ z`
- `distrib_lattice.is_modular_lattice`: Distributive lattices are modular.

## To do
- Relate atoms and coatoms in modular lattices

-/

variable {α : Type*}

/-- A modular lattice is one with a limited associativity between `⊓` and `⊔`. -/
class is_modular_lattice α [lattice α] : Prop :=
(sup_inf_le_assoc_of_le : ∀ {x : α} (y : α) {z : α}, x ≤ z → (x ⊔ y) ⊓ z ≤ x ⊔ (y ⊓ z))

section is_modular_lattice
variables [lattice α] [is_modular_lattice α]

theorem sup_inf_assoc_of_le {x : α} (y : α) {z : α} (h : x ≤ z) :
  (x ⊔ y) ⊓ z = x ⊔ (y ⊓ z) :=
le_antisymm (is_modular_lattice.sup_inf_le_assoc_of_le y h)
  (le_inf (sup_le_sup_left inf_le_left _) (sup_le h inf_le_right))

theorem is_modular_lattice.inf_sup_inf_assoc {x y z : α} :
  (x ⊓ z) ⊔ (y ⊓ z) = ((x ⊓ z) ⊔ y) ⊓ z :=
(sup_inf_assoc_of_le y inf_le_right).symm

lemma inf_sup_assoc_of_le {x : α} (y : α) {z : α} (h : z ≤ x) :
  (x ⊓ y) ⊔ z = x ⊓ (y ⊔ z) :=
by rw [inf_comm, sup_comm, ← sup_inf_assoc_of_le y h, inf_comm, sup_comm]

instance : is_modular_lattice (order_dual α) :=
⟨λ x y z xz, le_of_eq (by { rw [inf_comm, sup_comm, eq_comm, inf_comm, sup_comm],
  convert sup_inf_assoc_of_le (order_dual.of_dual y) (order_dual.dual_le.2 xz) })⟩

variables {x y z : α}

theorem is_modular_lattice.sup_inf_sup_assoc :
  (x ⊔ z) ⊓ (y ⊔ z) = ((x ⊔ z) ⊓ y) ⊔ z :=
@is_modular_lattice.inf_sup_inf_assoc (order_dual α) _ _ _ _ _

theorem eq_of_le_of_inf_le_of_sup_le (hxy : x ≤ y) (hinf : y ⊓ z ≤ x ⊓ z) (hsup : y ⊔ z ≤ x ⊔ z) :
  x = y :=
le_antisymm hxy $
  have h : y ≤ x ⊔ z,
    from calc y ≤ y ⊔ z : le_sup_left
      ... ≤ x ⊔ z : hsup,
  calc y ≤ (x ⊔ z) ⊓ y : le_inf h (le_refl _)
    ... = x ⊔ (z ⊓ y) : sup_inf_assoc_of_le _ hxy
    ... ≤ x ⊔ (z ⊓ x) : sup_le_sup_left
      (by rw [inf_comm, @inf_comm _ _ z]; exact hinf) _
    ... ≤ x : sup_le (le_refl _) inf_le_right

theorem sup_lt_sup_of_lt_of_inf_le_inf (hxy : x < y) (hinf : y ⊓ z ≤ x ⊓ z) : x ⊔ z < y ⊔ z :=
lt_of_le_of_ne
  (sup_le_sup_right (le_of_lt hxy) _)
  (λ hsup, ne_of_lt hxy $ eq_of_le_of_inf_le_of_sup_le (le_of_lt hxy) hinf
    (le_of_eq hsup.symm))

theorem inf_lt_inf_of_lt_of_sup_le_sup (hxy : x < y) (hinf : y ⊔ z ≤ x ⊔ z) : x ⊓ z < y ⊓ z :=
@sup_lt_sup_of_lt_of_inf_le_inf (order_dual α) _ _ _ _ _ hxy hinf

/-- A generalization of the theorem that if `N` is a submodule of `M` and
  `N` and `M / N` are both Artinian, then `M` is Artinian. -/
theorem well_founded_lt_exact_sequence
  {β γ : Type*} [partial_order β] [partial_order γ]
  (h₁ : well_founded ((<) : β → β → Prop))
  (h₂ : well_founded ((<) : γ → γ → Prop))
  (K : α) (f₁ : β → α) (f₂ : α → β) (g₁ : γ → α) (g₂ : α → γ)
  (gci : galois_coinsertion f₁ f₂)
  (gi : galois_insertion g₂ g₁)
  (hf : ∀ a, f₁ (f₂ a) = a ⊓ K)
  (hg : ∀ a, g₁ (g₂ a) = a ⊔ K) :
  well_founded ((<) : α → α → Prop) :=
subrelation.wf
  (λ A B hAB, show prod.lex (<) (<) (f₂ A, g₂ A) (f₂ B, g₂ B),
    begin
      simp only [prod.lex_def, lt_iff_le_not_le, ← gci.l_le_l_iff,
        ← gi.u_le_u_iff, hf, hg, le_antisymm_iff],
      simp only [gci.l_le_l_iff, gi.u_le_u_iff, ← lt_iff_le_not_le, ← le_antisymm_iff],
      cases lt_or_eq_of_le (inf_le_inf_right K (le_of_lt hAB)) with h h,
      { exact or.inl h },
      { exact or.inr ⟨h, sup_lt_sup_of_lt_of_inf_le_inf hAB (le_of_eq h.symm)⟩ }
    end)
  (inv_image.wf _ (prod.lex_wf h₁ h₂))

/-- A generalization of the theorem that if `N` is a submodule of `M` and
  `N` and `M / N` are both Noetherian, then `M` is Noetherian.  -/
theorem well_founded_gt_exact_sequence
  {β γ : Type*} [partial_order β] [partial_order γ]
  (h₁ : well_founded ((>) : β → β → Prop))
  (h₂ : well_founded ((>) : γ → γ → Prop))
  (K : α) (f₁ : β → α) (f₂ : α → β) (g₁ : γ → α) (g₂ : α → γ)
  (gci : galois_coinsertion f₁ f₂)
  (gi : galois_insertion g₂ g₁)
  (hf : ∀ a, f₁ (f₂ a) = a ⊓ K)
  (hg : ∀ a, g₁ (g₂ a) = a ⊔ K) :
  well_founded ((>) : α → α → Prop) :=
@well_founded_lt_exact_sequence
  (order_dual α) _ _ (order_dual γ) (order_dual β) _ _
  h₂ h₁ K g₁ g₂ f₁ f₂ gi.dual gci.dual hg hf

/-- The diamond isomorphism between the intervals `[a ⊓ b, a]` and `[b, a ⊔ b]` -/
def inf_Icc_order_iso_Icc_sup (a b : α) : set.Icc (a ⊓ b) a ≃o set.Icc b (a ⊔ b) :=
{ to_fun := λ x, ⟨x ⊔ b, ⟨le_sup_right, sup_le_sup_right x.prop.2 b⟩⟩,
  inv_fun := λ x, ⟨a ⊓ x, ⟨inf_le_inf_left a x.prop.1, inf_le_left⟩⟩,
  left_inv := λ x, subtype.ext (by { change a ⊓ (↑x ⊔ b) = ↑x,
    rw [sup_comm, ← inf_sup_assoc_of_le _ x.prop.2, sup_eq_right.2 x.prop.1] }),
  right_inv := λ x, subtype.ext (by { change a ⊓ ↑x ⊔ b = ↑x,
    rw [inf_comm, inf_sup_assoc_of_le _ x.prop.1, inf_eq_left.2 x.prop.2] }),
  map_rel_iff' := λ x y, begin
    simp only [subtype.mk_le_mk, equiv.coe_fn_mk, and_true, le_sup_right],
    rw [← subtype.coe_le_coe],
    refine ⟨λ h, _, λ h, sup_le_sup_right h _⟩,
    rw [← sup_eq_right.2 x.prop.1, inf_sup_assoc_of_le _ x.prop.2, sup_comm,
      ← sup_eq_right.2 y.prop.1, inf_sup_assoc_of_le _ y.prop.2, @sup_comm _ _ b],
    exact inf_le_inf_left _ h
  end }
end is_modular_lattice

namespace is_compl
variables [bounded_lattice α] [is_modular_lattice α]

/-- The diamond isomorphism between the intervals `set.Iic a` and `set.Ici b`. -/
def Iic_order_iso_Ici {a b : α} (h : is_compl a b) : set.Iic a ≃o set.Ici b :=
(order_iso.set_congr (set.Iic a) (set.Icc (a ⊓ b) a) (h.inf_eq_bot.symm ▸ set.Icc_bot.symm)).trans $
  (inf_Icc_order_iso_Icc_sup a b).trans
  (order_iso.set_congr (set.Icc b (a ⊔ b)) (set.Ici b) (h.sup_eq_top.symm ▸ set.Icc_top))

end is_compl

theorem is_modular_lattice_iff_inf_sup_inf_assoc [lattice α] :
  is_modular_lattice α ↔ ∀ (x y z : α), (x ⊓ z) ⊔ (y ⊓ z) = ((x ⊓ z) ⊔ y) ⊓ z :=
⟨λ h, @is_modular_lattice.inf_sup_inf_assoc _ _ h, λ h, ⟨λ x y z xz, by rw [← inf_eq_left.2 xz, h]⟩⟩

namespace distrib_lattice

@[priority 100]
instance [distrib_lattice α] : is_modular_lattice α :=
⟨λ x y z xz, by rw [inf_sup_right, inf_eq_left.2 xz]⟩

end distrib_lattice

theorem disjoint.disjoint_sup_right_of_disjoint_sup_left
  [bounded_lattice α] [is_modular_lattice α] {a b c : α}
  (h : disjoint a b) (hsup : disjoint (a ⊔ b) c) :
  disjoint a (b ⊔ c) :=
begin
  rw [disjoint, ← h.eq_bot, sup_comm],
  apply le_inf inf_le_left,
  apply (inf_le_inf_right (c ⊔ b) le_sup_right).trans,
  rw [sup_comm, is_modular_lattice.sup_inf_sup_assoc, hsup.eq_bot, bot_sup_eq]
end

theorem disjoint.disjoint_sup_left_of_disjoint_sup_right
  [bounded_lattice α] [is_modular_lattice α] {a b c : α}
  (h : disjoint b c) (hsup : disjoint a (b ⊔ c)) :
  disjoint (a ⊔ b) c :=
begin
  rw [disjoint.comm, sup_comm],
  apply disjoint.disjoint_sup_right_of_disjoint_sup_left h.symm,
  rwa [sup_comm, disjoint.comm] at hsup,
end

namespace is_modular_lattice

variables [bounded_lattice α] [is_modular_lattice α] {a : α}

instance is_modular_lattice_Iic : is_modular_lattice (set.Iic a) :=
⟨λ x y z xz, (sup_inf_le_assoc_of_le (y : α) xz : (↑x ⊔ ↑y) ⊓ ↑z ≤ ↑x ⊔ ↑y ⊓ ↑z)⟩

instance is_modular_lattice_Ici : is_modular_lattice (set.Ici a) :=
⟨λ x y z xz, (sup_inf_le_assoc_of_le (y : α) xz : (↑x ⊔ ↑y) ⊓ ↑z ≤ ↑x ⊔ ↑y ⊓ ↑z)⟩

section is_complemented
variables [is_complemented α]

instance is_complemented_Iic : is_complemented (set.Iic a) :=
⟨λ ⟨x, hx⟩, let ⟨y, hy⟩ := exists_is_compl x in
  ⟨⟨y ⊓ a, set.mem_Iic.2 inf_le_right⟩, begin
    split,
    { change x ⊓ (y ⊓ a) ≤ ⊥, -- improve lattice subtype API
      rw ← inf_assoc,
      exact le_trans inf_le_left hy.1 },
    { change a ≤ x ⊔ (y ⊓ a), -- improve lattice subtype API
      rw [← sup_inf_assoc_of_le _ (set.mem_Iic.1 hx), top_le_iff.1 hy.2, top_inf_eq] }
  end⟩⟩

instance is_complemented_Ici : is_complemented (set.Ici a) :=
⟨λ ⟨x, hx⟩, let ⟨y, hy⟩ := exists_is_compl x in
  ⟨⟨y ⊔ a, set.mem_Ici.2 le_sup_right⟩, begin
    split,
    { change x ⊓ (y ⊔ a) ≤ a, -- improve lattice subtype API
      rw [← inf_sup_assoc_of_le _ (set.mem_Ici.1 hx),  le_bot_iff.1 hy.1, bot_sup_eq] },
    { change ⊤ ≤ x ⊔ (y ⊔ a), -- improve lattice subtype API
      rw ← sup_assoc,
      exact le_trans hy.2 le_sup_left }
  end⟩⟩

end is_complemented

end is_modular_lattice
