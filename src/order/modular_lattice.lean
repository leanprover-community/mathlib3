/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Yaël Dillies
-/
import order.cover
import order.lattice_intervals

/-!
# Modular Lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines (semi)modular lattices, a kind of lattice useful in algebra.
For examples, look to the subobject lattices of abelian groups, submodules, and ideals, or consider
any distributive lattice.

## Typeclasses

We define (semi)modularity typeclasses as Prop-valued mixins.

* `is_weak_upper_modular_lattice`: Weakly upper modular lattices. Lattice where `a ⊔ b` covers `a`
  and `b` if `a` and `b` both cover `a ⊓ b`.
* `is_weak_lower_modular_lattice`: Weakly lower modular lattices. Lattice where `a` and `b` cover
  `a ⊓ b` if `a ⊔ b` covers both `a` and `b`
* `is_upper_modular_lattice`: Upper modular lattices. Lattices where `a ⊔ b` covers `a` if `b`
  covers `a ⊓ b`.
* `is_lower_modular_lattice`: Lower modular lattices. Lattices where `a` covers `a ⊓ b` if `a ⊔ b`
  covers `b`.
- `is_modular_lattice`: Modular lattices. Lattices where `a ≤ c → (a ⊔ b) ⊓ c = a ⊔ (b ⊓ c)`. We
  only require an inequality because the other direction holds in all lattices.

## Main Definitions

- `inf_Icc_order_iso_Icc_sup` gives an order isomorphism between the intervals
  `[a ⊓ b, a]` and `[b, a ⊔ b]`.
  This corresponds to the diamond (or second) isomorphism theorems of algebra.

## Main Results

- `is_modular_lattice_iff_inf_sup_inf_assoc`:
  Modularity is equivalent to the `inf_sup_inf_assoc`: `(x ⊓ z) ⊔ (y ⊓ z) = ((x ⊓ z) ⊔ y) ⊓ z`
- `distrib_lattice.is_modular_lattice`: Distributive lattices are modular.

## References

* [Manfred Stern, *Semimodular lattices. {Theory} and applications*][stern2009]
* [Wikipedia, *Modular Lattice*][https://en.wikipedia.org/wiki/Modular_lattice]

## TODO

- Relate atoms and coatoms in modular lattices
-/

open set

variable {α : Type*}

/-- A weakly upper modular lattice is a lattice where `a ⊔ b` covers `a` and `b` if `a` and `b` both
cover `a ⊓ b`. -/
class is_weak_upper_modular_lattice (α : Type*) [lattice α] : Prop :=
(covby_sup_of_inf_covby_covby {a b : α} : a ⊓ b ⋖ a → a ⊓ b ⋖ b → a ⋖ a ⊔ b)

/-- A weakly lower modular lattice is a lattice where `a` and `b` cover `a ⊓ b` if `a ⊔ b` covers
both `a` and `b`. -/
class is_weak_lower_modular_lattice (α : Type*) [lattice α] : Prop :=
(inf_covby_of_covby_covby_sup {a b : α} : a ⋖ a ⊔ b → b ⋖ a ⊔ b → a ⊓ b ⋖ a)

/-- An upper modular lattice, aka semimodular lattice, is a lattice where `a ⊔ b` covers `a` and `b`
if either `a` or `b` covers `a ⊓ b`. -/
class is_upper_modular_lattice (α : Type*) [lattice α] : Prop :=
(covby_sup_of_inf_covby {a b : α} : a ⊓ b ⋖ a → b ⋖ a ⊔ b)

/-- A lower modular lattice is a lattice where `a` and `b` both cover `a ⊓ b` if `a ⊔ b` covers
either `a` or `b`. -/
class is_lower_modular_lattice (α : Type*) [lattice α] : Prop :=
(inf_covby_of_covby_sup {a b : α} : a ⋖ a ⊔ b → a ⊓ b ⋖ b)

/-- A modular lattice is one with a limited associativity between `⊓` and `⊔`. -/
class is_modular_lattice (α : Type*) [lattice α] : Prop :=
(sup_inf_le_assoc_of_le : ∀ {x : α} (y : α) {z : α}, x ≤ z → (x ⊔ y) ⊓ z ≤ x ⊔ (y ⊓ z))

section weak_upper_modular
variables [lattice α] [is_weak_upper_modular_lattice α] {a b : α}

lemma covby_sup_of_inf_covby_of_inf_covby_left : a ⊓ b ⋖ a → a ⊓ b ⋖ b → a ⋖ a ⊔ b :=
is_weak_upper_modular_lattice.covby_sup_of_inf_covby_covby

lemma covby_sup_of_inf_covby_of_inf_covby_right : a ⊓ b ⋖ a → a ⊓ b ⋖ b → b ⋖ a ⊔ b :=
by { rw [inf_comm, sup_comm], exact λ ha hb, covby_sup_of_inf_covby_of_inf_covby_left hb ha }

alias covby_sup_of_inf_covby_of_inf_covby_left ← covby.sup_of_inf_of_inf_left
alias covby_sup_of_inf_covby_of_inf_covby_right ← covby.sup_of_inf_of_inf_right

instance : is_weak_lower_modular_lattice (order_dual α) :=
⟨λ a b ha hb, (ha.of_dual.sup_of_inf_of_inf_left hb.of_dual).to_dual⟩

end weak_upper_modular

section weak_lower_modular
variables [lattice α] [is_weak_lower_modular_lattice α] {a b : α}

lemma inf_covby_of_covby_sup_of_covby_sup_left : a ⋖ a ⊔ b → b ⋖ a ⊔ b → a ⊓ b ⋖ a :=
is_weak_lower_modular_lattice.inf_covby_of_covby_covby_sup

lemma inf_covby_of_covby_sup_of_covby_sup_right : a ⋖ a ⊔ b → b ⋖ a ⊔ b → a ⊓ b ⋖ b :=
by { rw [sup_comm, inf_comm], exact λ ha hb, inf_covby_of_covby_sup_of_covby_sup_left hb ha }

alias inf_covby_of_covby_sup_of_covby_sup_left ← covby.inf_of_sup_of_sup_left
alias inf_covby_of_covby_sup_of_covby_sup_right ← covby.inf_of_sup_of_sup_right

instance : is_weak_upper_modular_lattice (order_dual α) :=
⟨λ a b ha hb, (ha.of_dual.inf_of_sup_of_sup_left hb.of_dual).to_dual⟩

end weak_lower_modular

section upper_modular
variables [lattice α] [is_upper_modular_lattice α] {a b : α}

lemma covby_sup_of_inf_covby_left : a ⊓ b ⋖ a → b ⋖ a ⊔ b :=
is_upper_modular_lattice.covby_sup_of_inf_covby

lemma covby_sup_of_inf_covby_right : a ⊓ b ⋖ b → a ⋖ a ⊔ b :=
by { rw [sup_comm, inf_comm], exact covby_sup_of_inf_covby_left }

alias covby_sup_of_inf_covby_left ← covby.sup_of_inf_left
alias covby_sup_of_inf_covby_right ← covby.sup_of_inf_right

@[priority 100] -- See note [lower instance priority]
instance is_upper_modular_lattice.to_is_weak_upper_modular_lattice :
  is_weak_upper_modular_lattice α :=
⟨λ a b _, covby.sup_of_inf_right⟩

instance : is_lower_modular_lattice (order_dual α) := ⟨λ a b h, h.of_dual.sup_of_inf_left.to_dual⟩

end upper_modular

section lower_modular
variables [lattice α] [is_lower_modular_lattice α] {a b : α}

lemma inf_covby_of_covby_sup_left : a ⋖ a ⊔ b → a ⊓ b ⋖ b :=
is_lower_modular_lattice.inf_covby_of_covby_sup

lemma inf_covby_of_covby_sup_right : b ⋖ a ⊔ b → a ⊓ b ⋖ a :=
by { rw [inf_comm, sup_comm], exact inf_covby_of_covby_sup_left }

alias inf_covby_of_covby_sup_left ← covby.inf_of_sup_left
alias inf_covby_of_covby_sup_right ← covby.inf_of_sup_right

@[priority 100] -- See note [lower instance priority]
instance is_lower_modular_lattice.to_is_weak_lower_modular_lattice :
  is_weak_lower_modular_lattice α :=
⟨λ a b _, covby.inf_of_sup_right⟩

instance : is_upper_modular_lattice (order_dual α) := ⟨λ a b h, h.of_dual.inf_of_sup_left.to_dual⟩

end lower_modular

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

instance : is_modular_lattice αᵒᵈ :=
⟨λ x y z xz, le_of_eq (by { rw [inf_comm, sup_comm, eq_comm, inf_comm, sup_comm],
  exact @sup_inf_assoc_of_le α _ _ _ y _ xz })⟩

variables {x y z : α}

theorem is_modular_lattice.sup_inf_sup_assoc :
  (x ⊔ z) ⊓ (y ⊔ z) = ((x ⊔ z) ⊓ y) ⊔ z :=
@is_modular_lattice.inf_sup_inf_assoc αᵒᵈ _ _ _ _ _

theorem eq_of_le_of_inf_le_of_sup_le (hxy : x ≤ y) (hinf : y ⊓ z ≤ x ⊓ z) (hsup : y ⊔ z ≤ x ⊔ z) :
  x = y :=
le_antisymm hxy $
  have h : y ≤ x ⊔ z,
    from calc y ≤ y ⊔ z : le_sup_left
      ... ≤ x ⊔ z : hsup,
  calc y ≤ (x ⊔ z) ⊓ y : le_inf h le_rfl
    ... = x ⊔ (z ⊓ y) : sup_inf_assoc_of_le _ hxy
    ... ≤ x ⊔ (z ⊓ x) : sup_le_sup_left
      (by rw [inf_comm, @inf_comm _ _ z]; exact hinf) _
    ... ≤ x : sup_le le_rfl inf_le_right

theorem sup_lt_sup_of_lt_of_inf_le_inf (hxy : x < y) (hinf : y ⊓ z ≤ x ⊓ z) : x ⊔ z < y ⊔ z :=
lt_of_le_of_ne
  (sup_le_sup_right (le_of_lt hxy) _)
  (λ hsup, ne_of_lt hxy $ eq_of_le_of_inf_le_of_sup_le (le_of_lt hxy) hinf
    (le_of_eq hsup.symm))

theorem inf_lt_inf_of_lt_of_sup_le_sup (hxy : x < y) (hinf : y ⊔ z ≤ x ⊔ z) : x ⊓ z < y ⊓ z :=
@sup_lt_sup_of_lt_of_inf_le_inf αᵒᵈ _ _ _ _ _ hxy hinf

/-- A generalization of the theorem that if `N` is a submodule of `M` and
  `N` and `M / N` are both Artinian, then `M` is Artinian. -/
theorem well_founded_lt_exact_sequence
  {β γ : Type*} [partial_order β] [preorder γ]
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
  {β γ : Type*} [preorder β] [partial_order γ]
  (h₁ : well_founded ((>) : β → β → Prop))
  (h₂ : well_founded ((>) : γ → γ → Prop))
  (K : α) (f₁ : β → α) (f₂ : α → β) (g₁ : γ → α) (g₂ : α → γ)
  (gci : galois_coinsertion f₁ f₂)
  (gi : galois_insertion g₂ g₁)
  (hf : ∀ a, f₁ (f₂ a) = a ⊓ K)
  (hg : ∀ a, g₁ (g₂ a) = a ⊔ K) :
  well_founded ((>) : α → α → Prop) :=
@well_founded_lt_exact_sequence αᵒᵈ _ _ γᵒᵈ βᵒᵈ _ _ h₂ h₁ K g₁ g₂ f₁ f₂ gi.dual gci.dual hg hf

/-- The diamond isomorphism between the intervals `[a ⊓ b, a]` and `[b, a ⊔ b]` -/
@[simps]
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

lemma inf_strict_mono_on_Icc_sup {a b : α} : strict_mono_on (λ c, a ⊓ c) (Icc b (a ⊔ b)) :=
strict_mono.of_restrict (inf_Icc_order_iso_Icc_sup a b).symm.strict_mono

lemma sup_strict_mono_on_Icc_inf {a b : α} : strict_mono_on (λ c, c ⊔ b) (Icc (a ⊓ b) a) :=
strict_mono.of_restrict (inf_Icc_order_iso_Icc_sup a b).strict_mono

/-- The diamond isomorphism between the intervals `]a ⊓ b, a[` and `}b, a ⊔ b[`. -/
@[simps]
def inf_Ioo_order_iso_Ioo_sup (a b : α) : Ioo (a ⊓ b) a ≃o Ioo b (a ⊔ b) :=
{ to_fun := λ c, ⟨c ⊔ b,
    le_sup_right.trans_lt $ sup_strict_mono_on_Icc_inf (left_mem_Icc.2 inf_le_left)
      (Ioo_subset_Icc_self c.2) c.2.1,
    sup_strict_mono_on_Icc_inf (Ioo_subset_Icc_self c.2) (right_mem_Icc.2 inf_le_left) c.2.2⟩,
  inv_fun := λ c, ⟨a ⊓ c,
    inf_strict_mono_on_Icc_sup (left_mem_Icc.2 le_sup_right) (Ioo_subset_Icc_self c.2) c.2.1,
    inf_le_left.trans_lt' $ inf_strict_mono_on_Icc_sup (Ioo_subset_Icc_self c.2)
      (right_mem_Icc.2 le_sup_right) c.2.2⟩,
  left_inv := λ c, subtype.ext $
    by { dsimp, rw [sup_comm, ←inf_sup_assoc_of_le _ c.prop.2.le, sup_eq_right.2 c.prop.1.le] },
  right_inv := λ c, subtype.ext $
    by { dsimp, rw [inf_comm, inf_sup_assoc_of_le _ c.prop.1.le, inf_eq_left.2 c.prop.2.le] },
  map_rel_iff' := λ c d, @order_iso.le_iff_le _ _ _ _ (inf_Icc_order_iso_Icc_sup _ _)
    ⟨c.1, Ioo_subset_Icc_self c.2⟩ ⟨d.1, Ioo_subset_Icc_self d.2⟩ }

@[priority 100] -- See note [lower instance priority]
instance is_modular_lattice.to_is_lower_modular_lattice : is_lower_modular_lattice α :=
⟨λ a b, by { simp_rw [covby_iff_Ioo_eq, @sup_comm _ _ a, @inf_comm _ _ a, ←is_empty_coe_sort,
  right_lt_sup, inf_lt_left, (inf_Ioo_order_iso_Ioo_sup _ _).symm.to_equiv.is_empty_congr],
    exact id }⟩

@[priority 100] -- See note [lower instance priority]
instance is_modular_lattice.to_is_upper_modular_lattice : is_upper_modular_lattice α :=
⟨λ a b, by { simp_rw [covby_iff_Ioo_eq, ←is_empty_coe_sort,
  right_lt_sup, inf_lt_left, (inf_Ioo_order_iso_Ioo_sup _ _).to_equiv.is_empty_congr], exact id }⟩

end is_modular_lattice

namespace is_compl
variables [lattice α] [bounded_order α] [is_modular_lattice α]

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
  [lattice α] [order_bot α] [is_modular_lattice α] {a b c : α}
  (h : disjoint a b) (hsup : disjoint (a ⊔ b) c) :
  disjoint a (b ⊔ c) :=
begin
  rw [disjoint_iff_inf_le, ← h.eq_bot, sup_comm],
  apply le_inf inf_le_left,
  apply (inf_le_inf_right (c ⊔ b) le_sup_right).trans,
  rw [sup_comm, is_modular_lattice.sup_inf_sup_assoc, hsup.eq_bot, bot_sup_eq]
end

theorem disjoint.disjoint_sup_left_of_disjoint_sup_right
  [lattice α] [order_bot α] [is_modular_lattice α] {a b c : α}
  (h : disjoint b c) (hsup : disjoint a (b ⊔ c)) :
  disjoint (a ⊔ b) c :=
begin
  rw [disjoint.comm, sup_comm],
  apply disjoint.disjoint_sup_right_of_disjoint_sup_left h.symm,
  rwa [sup_comm, disjoint.comm] at hsup,
end

namespace is_modular_lattice

variables [lattice α] [is_modular_lattice α] {a : α}

instance is_modular_lattice_Iic : is_modular_lattice (set.Iic a) :=
⟨λ x y z xz, (sup_inf_le_assoc_of_le (y : α) xz : (↑x ⊔ ↑y) ⊓ ↑z ≤ ↑x ⊔ ↑y ⊓ ↑z)⟩

instance is_modular_lattice_Ici : is_modular_lattice (set.Ici a) :=
⟨λ x y z xz, (sup_inf_le_assoc_of_le (y : α) xz : (↑x ⊔ ↑y) ⊓ ↑z ≤ ↑x ⊔ ↑y ⊓ ↑z)⟩

section complemented_lattice
variables [bounded_order α] [complemented_lattice α]

instance complemented_lattice_Iic : complemented_lattice (set.Iic a) :=
⟨λ ⟨x, hx⟩, let ⟨y, hy⟩ := exists_is_compl x in
  ⟨⟨y ⊓ a, set.mem_Iic.2 inf_le_right⟩, begin
    split,
    { rw disjoint_iff_inf_le,
      change x ⊓ (y ⊓ a) ≤ ⊥, -- improve lattice subtype API
      rw ← inf_assoc,
      exact le_trans inf_le_left hy.1.le_bot },
    { rw codisjoint_iff_le_sup,
      change a ≤ x ⊔ (y ⊓ a), -- improve lattice subtype API
      rw [← sup_inf_assoc_of_le _ (set.mem_Iic.1 hx), hy.2.eq_top, top_inf_eq] }
  end⟩⟩

instance complemented_lattice_Ici : complemented_lattice (set.Ici a) :=
⟨λ ⟨x, hx⟩, let ⟨y, hy⟩ := exists_is_compl x in
  ⟨⟨y ⊔ a, set.mem_Ici.2 le_sup_right⟩, begin
    split,
    { rw disjoint_iff_inf_le,
      change x ⊓ (y ⊔ a) ≤ a, -- improve lattice subtype API
      rw [← inf_sup_assoc_of_le _ (set.mem_Ici.1 hx), hy.1.eq_bot, bot_sup_eq] },
    { rw codisjoint_iff_le_sup,
      change ⊤ ≤ x ⊔ (y ⊔ a), -- improve lattice subtype API
      rw ← sup_assoc,
      exact le_trans hy.2.top_le le_sup_left }
  end⟩⟩

end complemented_lattice

end is_modular_lattice
