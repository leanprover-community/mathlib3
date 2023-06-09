/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import order.modular_lattice
import order.well_founded

/-!
# Atoms, Coatoms, and Simple Lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module defines atoms, which are minimal non-`⊥` elements in bounded lattices, simple lattices,
which are lattices with only two elements, and related ideas.

## Main definitions

### Atoms and Coatoms
  * `is_atom a` indicates that the only element below `a` is `⊥`.
  * `is_coatom a` indicates that the only element above `a` is `⊤`.

### Atomic and Atomistic Lattices
  * `is_atomic` indicates that every element other than `⊥` is above an atom.
  * `is_coatomic` indicates that every element other than `⊤` is below a coatom.
  * `is_atomistic` indicates that every element is the `Sup` of a set of atoms.
  * `is_coatomistic` indicates that every element is the `Inf` of a set of coatoms.

### Simple Lattices
  * `is_simple_order` indicates that an order has only two unique elements, `⊥` and `⊤`.
  * `is_simple_order.bounded_order`
  * `is_simple_order.distrib_lattice`
  * Given an instance of `is_simple_order`, we provide the following definitions. These are not
    made global instances as they contain data :
    * `is_simple_order.boolean_algebra`
    * `is_simple_order.complete_lattice`
    * `is_simple_order.complete_boolean_algebra`

## Main results
  * `is_atom_dual_iff_is_coatom` and `is_coatom_dual_iff_is_atom` express the (definitional) duality
   of `is_atom` and `is_coatom`.
  * `is_simple_order_iff_is_atom_top` and `is_simple_order_iff_is_coatom_bot` express the
  connection between atoms, coatoms, and simple lattices
  * `is_compl.is_atom_iff_is_coatom` and `is_compl.is_coatom_if_is_atom`: In a modular
  bounded lattice, a complement of an atom is a coatom and vice versa.
  * `is_atomic_iff_is_coatomic`: A modular complemented lattice is atomic iff it is coatomic.

-/

variables {α β : Type*}

section atoms

section is_atom

section preorder

variables [preorder α] [order_bot α] {a b x : α}

/-- An atom of an `order_bot` is an element with no other element between it and `⊥`,
  which is not `⊥`. -/
def is_atom (a : α) : Prop := a ≠ ⊥ ∧ (∀ b, b < a → b = ⊥)

lemma is_atom.Iic (ha : is_atom a) (hax : a ≤ x) : is_atom (⟨a, hax⟩ : set.Iic x) :=
⟨λ con, ha.1 (subtype.mk_eq_mk.1 con), λ ⟨b, hb⟩ hba, subtype.mk_eq_mk.2 (ha.2 b hba)⟩

lemma is_atom.of_is_atom_coe_Iic {a : set.Iic x} (ha : is_atom a) : is_atom (a : α) :=
⟨λ con, ha.1 (subtype.ext con), λ b hba, subtype.mk_eq_mk.1 (ha.2 ⟨b, hba.le.trans a.prop⟩ hba)⟩

lemma is_atom_iff {a : α} : is_atom a ↔ a ≠ ⊥ ∧ ∀ b ≠ ⊥, b ≤ a → a ≤ b :=
and_congr iff.rfl $ forall_congr $
  λ b, by simp only [ne.def, @not_imp_comm (b = ⊥), not_imp, lt_iff_le_not_le]

end preorder

variables [partial_order α] [order_bot α] {a b x : α}

lemma is_atom.lt_iff (h : is_atom a) : x < a ↔ x = ⊥ := ⟨h.2 x, λ hx, hx.symm ▸ h.1.bot_lt⟩

lemma is_atom.le_iff (h : is_atom a) : x ≤ a ↔ x = ⊥ ∨ x = a :=
by rw [le_iff_lt_or_eq, h.lt_iff]

lemma is_atom.Iic_eq (h : is_atom a) : set.Iic a = {⊥, a} := set.ext $ λ x, h.le_iff

@[simp] lemma bot_covby_iff : ⊥ ⋖ a ↔ is_atom a :=
by simp only [covby, bot_lt_iff_ne_bot, is_atom, not_imp_not]

alias bot_covby_iff ↔ covby.is_atom is_atom.bot_covby

end is_atom

section is_coatom

section preorder

variables [preorder α]

/-- A coatom of an `order_top` is an element with no other element between it and `⊤`,
  which is not `⊤`. -/
def is_coatom [order_top α] (a : α) : Prop := a ≠ ⊤ ∧ (∀ b, a < b → b = ⊤)

@[simp] lemma is_coatom_dual_iff_is_atom [order_bot α] {a : α}:
  is_coatom (order_dual.to_dual a) ↔ is_atom a :=
iff.rfl

@[simp] lemma is_atom_dual_iff_is_coatom [order_top α] {a : α} :
  is_atom (order_dual.to_dual a) ↔ is_coatom a :=
iff.rfl

alias is_coatom_dual_iff_is_atom ↔ _ is_atom.dual
alias is_atom_dual_iff_is_coatom ↔ _ is_coatom.dual

variables [order_top α] {a x : α}

lemma is_coatom.Ici (ha : is_coatom a) (hax : x ≤ a) : is_coatom (⟨a, hax⟩ : set.Ici x) :=
ha.dual.Iic hax

lemma is_coatom.of_is_coatom_coe_Ici {a : set.Ici x} (ha : is_coatom a) :
  is_coatom (a : α) :=
@is_atom.of_is_atom_coe_Iic αᵒᵈ _ _ x a ha

lemma is_coatom_iff {a : α} : is_coatom a ↔ a ≠ ⊤ ∧ ∀ b ≠ ⊤, a ≤ b → b ≤ a := @is_atom_iff αᵒᵈ _ _ _

end preorder

variables [partial_order α] [order_top α] {a b x : α}

lemma is_coatom.lt_iff (h : is_coatom a) : a < x ↔ x = ⊤ := h.dual.lt_iff
lemma is_coatom.le_iff (h : is_coatom a) : a ≤ x ↔ x = ⊤ ∨ x = a := h.dual.le_iff
lemma is_coatom.Ici_eq (h : is_coatom a) : set.Ici a = {⊤, a} := h.dual.Iic_eq

@[simp] lemma covby_top_iff : a ⋖ ⊤ ↔ is_coatom a :=
to_dual_covby_to_dual_iff.symm.trans bot_covby_iff

alias covby_top_iff ↔ covby.is_coatom is_coatom.covby_top

end is_coatom

section partial_order
variables [partial_order α] {a b : α}

@[simp] lemma set.Ici.is_atom_iff {b : set.Ici a} : is_atom b ↔ a ⋖ b :=
begin
  rw ←bot_covby_iff,
  refine (set.ord_connected.apply_covby_apply_iff (order_embedding.subtype $ λ c, a ≤ c) _).symm,
  simpa only [order_embedding.subtype_apply, subtype.range_coe_subtype] using set.ord_connected_Ici,
end

@[simp] lemma set.Iic.is_coatom_iff {a : set.Iic b} : is_coatom a ↔ ↑a ⋖ b :=
begin
  rw ←covby_top_iff,
  refine (set.ord_connected.apply_covby_apply_iff (order_embedding.subtype $ λ c, c ≤ b) _).symm,
  simpa only [order_embedding.subtype_apply, subtype.range_coe_subtype] using set.ord_connected_Iic,
end

lemma covby_iff_atom_Ici (h : a ≤ b) : a ⋖ b ↔ is_atom (⟨b, h⟩ : set.Ici a) := by simp
lemma covby_iff_coatom_Iic (h : a ≤ b) : a ⋖ b ↔ is_coatom (⟨a, h⟩ : set.Iic b) := by simp

end partial_order

section pairwise

lemma is_atom.inf_eq_bot_of_ne [semilattice_inf α] [order_bot α] {a b : α}
  (ha : is_atom a) (hb : is_atom b) (hab : a ≠ b) : a ⊓ b = ⊥ :=
hab.not_le_or_not_le.elim (ha.lt_iff.1 ∘ inf_lt_left.2) (hb.lt_iff.1 ∘ inf_lt_right.2)

lemma is_atom.disjoint_of_ne [semilattice_inf α] [order_bot α] {a b : α}
  (ha : is_atom a) (hb : is_atom b) (hab : a ≠ b) : disjoint a b :=
disjoint_iff.mpr (is_atom.inf_eq_bot_of_ne ha hb hab)

lemma is_coatom.sup_eq_top_of_ne [semilattice_sup α] [order_top α] {a b : α}
  (ha : is_coatom a) (hb : is_coatom b) (hab : a ≠ b) : a ⊔ b = ⊤ :=
ha.dual.inf_eq_bot_of_ne hb.dual hab

end pairwise

end atoms

section atomic

variables [partial_order α] (α)

/-- A lattice is atomic iff every element other than `⊥` has an atom below it. -/
@[mk_iff] class is_atomic [order_bot α] : Prop :=
(eq_bot_or_exists_atom_le : ∀ (b : α), b = ⊥ ∨ ∃ (a : α), is_atom a ∧ a ≤ b)

/-- A lattice is coatomic iff every element other than `⊤` has a coatom above it. -/
@[mk_iff] class is_coatomic [order_top α] : Prop :=
(eq_top_or_exists_le_coatom : ∀ (b : α), b = ⊤ ∨ ∃ (a : α), is_coatom a ∧ b ≤ a)

export is_atomic (eq_bot_or_exists_atom_le) is_coatomic (eq_top_or_exists_le_coatom)

variable {α}

@[simp] lemma is_coatomic_dual_iff_is_atomic [order_bot α] : is_coatomic αᵒᵈ ↔ is_atomic α :=
⟨λ h, ⟨λ b, by apply h.eq_top_or_exists_le_coatom⟩, λ h, ⟨λ b, by apply h.eq_bot_or_exists_atom_le⟩⟩

@[simp] lemma is_atomic_dual_iff_is_coatomic [order_top α] : is_atomic αᵒᵈ ↔ is_coatomic α :=
⟨λ h, ⟨λ b, by apply h.eq_bot_or_exists_atom_le⟩, λ h, ⟨λ b, by apply h.eq_top_or_exists_le_coatom⟩⟩

namespace is_atomic

variables [order_bot α] [is_atomic α]

instance is_coatomic_dual : is_coatomic αᵒᵈ := is_coatomic_dual_iff_is_atomic.2 ‹is_atomic α›

instance {x : α} : is_atomic (set.Iic x) :=
⟨λ ⟨y, hy⟩, (eq_bot_or_exists_atom_le y).imp subtype.mk_eq_mk.2
  (λ ⟨a, ha, hay⟩, ⟨⟨a, hay.trans hy⟩, ha.Iic (hay.trans hy), hay⟩)⟩

end is_atomic

namespace is_coatomic

variables [order_top α] [is_coatomic α]

instance is_coatomic : is_atomic αᵒᵈ := is_atomic_dual_iff_is_coatomic.2 ‹is_coatomic α›

instance {x : α} : is_coatomic (set.Ici x) :=
⟨λ ⟨y, hy⟩, (eq_top_or_exists_le_coatom y).imp subtype.mk_eq_mk.2
  (λ ⟨a, ha, hay⟩, ⟨⟨a, le_trans hy hay⟩, ha.Ici (le_trans hy hay), hay⟩)⟩

end is_coatomic

theorem is_atomic_iff_forall_is_atomic_Iic [order_bot α] :
  is_atomic α ↔ ∀ (x : α), is_atomic (set.Iic x) :=
⟨@is_atomic.set.Iic.is_atomic _ _ _, λ h, ⟨λ x, ((@eq_bot_or_exists_atom_le _ _ _ (h x))
  (⊤ : set.Iic x)).imp subtype.mk_eq_mk.1 (exists_imp_exists' coe
  (λ ⟨a, ha⟩, and.imp_left (is_atom.of_is_atom_coe_Iic)))⟩⟩

theorem is_coatomic_iff_forall_is_coatomic_Ici [order_top α] :
  is_coatomic α ↔ ∀ (x : α), is_coatomic (set.Ici x) :=
is_atomic_dual_iff_is_coatomic.symm.trans $ is_atomic_iff_forall_is_atomic_Iic.trans $ forall_congr
  (λ x, is_coatomic_dual_iff_is_atomic.symm.trans iff.rfl)

section well_founded

lemma is_atomic_of_order_bot_well_founded_lt [order_bot α]
  (h : well_founded ((<) : α → α → Prop)) : is_atomic α :=
⟨λ a, or_iff_not_imp_left.2 $
  λ ha, let ⟨b, hb, hm⟩ := h.has_min { b | b ≠ ⊥ ∧ b ≤ a } ⟨a, ha, le_rfl⟩ in
  ⟨b, ⟨hb.1, λ c, not_imp_not.1 $ λ hc hl, hm c ⟨hc, hl.le.trans hb.2⟩ hl⟩, hb.2⟩⟩

lemma is_coatomic_of_order_top_gt_well_founded [order_top α]
  (h : well_founded ((>) : α → α → Prop)) : is_coatomic α :=
is_atomic_dual_iff_is_coatomic.1 (@is_atomic_of_order_bot_well_founded_lt αᵒᵈ _ _ h)

end well_founded

end atomic

section atomistic

variables (α) [complete_lattice α]

/-- A lattice is atomistic iff every element is a `Sup` of a set of atoms. -/
class is_atomistic : Prop :=
(eq_Sup_atoms : ∀ (b : α), ∃ (s : set α), b = Sup s ∧ ∀ a, a ∈ s → is_atom a)

/-- A lattice is coatomistic iff every element is an `Inf` of a set of coatoms. -/
class is_coatomistic : Prop :=
(eq_Inf_coatoms : ∀ (b : α), ∃ (s : set α), b = Inf s ∧ ∀ a, a ∈ s → is_coatom a)

export is_atomistic (eq_Sup_atoms) is_coatomistic (eq_Inf_coatoms)

variable {α}

@[simp]
theorem is_coatomistic_dual_iff_is_atomistic : is_coatomistic αᵒᵈ ↔ is_atomistic α :=
⟨λ h, ⟨λ b, by apply h.eq_Inf_coatoms⟩, λ h, ⟨λ b, by apply h.eq_Sup_atoms⟩⟩

@[simp]
theorem is_atomistic_dual_iff_is_coatomistic : is_atomistic αᵒᵈ ↔ is_coatomistic α :=
⟨λ h, ⟨λ b, by apply h.eq_Sup_atoms⟩, λ h, ⟨λ b, by apply h.eq_Inf_coatoms⟩⟩

namespace is_atomistic

instance is_coatomistic_dual [h : is_atomistic α] : is_coatomistic αᵒᵈ :=
is_coatomistic_dual_iff_is_atomistic.2 h

variable [is_atomistic α]

@[priority 100]
instance : is_atomic α :=
⟨λ b, by { rcases eq_Sup_atoms b with ⟨s, rfl, hs⟩,
  cases s.eq_empty_or_nonempty with h h,
  { simp [h] },
  { exact or.intro_right _ ⟨h.some, hs _ h.some_spec, le_Sup h.some_spec⟩ } } ⟩

end is_atomistic

section is_atomistic
variables [is_atomistic α]

@[simp]
theorem Sup_atoms_le_eq (b : α) : Sup {a : α | is_atom a ∧ a ≤ b} = b :=
begin
  rcases eq_Sup_atoms b with ⟨s, rfl, hs⟩,
  exact le_antisymm (Sup_le (λ _, and.right)) (Sup_le_Sup (λ a ha, ⟨hs a ha, le_Sup ha⟩)),
end

@[simp]
theorem Sup_atoms_eq_top : Sup {a : α | is_atom a} = ⊤ :=
begin
  refine eq.trans (congr rfl (set.ext (λ x, _))) (Sup_atoms_le_eq ⊤),
  exact (and_iff_left le_top).symm,
end

theorem le_iff_atom_le_imp {a b : α} :
  a ≤ b ↔ ∀ c : α, is_atom c → c ≤ a → c ≤ b :=
⟨λ ab c hc ca, le_trans ca ab, λ h, begin
  rw [← Sup_atoms_le_eq a, ← Sup_atoms_le_eq b],
  exact Sup_le_Sup (λ c hc, ⟨hc.1, h c hc.1 hc.2⟩),
end⟩

end is_atomistic

namespace is_coatomistic

instance is_atomistic_dual [h : is_coatomistic α] : is_atomistic αᵒᵈ :=
is_atomistic_dual_iff_is_coatomistic.2 h

variable [is_coatomistic α]

@[priority 100]
instance : is_coatomic α :=
⟨λ b, by { rcases eq_Inf_coatoms b with ⟨s, rfl, hs⟩,
  cases s.eq_empty_or_nonempty with h h,
  { simp [h] },
  { exact or.intro_right _ ⟨h.some, hs _ h.some_spec, Inf_le h.some_spec⟩ } } ⟩

end is_coatomistic
end atomistic

/-- An order is simple iff it has exactly two elements, `⊥` and `⊤`. -/
class is_simple_order (α : Type*) [has_le α] [bounded_order α] extends nontrivial α : Prop :=
(eq_bot_or_eq_top : ∀ (a : α), a = ⊥ ∨ a = ⊤)

export is_simple_order (eq_bot_or_eq_top)

theorem is_simple_order_iff_is_simple_order_order_dual [has_le α] [bounded_order α] :
  is_simple_order α ↔ is_simple_order αᵒᵈ :=
begin
  split; intro i; haveI := i,
  { exact { exists_pair_ne := @exists_pair_ne α _,
      eq_bot_or_eq_top := λ a, or.symm (eq_bot_or_eq_top ((order_dual.of_dual a)) : _ ∨ _) } },
  { exact { exists_pair_ne := @exists_pair_ne αᵒᵈ _,
      eq_bot_or_eq_top := λ a, or.symm (eq_bot_or_eq_top (order_dual.to_dual a)) } }
end

lemma is_simple_order.bot_ne_top [has_le α] [bounded_order α] [is_simple_order α] :
  (⊥ : α) ≠ (⊤ : α) :=
begin
  obtain ⟨a, b, h⟩ := exists_pair_ne α,
  rcases eq_bot_or_eq_top a with rfl|rfl;
  rcases eq_bot_or_eq_top b with rfl|rfl;
  simpa <|> simpa using h.symm
end

section is_simple_order

variables [partial_order α] [bounded_order α] [is_simple_order α]

instance {α} [has_le α] [bounded_order α] [is_simple_order α] : is_simple_order αᵒᵈ :=
is_simple_order_iff_is_simple_order_order_dual.1 (by apply_instance)

/-- A simple `bounded_order` induces a preorder. This is not an instance to prevent loops. -/
protected def is_simple_order.preorder {α} [has_le α] [bounded_order α] [is_simple_order α] :
  preorder α :=
{ le := (≤),
  le_refl := λ a, by rcases eq_bot_or_eq_top a with rfl|rfl; simp,
  le_trans := λ a b c, begin
    rcases eq_bot_or_eq_top a with rfl|rfl,
    { simp },
    { rcases eq_bot_or_eq_top b with rfl|rfl,
      { rcases eq_bot_or_eq_top c with rfl|rfl; simp },
      { simp } }
  end }

/-- A simple partial ordered `bounded_order` induces a linear order.
This is not an instance to prevent loops. -/
protected def is_simple_order.linear_order [decidable_eq α] : linear_order α :=
{ le_total := λ a b, by rcases eq_bot_or_eq_top a with rfl|rfl; simp,
  decidable_le := λ a b, if ha : a = ⊥ then is_true (ha.le.trans bot_le) else
    if hb : b = ⊤ then is_true (le_top.trans hb.ge) else
      is_false (λ H, hb (top_unique
        (le_trans (top_le_iff.mpr (or.resolve_left (eq_bot_or_eq_top a) ha)) H))),
  decidable_eq := by assumption,
  ..(infer_instance : partial_order α) }

@[simp] lemma is_atom_top : is_atom (⊤ : α) :=
⟨top_ne_bot, λ a ha, or.resolve_right (eq_bot_or_eq_top a) (ne_of_lt ha)⟩

@[simp] lemma is_coatom_bot : is_coatom (⊥ : α) := is_atom_dual_iff_is_coatom.1 is_atom_top

lemma bot_covby_top : (⊥ : α) ⋖ ⊤ := is_atom_top.bot_covby

end is_simple_order

namespace is_simple_order
section preorder
variables [preorder α] [bounded_order α] [is_simple_order α] {a b : α} (h : a < b)

lemma eq_bot_of_lt : a = ⊥ := (is_simple_order.eq_bot_or_eq_top _).resolve_right h.ne_top
lemma eq_top_of_lt : b = ⊤ := (is_simple_order.eq_bot_or_eq_top _).resolve_left h.ne_bot

alias eq_bot_of_lt ← has_lt.lt.eq_bot
alias eq_top_of_lt ← has_lt.lt.eq_top

end preorder

section bounded_order

variables [lattice α] [bounded_order α] [is_simple_order α]

/-- A simple partial ordered `bounded_order` induces a lattice.
This is not an instance to prevent loops -/
protected def lattice {α} [decidable_eq α] [partial_order α] [bounded_order α]
  [is_simple_order α] : lattice α :=
@linear_order.to_lattice α (is_simple_order.linear_order)

/-- A lattice that is a `bounded_order` is a distributive lattice.
This is not an instance to prevent loops -/
protected def distrib_lattice : distrib_lattice α :=
{ le_sup_inf := λ x y z, by { rcases eq_bot_or_eq_top x with rfl | rfl; simp },
  .. (infer_instance : lattice α) }

@[priority 100] -- see Note [lower instance priority]
instance : is_atomic α :=
⟨λ b, (eq_bot_or_eq_top b).imp_right (λ h, ⟨⊤, ⟨is_atom_top, ge_of_eq h⟩⟩)⟩

@[priority 100] -- see Note [lower instance priority]
instance : is_coatomic α := is_atomic_dual_iff_is_coatomic.1 is_simple_order.is_atomic

end bounded_order

/- It is important that in this section `is_simple_order` is the last type-class argument. -/
section decidable_eq

variables [decidable_eq α] [partial_order α] [bounded_order α] [is_simple_order α]

/-- Every simple lattice is isomorphic to `bool`, regardless of order. -/
@[simps] def equiv_bool {α} [decidable_eq α] [has_le α] [bounded_order α] [is_simple_order α] :
  α ≃ bool :=
{ to_fun := λ x, x = ⊤,
  inv_fun := λ x, cond x ⊤ ⊥,
  left_inv := λ x, by { rcases (eq_bot_or_eq_top x) with rfl | rfl; simp [bot_ne_top] },
  right_inv := λ x, by { cases x; simp [bot_ne_top] } }

/-- Every simple lattice over a partial order is order-isomorphic to `bool`. -/
def order_iso_bool : α ≃o bool :=
{ map_rel_iff' := λ a b, begin
    rcases (eq_bot_or_eq_top a) with rfl | rfl,
    { simp [bot_ne_top] },
    { rcases (eq_bot_or_eq_top b) with rfl | rfl,
      { simp [bot_ne_top.symm, bot_ne_top, bool.ff_lt_tt] },
      { simp [bot_ne_top] } }
  end,
  ..equiv_bool }

/-- A simple `bounded_order` is also a `boolean_algebra`. -/
protected def boolean_algebra {α} [decidable_eq α] [lattice α] [bounded_order α]
  [is_simple_order α] : boolean_algebra α :=
{ compl := λ x, if x = ⊥ then ⊤ else ⊥,
  sdiff := λ x y, if x = ⊤ ∧ y = ⊥ then ⊤ else ⊥,
  sdiff_eq := λ x y, by rcases eq_bot_or_eq_top x with rfl | rfl;
      simp [bot_ne_top, has_sdiff.sdiff, compl],
  inf_compl_le_bot := λ x, begin
      rcases eq_bot_or_eq_top x with rfl | rfl,
      { simp },
      { simp only [top_inf_eq],
        split_ifs with h h;
        simp [h] }
    end,
  top_le_sup_compl := λ x, by rcases eq_bot_or_eq_top x with rfl | rfl; simp,
  .. (show bounded_order α, by apply_instance),
  .. is_simple_order.distrib_lattice }

end decidable_eq

variables [lattice α] [bounded_order α] [is_simple_order α]
open_locale classical

/-- A simple `bounded_order` is also complete. -/
protected noncomputable def complete_lattice : complete_lattice α :=
{ Sup := λ s, if ⊤ ∈ s then ⊤ else ⊥,
  Inf := λ s, if ⊥ ∈ s then ⊥ else ⊤,
  le_Sup := λ s x h, by { rcases eq_bot_or_eq_top x with rfl | rfl,
    { exact bot_le },
    { rw if_pos h } },
  Sup_le := λ s x h, by { rcases eq_bot_or_eq_top x with rfl | rfl,
    { rw if_neg,
      intro con,
      exact bot_ne_top (eq_top_iff.2 (h ⊤ con)) },
    { exact le_top } },
  Inf_le := λ s x h, by { rcases eq_bot_or_eq_top x with rfl | rfl,
    { rw if_pos h },
    { exact le_top } },
  le_Inf := λ s x h, by { rcases eq_bot_or_eq_top x with rfl | rfl,
    { exact bot_le },
    { rw if_neg,
      intro con,
      exact top_ne_bot (eq_bot_iff.2 (h ⊥ con)) } },
  .. (infer_instance : lattice α),
  .. (infer_instance : bounded_order α) }

/-- A simple `bounded_order` is also a `complete_boolean_algebra`. -/
protected noncomputable def complete_boolean_algebra : complete_boolean_algebra α :=
{ infi_sup_le_sup_Inf := λ x s, by { rcases eq_bot_or_eq_top x with rfl | rfl,
    { simp only [bot_sup_eq, ← Inf_eq_infi], exact le_rfl },
    { simp only [top_sup_eq, le_top] }, },
  inf_Sup_le_supr_inf := λ x s, by { rcases eq_bot_or_eq_top x with rfl | rfl,
    { simp only [bot_inf_eq, bot_le] },
    { simp only [top_inf_eq, ← Sup_eq_supr], exact le_rfl } },
  .. is_simple_order.complete_lattice,
  .. is_simple_order.boolean_algebra }

end is_simple_order

namespace is_simple_order
variables [complete_lattice α] [is_simple_order α]
set_option default_priority 100

instance : is_atomistic α :=
⟨λ b, (eq_bot_or_eq_top b).elim
  (λ h, ⟨∅, ⟨h.trans Sup_empty.symm, λ a ha, false.elim (set.not_mem_empty _ ha)⟩⟩)
  (λ h, ⟨{⊤}, h.trans Sup_singleton.symm, λ a ha, (set.mem_singleton_iff.1 ha).symm ▸ is_atom_top⟩)⟩

instance : is_coatomistic α := is_atomistic_dual_iff_is_coatomistic.1 is_simple_order.is_atomistic

end is_simple_order

theorem is_simple_order_iff_is_atom_top [partial_order α] [bounded_order α] :
  is_simple_order α ↔ is_atom (⊤ : α) :=
⟨λ h, @is_atom_top _ _ _ h, λ h,
  { exists_pair_ne := ⟨⊤, ⊥, h.1⟩,
    eq_bot_or_eq_top := λ a, ((eq_or_lt_of_le le_top).imp_right (h.2 a)).symm }⟩

theorem is_simple_order_iff_is_coatom_bot [partial_order α] [bounded_order α] :
  is_simple_order α ↔ is_coatom (⊥ : α) :=
is_simple_order_iff_is_simple_order_order_dual.trans is_simple_order_iff_is_atom_top

namespace set

theorem is_simple_order_Iic_iff_is_atom [partial_order α] [order_bot α] {a : α} :
  is_simple_order (Iic a) ↔ is_atom a :=
is_simple_order_iff_is_atom_top.trans $ and_congr (not_congr subtype.mk_eq_mk)
  ⟨λ h b ab, subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab),
    λ h ⟨b, hab⟩ hbotb, subtype.mk_eq_mk.2 (h b (subtype.mk_lt_mk.1 hbotb))⟩

theorem is_simple_order_Ici_iff_is_coatom [partial_order α] [order_top α] {a : α} :
  is_simple_order (Ici a) ↔ is_coatom a :=
is_simple_order_iff_is_coatom_bot.trans $ and_congr (not_congr subtype.mk_eq_mk)
  ⟨λ h b ab, subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab),
    λ h ⟨b, hab⟩ hbotb, subtype.mk_eq_mk.2 (h b (subtype.mk_lt_mk.1 hbotb))⟩

end set

namespace order_embedding

variables [partial_order α] [partial_order β]

lemma is_atom_of_map_bot_of_image [order_bot α] [order_bot β] (f : β ↪o α) (hbot : f ⊥ = ⊥) {b : β}
  (hb : is_atom (f b)) : is_atom b :=
by { simp only [←bot_covby_iff] at hb ⊢, exact covby.of_image f (hbot.symm ▸ hb) }

lemma is_coatom_of_map_top_of_image [order_top α] [order_top β] (f : β ↪o α) (htop : f ⊤ = ⊤)
  {b : β} (hb : is_coatom (f b)) : is_coatom b :=
f.dual.is_atom_of_map_bot_of_image htop hb

end order_embedding

namespace galois_insertion

variables [partial_order α] [partial_order β]

lemma is_atom_of_u_bot [order_bot α] [order_bot β] {l : α → β} {u : β → α}
  (gi : galois_insertion l u) (hbot : u ⊥ = ⊥) {b : β} (hb : is_atom (u b)) : is_atom b :=
order_embedding.is_atom_of_map_bot_of_image
  ⟨⟨u, gi.u_injective⟩, @galois_insertion.u_le_u_iff _ _ _ _ _ _ gi⟩ hbot hb

lemma is_atom_iff [order_bot α] [is_atomic α] [order_bot β] {l : α → β} {u : β → α}
  (gi : galois_insertion l u) (hbot : u ⊥ = ⊥) (h_atom : ∀ a, is_atom a → u (l a) = a) (a : α) :
  is_atom (l a) ↔ is_atom a :=
begin
  refine ⟨λ hla, _, λ ha, gi.is_atom_of_u_bot hbot ((h_atom a ha).symm ▸ ha)⟩,
  obtain ⟨a', ha', hab'⟩ := (eq_bot_or_exists_atom_le (u (l a))).resolve_left
    (hbot ▸ λ h, hla.1 (gi.u_injective h)),
  have := (hla.le_iff.mp $ (gi.l_u_eq (l a) ▸ gi.gc.monotone_l hab' : l a' ≤ l a)).resolve_left
    (λ h, ha'.1 (hbot ▸ (h_atom a' ha') ▸ congr_arg u h)),
  have haa' : a = a' := (ha'.le_iff.mp $
    (gi.gc.le_u_l a).trans_eq (h_atom a' ha' ▸ congr_arg u this.symm)).resolve_left
    (mt (congr_arg l) (gi.gc.l_bot.symm ▸ hla.1)),
  exact haa'.symm ▸ ha'
end

lemma is_atom_iff' [order_bot α] [is_atomic α] [order_bot β] {l : α → β} {u : β → α}
  (gi : galois_insertion l u) (hbot : u ⊥ = ⊥) (h_atom : ∀ a, is_atom a → u (l a) = a) (b : β) :
  is_atom (u b) ↔ is_atom b :=
by rw [←gi.is_atom_iff hbot h_atom, gi.l_u_eq]

lemma is_coatom_of_image [order_top α] [order_top β] {l : α → β} {u : β → α}
  (gi : galois_insertion l u) {b : β} (hb : is_coatom (u b)) : is_coatom b :=
order_embedding.is_coatom_of_map_top_of_image
  ⟨⟨u, gi.u_injective⟩, @galois_insertion.u_le_u_iff _ _ _ _ _ _ gi⟩ gi.gc.u_top hb

lemma is_coatom_iff [order_top α] [is_coatomic α] [order_top β] {l : α → β} {u : β → α}
  (gi : galois_insertion l u) (h_coatom : ∀ a : α, is_coatom a → u (l a) = a) (b : β) :
  is_coatom (u b) ↔ is_coatom b :=
begin
  refine ⟨λ hb, gi.is_coatom_of_image hb, λ hb, _⟩,
  obtain ⟨a, ha, hab⟩ := (eq_top_or_exists_le_coatom (u b)).resolve_left
    (λ h, hb.1 $ (gi.gc.u_top ▸ gi.l_u_eq ⊤ : l ⊤ = ⊤) ▸ gi.l_u_eq b ▸ congr_arg l h),
  have : l a = b := (hb.le_iff.mp ((gi.l_u_eq b ▸ gi.gc.monotone_l hab) : b ≤ l a)).resolve_left
    (λ hla, ha.1 (gi.gc.u_top ▸ h_coatom a ha ▸ congr_arg u hla)),
  exact this ▸ (h_coatom a ha).symm ▸ ha,
end

end galois_insertion

namespace galois_coinsertion

variables [partial_order α] [partial_order β]

lemma is_coatom_of_l_top [order_top α] [order_top β] {l : α → β} {u : β → α}
  (gi : galois_coinsertion l u) (hbot : l ⊤ = ⊤) {a : α} (hb : is_coatom (l a)) : is_coatom a :=
gi.dual.is_atom_of_u_bot hbot hb.dual

lemma is_coatom_iff [order_top α] [order_top β] [is_coatomic β] {l : α → β} {u : β → α}
  (gi : galois_coinsertion l u) (htop : l ⊤ = ⊤) (h_coatom : ∀ b, is_coatom b → l (u b) = b)
  (b : β) : is_coatom (u b) ↔ is_coatom b :=
gi.dual.is_atom_iff htop h_coatom b

lemma is_coatom_iff' [order_top α] [order_top β] [is_coatomic β] {l : α → β} {u : β → α}
  (gi : galois_coinsertion l u) (htop : l ⊤ = ⊤) (h_coatom : ∀ b, is_coatom b → l (u b) = b)
  (a : α) : is_coatom (l a) ↔ is_coatom a :=
gi.dual.is_atom_iff' htop h_coatom a

lemma is_atom_of_image [order_bot α] [order_bot β] {l : α → β} {u : β → α}
  (gi : galois_coinsertion l u) {a : α} (hb : is_atom (l a)) : is_atom a :=
gi.dual.is_coatom_of_image hb.dual

lemma is_atom_iff [order_bot α] [order_bot β] [is_atomic β] {l : α → β} {u : β → α}
  (gi : galois_coinsertion l u) (h_atom : ∀ b, is_atom b → l (u b) = b) (a : α) :
  is_atom (l a) ↔ is_atom a :=
gi.dual.is_coatom_iff h_atom a

end galois_coinsertion

namespace order_iso

variables [partial_order α] [partial_order β]

@[simp] lemma is_atom_iff [order_bot α] [order_bot β] (f : α ≃o β) (a : α) :
  is_atom (f a) ↔ is_atom a :=
⟨f.to_galois_coinsertion.is_atom_of_image,
 λ ha, f.to_galois_insertion.is_atom_of_u_bot (map_bot f.symm) $ (f.symm_apply_apply a).symm ▸ ha⟩

@[simp] lemma is_coatom_iff [order_top α] [order_top β] (f : α ≃o β) (a : α) :
  is_coatom (f a) ↔ is_coatom a :=
f.dual.is_atom_iff a

lemma is_simple_order_iff [bounded_order α] [bounded_order β] (f : α ≃o β) :
  is_simple_order α ↔ is_simple_order β :=
by rw [is_simple_order_iff_is_atom_top, is_simple_order_iff_is_atom_top,
  ← f.is_atom_iff ⊤, f.map_top]

lemma is_simple_order [bounded_order α] [bounded_order β] [h : is_simple_order β] (f : α ≃o β) :
  is_simple_order α :=
f.is_simple_order_iff.mpr h

protected lemma is_atomic_iff [order_bot α] [order_bot β] (f : α ≃o β) :
  is_atomic α ↔ is_atomic β :=
by simp only [is_atomic_iff, f.surjective.forall, f.surjective.exists, ← map_bot f, f.eq_iff_eq,
  f.le_iff_le, f.is_atom_iff]

protected lemma is_coatomic_iff [order_top α] [order_top β] (f : α ≃o β) :
  is_coatomic α ↔ is_coatomic β :=
by simp only [← is_atomic_dual_iff_is_coatomic, f.dual.is_atomic_iff]

end order_iso

section is_modular_lattice
variables [lattice α] [bounded_order α] [is_modular_lattice α]

namespace is_compl
variables {a b : α} (hc : is_compl a b)
include hc

lemma is_atom_iff_is_coatom : is_atom a ↔ is_coatom b :=
set.is_simple_order_Iic_iff_is_atom.symm.trans $ hc.Iic_order_iso_Ici.is_simple_order_iff.trans
  set.is_simple_order_Ici_iff_is_coatom

lemma is_coatom_iff_is_atom : is_coatom a ↔ is_atom b := hc.symm.is_atom_iff_is_coatom.symm

end is_compl

variables [complemented_lattice α]

lemma is_coatomic_of_is_atomic_of_complemented_lattice_of_is_modular [is_atomic α] :
  is_coatomic α :=
⟨λ x, begin
  rcases exists_is_compl x with ⟨y, xy⟩,
  apply (eq_bot_or_exists_atom_le y).imp _ _,
  { rintro rfl,
    exact eq_top_of_is_compl_bot xy },
  { rintro ⟨a, ha, ay⟩,
    rcases exists_is_compl (xy.symm.Iic_order_iso_Ici ⟨a, ay⟩) with ⟨⟨b, xb⟩, hb⟩,
    refine ⟨↑(⟨b, xb⟩ : set.Ici x), is_coatom.of_is_coatom_coe_Ici _, xb⟩,
    rw [← hb.is_atom_iff_is_coatom, order_iso.is_atom_iff],
    apply ha.Iic }
end⟩

lemma is_atomic_of_is_coatomic_of_complemented_lattice_of_is_modular [is_coatomic α] :
  is_atomic α :=
is_coatomic_dual_iff_is_atomic.1 is_coatomic_of_is_atomic_of_complemented_lattice_of_is_modular

theorem is_atomic_iff_is_coatomic : is_atomic α ↔ is_coatomic α :=
⟨λ h, @is_coatomic_of_is_atomic_of_complemented_lattice_of_is_modular _ _ _ _ _ h,
  λ h, @is_atomic_of_is_coatomic_of_complemented_lattice_of_is_modular _ _ _ _ _ h⟩

end is_modular_lattice

namespace set

lemma is_atom_singleton (x : α) : is_atom ({x} : set α) :=
⟨singleton_ne_empty _, λ s hs, ssubset_singleton_iff.mp hs⟩

lemma is_atom_iff (s : set α) : is_atom s ↔ ∃ x, s = {x} :=
begin
  refine ⟨_, by { rintro ⟨x, rfl⟩, exact is_atom_singleton x }⟩,
  rw [is_atom_iff, bot_eq_empty, ←nonempty_iff_ne_empty],
  rintro ⟨⟨x, hx⟩, hs⟩,
  exact ⟨x, eq_singleton_iff_unique_mem.2 ⟨hx, λ y hy,
    (hs {y} (singleton_ne_empty _) (singleton_subset_iff.2 hy) hx).symm⟩⟩,
end

lemma is_coatom_iff (s : set α) : is_coatom s ↔ ∃ x, s = {x}ᶜ :=
by simp_rw [is_compl_compl.is_coatom_iff_is_atom, is_atom_iff, @eq_comm _ s, compl_eq_comm]

lemma is_coatom_singleton_compl (x : α) : is_coatom ({x}ᶜ : set α) :=
(is_coatom_iff {x}ᶜ).mpr ⟨x, rfl⟩

instance : is_atomistic (set α) :=
{ eq_Sup_atoms := λ s, ⟨(λ x, {x}) '' s,
    by rw [Sup_eq_sUnion, sUnion_image, bUnion_of_singleton],
    by { rintro - ⟨x, hx, rfl⟩, exact is_atom_singleton x }⟩ }

instance : is_coatomistic (set α) :=
{ eq_Inf_coatoms := λ s, ⟨(λ x, {x}ᶜ) '' sᶜ,
    by rw [Inf_eq_sInter, sInter_image, ←compl_Union₂, bUnion_of_singleton, compl_compl],
    by { rintro - ⟨x, hx, rfl⟩, exact is_coatom_singleton_compl x }⟩ }

end set
