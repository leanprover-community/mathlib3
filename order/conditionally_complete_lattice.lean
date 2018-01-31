/-
Copyright (c) 2018  Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
Adapted from the corresponding theory for complete lattices.

Theory of conditionally complete lattices.

A conditionally complete lattice is a set with an order for which every set
which is nonempty and bounded above has a supremum, and every set which
is nonempty and bounded below has an infimum. Typical examples are real, nat, int

The theory is very comparable to the theory of complete lattices, except that suitable
boundedness and non-emptyness assumptions have to be added to most statements.
We introduce two predicates bdd_above and bdd_below to express this boundedness, prove
their basic properties, and then go on to prove most useful properties of Sup and Inf
in conditionally complete lattices.

To differentiate the statements between complete lattices and conditionally complete
lattices, we prefix Inf and Sup in the statements by c, giving cInf and cSup. For instance,
Inf_le is a statement in complete lattices ensuring Inf s ≤ x, while cInf_le is the same
statement in conditionally complete lattices with an additional assumption that s is
bounded below.
-/
import order.lattice order.complete_lattice tactic.finish data.set.countable

noncomputable theory
local attribute [instance] classical.decidable_inhabited classical.prop_decidable

set_option old_structure_cmd true

open preorder set lattice

universes u v
variables {α : Type u} {β : Type v}

section preorder
variables [preorder α] {s t: set α} {a b: α}

/-Sets bounded above and bounded below.-/
def bdd_above (s: set α) := (∃x, ∀y∈s, y ≤ x)
def bdd_below (s: set α) := (∃x, ∀y∈s, x ≤ y)

/-Introduction rules for boundedness above and below-/
lemma bdd_aboveI (a:α) (H: ∀y∈s, y≤a) : bdd_above s := ⟨a, H⟩
lemma bdd_belowI (a:α) (H: ∀y∈s, a≤y) : bdd_below s := ⟨a, H⟩

/-Empty sets and singletons are trivially bounded. For finite sets, we need
a notion of maximum and minimum, i.e., a lattice structure, see later on.-/
@[simp] lemma bdd_above_empty [inhabited α]: bdd_above ({}:set α) :=
⟨default α, by simp⟩

@[simp] lemma bdd_below_empty [inhabited α]: bdd_below ({}:set α) :=
⟨default α, by simp⟩

@[simp] lemma bdd_above_singleton: bdd_above ({a}:set α) :=
⟨a, by simp⟩

@[simp] lemma bdd_below_singleton: bdd_below ({a}:set α) :=
⟨a, by simp⟩

/-If a set is included in another one, boundedness of the second implies boundedness
of the first-/
lemma bdd_above_subset (_: s ⊆ t) (_: bdd_above t) : bdd_above s :=
  let ⟨w, hw⟩ := ‹bdd_above t› in  /-hw : ∀ (y : α), y ∈ t → y ≤ w-/
  ⟨w, by intros; apply hw _ (‹s ⊆ t› ‹_ ∈ s›)⟩

lemma bdd_below_subset (_: s ⊆ t) (_: bdd_below t) : bdd_below s :=
  let ⟨w, hw⟩ := ‹bdd_below t› in  /-hw : ∀ (y : α), y ∈ t → w ≤ y-/
  ⟨w, by intros; apply hw _ (‹s ⊆ t› ‹_ ∈ s›)⟩

/- Boundedness of intersections of sets, in different guises, deduced from the
subsettonicity of boundedness.-/
lemma bdd_above_Int1 (_: bdd_above s) : bdd_above (s ∩ t) :=
  by apply bdd_above_subset _ ‹bdd_above s›; simp

lemma bdd_above_Int2 (_: bdd_above t) : bdd_above (s ∩ t) :=
  by apply bdd_above_subset _ ‹bdd_above t›; simp

lemma bdd_below_Int1 (_: bdd_below s) : bdd_below (s ∩ t) :=
  by apply bdd_below_subset _ ‹bdd_below s›; simp

lemma bdd_below_Int2 (_: bdd_below t) : bdd_below (s ∩ t) :=
  by apply bdd_below_subset _ ‹bdd_below t›; simp

end preorder

/--When there is a global maximum, every set is bounded above.-/
@[simp] lemma bdd_above_top [order_top α] (s:set α): bdd_above s :=
  ⟨⊤, by intros; apply order_top.le_top⟩

/--When there is a global minimum, every set is bounded below.-/
@[simp] lemma bdd_above_bot [order_bot α] (s:set α): bdd_below s :=
  ⟨⊥, by intros; apply order_bot.bot_le⟩

/-When there is a max (i.e., in the class semilattice_sup), then the union of
two bounded sets is bounded, by the maximum of the bounds for the two sets.
With this, we deduce that finite sets are bounded by induction, and that a finite
union of bounded sets is bounded.-/
section semilattice_sup
variables [semilattice_sup α] {s t: set α} {a b: α}

/--The union of two sets is bounded above if and only if each of the sets is.-/
@[simp] lemma bdd_above_union: bdd_above (s ∪ t) ↔ (bdd_above s ∧ bdd_above t) :=
  have A: bdd_above (s ∪ t) → (bdd_above s ∧ bdd_above t) :=
  begin
    intro,
    have S: bdd_above s := by apply bdd_above_subset _ ‹bdd_above (s ∪ t)›; simp,
    have T: bdd_above t := by apply bdd_above_subset _ ‹bdd_above (s ∪ t)›; simp,
    apply and.intro S T
  end,
  have B: (bdd_above s ∧ bdd_above t) → bdd_above (s ∪ t) :=
    assume H: bdd_above s ∧ bdd_above t,
    let ⟨⟨ws, hs⟩, ⟨wt, ht⟩⟩ := H in
      /-hs : ∀ (y : α), y ∈ s → y ≤ ws      ht : ∀ (y : α), y ∈ s → y ≤ wt-/
    have Bs: ∀b∈s, b ≤ ws ⊔ wt,
      by intros; apply le_trans (hs b ‹b ∈ s›) _; simp,
    have Bt: ∀b∈t, b ≤ ws ⊔ wt,
      by intros; apply le_trans (ht b ‹b ∈ t›) _; simp,
    show bdd_above (s ∪ t),
      begin
      apply bdd_aboveI (ws ⊔ wt),
      intros b H_1,
      cases H_1,
      apply Bs _ ‹b ∈ s›,
      apply Bt _ ‹b ∈ t›,
      end,
  ⟨A, B⟩

/--Adding a point to a set preserves its boundedness above.-/
@[simp] lemma bdd_above_insert: bdd_above (insert a s) ↔ bdd_above s :=
  have A: bdd_above (insert a s) → bdd_above s :=
    by intro; apply bdd_above_subset _ ‹bdd_above (insert a s)›; simp,
  have B: bdd_above s → bdd_above (insert a s) := by rw[insert_eq]; finish,
  ⟨A, B⟩

/--A finite set is bounded above.-/
lemma bdd_above_finite [inhabited α] (_: finite s) : bdd_above s :=
  by apply finite.induction_on ‹finite s›; simp; simp

/--A finite union of sets which are all bounded above is still bounded above.-/
lemma bdd_above_finite_union [inhabited α] {β: Type v} {I : set β} {S:β → set α} (H: finite I) :
(bdd_above (⋃i∈I, S i)) ↔ (∀i ∈ I, bdd_above (S i)) :=
  have A: (bdd_above (⋃i∈I, S i)) → (∀i ∈ I, bdd_above (S i)),
    by
    intros;
    apply bdd_above_subset _ ‹bdd_above (⋃i∈I, S i)›;
    apply subset_bUnion_of_mem ‹i ∈ I›,
  have B: (∀i ∈ I, bdd_above (S i)) → (bdd_above (⋃i∈I, S i)),
    by apply finite.induction_on ‹finite I›; simp; finish,
  ⟨A, B⟩

end semilattice_sup


/-When there is a min (i.e., in the class semilattice_inf), then the union of
two sets which are bounded from below is bounded from below, by the minimum of
the bounds for the two sets. With this, we deduce that finite sets are
bounded below by induction, and that a finite union of sets which are bounded below
is still bounded below.-/

section semilattice_inf
variables [semilattice_inf α] {s t: set α} {a b: α}

/--The union of two sets is bounded below if and only if each of the sets is.-/
@[simp] lemma bdd_below_union: bdd_below (s ∪ t) ↔ (bdd_below s ∧ bdd_below t) :=
  have A: bdd_below (s ∪ t) → (bdd_below s ∧ bdd_below t) :=
  begin
    intro,
    have S: bdd_below s := by apply bdd_below_subset _ ‹bdd_below (s ∪ t)›; simp,
    have T: bdd_below t := by apply bdd_below_subset _ ‹bdd_below (s ∪ t)›; simp,
    apply and.intro S T
  end,
  have B: (bdd_below s ∧ bdd_below t) → bdd_below (s ∪ t) :=
    assume H: bdd_below s ∧ bdd_below t,
    let ⟨⟨ws, hs⟩, ⟨wt, ht⟩⟩ := H in
      /-hs : ∀ (y : α), y ∈ s → ws ≤ y      ht : ∀ (y : α), y ∈ s → wt ≤ y-/
    have Bs: ∀b∈s, ws ⊓ wt ≤ b,
      by intros; apply le_trans _ (hs b ‹b ∈ s›); simp,
    have Bt: ∀b∈t, ws ⊓ wt ≤ b,
      by intros; apply le_trans _ (ht b ‹b ∈ t›); simp,
    show bdd_below (s ∪ t),
      begin
      apply bdd_belowI (ws ⊓ wt),
      intros b H_1,
      cases H_1,
      apply Bs _ ‹b ∈ s›,
      apply Bt _ ‹b ∈ t›,
      end,
  ⟨A, B⟩

/--Adding a point to a set preserves its boundedness below.-/
@[simp] lemma bdd_below_insert: bdd_below (insert a s) ↔ bdd_below s :=
  have A: bdd_below (insert a s) → bdd_below s :=
    by intro; apply bdd_below_subset _ ‹bdd_below (insert a s)›; simp,
  have B: bdd_below s → bdd_below (insert a s) := by rw[insert_eq]; finish,
  ⟨A, B⟩

/--A finite set is bounded below.-/
lemma bdd_below_finite [inhabited α] (_: finite s) : bdd_below s :=
  by apply finite.induction_on ‹finite s›; simp; simp

/--A finite union of sets which are all bounded below is still bounded below.-/
lemma bdd_below_finite_union [inhabited α] {β: Type v} {I: set β} {S:β → set α} (H: finite I) :
(bdd_below (⋃i∈I, S i)) ↔ (∀i ∈ I, bdd_below (S i)) :=
  have A: (bdd_below (⋃i∈I, S i)) → (∀i ∈ I, bdd_below (S i)),
    by
    intros;
    apply bdd_below_subset _ ‹bdd_below (⋃i∈I, S i)›;
    apply subset_bUnion_of_mem ‹i ∈ I›,
  have B: (∀i ∈ I, bdd_below (S i)) → (bdd_below (⋃i∈I, S i)),
    by apply finite.induction_on ‹finite I›; simp; finish,
  ⟨A, B⟩

end semilattice_inf


namespace lattice
/-- A conditionally complete lattice is a lattice in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete lattices, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of non-emptyness or
boundedness.-/
class conditionally_complete_lattice (α : Type u) extends lattice α, has_Sup α, has_Inf α :=
(le_cSup : ∀s a, bdd_above s → a ∈ s → a ≤ Sup s)
(cSup_le : ∀s a, s ≠ ∅ → (∀b∈s, b ≤ a) → Sup s ≤ a)
(cInf_le : ∀s a, bdd_below s → a ∈ s → Inf s ≤ a)
(le_cInf : ∀s a, s ≠ ∅ → (∀b∈s, a ≤ b) → a ≤ Inf s)

class conditionally_complete_linear_order (α : Type u)
  extends conditionally_complete_lattice α, linear_order α

/- A complete lattice is a conditionally complete lattice, as there are no restrictions
on the properties of Inf and Sup in a complete lattice.-/

instance conditionally_complete_lattice_of_complete_lattice [complete_lattice α]:
conditionally_complete_lattice α :=
{le_cSup := by intros; apply le_Sup ‹a ∈ s›,
 cSup_le := by intros; apply Sup_le; assumption,
 cInf_le := by intros; apply Inf_le ‹a ∈ s›,
 le_cInf := by intros; apply le_Inf; assumption,
..‹complete_lattice α›}

section conditionally_complete_lattice
variables [conditionally_complete_lattice α] {s t : set α} {a b : α}

theorem le_cSup (h₁: bdd_above s) (h₂: a ∈ s) : a ≤ Sup s :=
  conditionally_complete_lattice.le_cSup s a h₁ h₂

theorem cSup_le (h₁: s ≠ ∅) (h₂: ∀b∈s, b ≤ a) : Sup s ≤ a :=
  conditionally_complete_lattice.cSup_le s a h₁ h₂

theorem cInf_le (h₁: bdd_below s) (h₂: a ∈ s) : Inf s ≤ a :=
  conditionally_complete_lattice.cInf_le s a h₁ h₂

theorem le_cInf (h₁: s ≠ ∅) (h₂: ∀b∈s, a ≤ b) : a ≤ Inf s :=
  conditionally_complete_lattice.le_cInf s a h₁ h₂

theorem le_cSup_of_le (_: bdd_above s) (hb : b ∈ s) (h : a ≤ b) : a ≤ Sup s :=
le_trans h (le_cSup ‹bdd_above s› hb)

theorem cInf_le_of_le (_: bdd_below s) (hb : b ∈ s) (h : b ≤ a) : Inf s ≤ a :=
le_trans (cInf_le ‹bdd_below s› hb) h

theorem cSup_le_cSup (_: bdd_above t) (_:s ≠ ∅) (h : s ⊆ t) : Sup s ≤ Sup t :=
cSup_le ‹s ≠ ∅› (assume a, assume ha : a ∈ s, le_cSup ‹bdd_above t› (h ha))

theorem cInf_le_cInf (_: bdd_below t) (_:s ≠ ∅) (h : s ⊆ t) : Inf t ≤ Inf s :=
le_cInf ‹s ≠ ∅› (assume a, assume ha : a ∈ s, cInf_le ‹bdd_below t› (h ha))

theorem cSup_le_iff (_: bdd_above s) (_: s ≠ ∅) : Sup s ≤ a ↔ (∀b ∈ s, b ≤ a) :=
⟨assume (_: Sup s ≤ a) (b) (_: b ∈ s),
  le_trans (le_cSup ‹bdd_above s› ‹b ∈ s›) ‹Sup s ≤ a›,
  cSup_le ‹s ≠ ∅›⟩

theorem le_cInf_iff (_: bdd_below s) (_: s ≠ ∅): a ≤ Inf s ↔ (∀b ∈ s, a ≤ b) :=
⟨assume (_: a ≤ Inf s) (b) (_: b ∈ s),
  le_trans ‹a ≤ Inf s› (cInf_le ‹bdd_below s› ‹b ∈ s›),
  le_cInf ‹s ≠ ∅›⟩

/--Introduction rule to prove that b is the supremum of s: it suffices to check that b
is larger than all elements of s, and that this is not the case of any w<b.-/
theorem cSup_intro (_: s ≠ ∅) (_: ∀a∈s, a ≤ b) (H: ∀w, w < b → (∃a∈s, w < a)) : Sup s = b :=
  have bdd_above s := ⟨b, by assumption⟩,
  have (Sup s < b) ∨ (Sup s = b) := lt_or_eq_of_le (cSup_le ‹s ≠ ∅› ‹∀a∈s, a ≤ b›),
  have ¬(Sup s < b) :=
    assume: Sup s < b,
    let ⟨a, _, _⟩ := (H (Sup s) ‹Sup s < b›) in  /- a ∈ s, Sup s < a-/
    have Sup s < Sup s := lt_of_lt_of_le ‹Sup s < a› (le_cSup ‹bdd_above s› ‹a ∈ s›),
    show false, by finish [lt_irrefl (Sup s)],
  show Sup s = b, by finish

/--Introduction rule to prove that b is the infimum of s: it suffices to check that b
is smaller than all elements of s, and that this is not the case of any w>b.-/
theorem cInf_intro (_: s ≠ ∅) (_: ∀a∈s, b ≤ a) (H: ∀w, b < w → (∃a∈s, a < w)) : Inf s = b :=
  have bdd_below s := ⟨b, by assumption⟩,
  have (b < Inf s) ∨ (b = Inf s) := lt_or_eq_of_le (le_cInf ‹s ≠ ∅› ‹∀a∈s, b ≤ a›),
  have ¬(b < Inf s) :=
    assume: b < Inf s,
    let ⟨a, _, _⟩ := (H (Inf s) ‹b < Inf s›) in  /- a ∈ s, a < Inf s-/
    have Inf s < Inf s := lt_of_le_of_lt (cInf_le ‹bdd_below s› ‹a ∈ s›) ‹a < Inf s› ,
    show false, by finish [lt_irrefl (Inf s)],
  show Inf s = b, by finish

/--When an element a of a set s is larger than all elements of the set, it is Sup s-/
theorem cSup_of_in_of_le (_: a ∈ s) (_: ∀w∈s, w ≤ a) : Sup s = a :=
  have bdd_above s := ⟨a, by assumption⟩,
  have s ≠ ∅ := ne_empty_of_mem ‹a ∈ s›,
  have A: a ≤ Sup s := le_cSup ‹bdd_above s› ‹a ∈ s›,
  have B: Sup s ≤ a := cSup_le ‹s ≠ ∅› ‹∀w∈s, w ≤ a›,
  le_antisymm B A

/--When an element a of a set s is smaller than all elements of the set, it is Inf s-/
theorem cInf_of_in_of_le (_: a ∈ s) (_: ∀w∈s, a ≤ w) : Inf s = a :=
  have bdd_below s := ⟨a, by assumption⟩,
  have s ≠ ∅ := ne_empty_of_mem ‹a ∈ s›,
  have A: Inf s ≤ a := cInf_le ‹bdd_below s› ‹a ∈ s›,
  have B: a ≤ Inf s := le_cInf ‹s ≠ ∅› ‹∀w∈s, a ≤ w›,
  le_antisymm A B

/--b < Sup s when there is an element a in s with b < a, when s is bounded above.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness above for one direction, nonemptyness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/
lemma lt_cSup_of_lt (_: bdd_above s) (_: a ∈ s) (_: b < a) : b < Sup s :=
  lt_of_lt_of_le ‹b < a› (le_cSup ‹bdd_above s› ‹a ∈ s›)

/--Inf s < b s when there is an element a in s with a < b, when s is bounded below.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness below for one direction, nonemptyness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/

lemma cInf_lt_of_lt (_: bdd_below s) (_: a ∈ s) (_: a < b) : Inf s < b :=
  lt_of_le_of_lt (cInf_le ‹bdd_below s› ‹a ∈ s›) ‹a < b›

/--The supremum of a singleton is the element of the singleton-/
@[simp] theorem cSup_singleton (a : α) : Sup {a} = a :=
  have A: a ≤ Sup {a} :=
    by apply le_cSup _ _; simp; simp,
  have B: Sup {a} ≤ a :=
    by apply cSup_le _ _; simp; simp,
  le_antisymm B A

/--The infimum of a singleton is the element of the singleton-/
@[simp] theorem cInf_singleton (a : α) : Inf {a} = a :=
  have A: Inf {a} ≤ a :=
    by apply cInf_le _ _; simp; simp,
  have B: a ≤ Inf {a} :=
    by apply le_cInf _ _; simp; simp,
  le_antisymm A B

/--If a set is bounded below and above, and nonempty, its infimum is less than or equal to
its supremum.-/
theorem cInf_le_cSup (_: bdd_below s) (_: bdd_above s) (_: s ≠ ∅) : Inf s ≤ Sup s :=
  let ⟨w, hw⟩ := exists_mem_of_ne_empty ‹s ≠ ∅› in   /-hw : w ∈ s-/
  have Inf s ≤ w := cInf_le ‹bdd_below s› ‹w ∈ s›,
  have w ≤ Sup s := le_cSup ‹bdd_above s› ‹w ∈ s›,
  le_trans ‹Inf s ≤ w› ‹w ≤ Sup s›

/--The sup of a union of sets is the max of the suprema of each subset, under the assumptions
that all sets are bounded above and nonempty.-/
theorem cSup_union (_: bdd_above s) (_: s ≠ ∅) (_: bdd_above t) (_: t ≠ ∅) :
Sup (s ∪ t) = Sup s ⊔ Sup t :=
  have A: Sup (s ∪ t) ≤ Sup s ⊔ Sup t :=
    have s ∪ t ≠ ∅ := by simp at *; finish,
    have F: ∀b∈ s∪t, b ≤ Sup s ⊔ Sup t :=
      begin
        intros,
        cases H,
        apply le_trans (le_cSup ‹bdd_above s› ‹b ∈ s›) _, simp,
        apply le_trans (le_cSup ‹bdd_above t› ‹b ∈ t›) _, simp
      end,
    cSup_le this F,
  have B: Sup s ⊔ Sup t ≤ Sup (s ∪ t) :=
    have Sup s ≤ Sup (s ∪ t) := by apply cSup_le_cSup _ ‹s ≠ ∅›; simp; finish,
    have Sup t ≤ Sup (s ∪ t) := by apply cSup_le_cSup _ ‹t ≠ ∅›; simp; finish,
    by simp; split; assumption; assumption,
  le_antisymm A B

/--The inf of a union of sets is the min of the infima of each subset, under the assumptions
that all sets are bounded below and nonempty.-/
theorem cInf_union (_: bdd_below s) (_: s ≠ ∅) (_: bdd_below t) (_: t ≠ ∅) :
Inf (s ∪ t) = Inf s ⊓ Inf t :=
  have A: Inf s ⊓ Inf t ≤ Inf (s ∪ t) :=
    have s ∪ t ≠ ∅ := by simp at *; finish,
    have F: ∀b∈ s∪t, Inf s ⊓ Inf t ≤ b :=
      begin
        intros,
        cases H,
        apply le_trans _ (cInf_le ‹bdd_below s› ‹b ∈ s›), simp,
        apply le_trans _ (cInf_le ‹bdd_below t› ‹b ∈ t›), simp
      end,
    le_cInf this F,
  have B: Inf (s ∪ t) ≤ Inf s ⊓ Inf t  :=
    have Inf (s ∪ t) ≤ Inf s := by apply cInf_le_cInf _ ‹s ≠ ∅›; simp; finish,
    have Inf (s ∪ t) ≤ Inf t := by apply cInf_le_cInf _ ‹t ≠ ∅›; simp; finish,
    by simp; split; assumption; assumption,
  le_antisymm B A

/--The supremum of an intersection of sets is bounded by the minimum of the suprema of each
set, if all sets are bounded above and nonempty.-/
theorem cSup_inter_le (_: bdd_above s) (_: bdd_above t) (_: s ∩ t ≠ ∅) :
Sup (s ∩ t) ≤ Sup s ⊓ Sup t :=
begin
  apply cSup_le ‹s ∩ t ≠ ∅› _, simp, intros b _ _, split,
  apply le_cSup ‹bdd_above s› ‹b ∈ s›,
  apply le_cSup ‹bdd_above t› ‹b ∈ t›
end

/--The infimum of an intersection of sets is bounded below by the maximum of the
infima of each set, if all sets are bounded below and nonempty.-/
theorem le_cInf_inter (_: bdd_below s) (_: bdd_below t) (_: s ∩ t ≠ ∅) :
Inf s ⊔ Inf t ≤ Inf (s ∩ t) :=
begin
  apply le_cInf ‹s ∩ t ≠ ∅› _, simp, intros b _ _, split,
  apply cInf_le ‹bdd_below s› ‹b ∈ s›,
  apply cInf_le ‹bdd_below t› ‹b ∈ t›
end

/-- The supremum of insert a s is the maximum of a and the supremum of s, if s is
nonempty and bounded above.-/
theorem cSup_insert (_: bdd_above s) (_: s ≠ ∅) : Sup (insert a s) = a ⊔ Sup s :=
  calc Sup (insert a s)
         = Sup ({a} ∪ s)   : by rw [insert_eq]
     ... = Sup {a} ⊔ Sup s : by apply cSup_union _ _ ‹bdd_above s› ‹s ≠ ∅›; simp; simp
     ... = a ⊔ Sup s       : by simp

/-- The infimum of insert a s is the minimum of a and the infimum of s, if s is
nonempty and bounded below.-/
theorem cInf_insert (_: bdd_below s) (_: s ≠ ∅) : Inf (insert a s) = a ⊓ Inf s :=
  calc Inf (insert a s)
         = Inf ({a} ∪ s)   : by rw [insert_eq]
     ... = Inf {a} ⊓ Inf s : by apply cInf_union _ _ ‹bdd_below s› ‹s ≠ ∅›; simp; simp
     ... = a ⊓ Inf s       : by simp

end conditionally_complete_lattice


section conditionally_complete_linear_order
variables [conditionally_complete_linear_order α] {s t : set α} {a b : α}

/--When b < Sup s, there is an element a in s with b < a, if s is nonempty and the order is
a linear order.-/
lemma exists_lt_of_lt_cSup (_: s ≠ ∅) (_: b < Sup s) : (∃a∈s, b < a) :=
  begin
    apply classical.by_contradiction,
    assume : ¬ (∃a∈s, b < a),
    have: Sup s ≤ b :=
      by apply cSup_le ‹s ≠ ∅› _; finish,
    apply lt_irrefl b (lt_of_lt_of_le ‹b < Sup s› ‹Sup s ≤ b›)
  end

/--When Inf s < b, there is an element a in s with a < b, if s is nonempty and the order is
a linear order.-/
lemma exists_lt_of_cInf_lt (_: s ≠ ∅) (_: Inf s < b) : (∃a∈s, a < b) :=
  begin
    apply classical.by_contradiction,
    assume : ¬ (∃a∈s, a < b),
    have: b ≤ Inf s :=
      by apply le_cInf ‹s ≠ ∅› _; finish,
    apply lt_irrefl b (lt_of_le_of_lt ‹b ≤ Inf s› ‹Inf s < b›)
  end

end conditionally_complete_linear_order

end lattice /-end of namespace lattice-/
