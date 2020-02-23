/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
Adapted from the corresponding theory for complete lattices.

Theory of conditionally complete lattices.

A conditionally complete lattice is a lattice in which every non-empty bounded subset s
has a least upper bound and a greatest lower bound, denoted below by Sup s and Inf s.
Typical examples are real, nat, int with their usual orders.

The theory is very comparable to the theory of complete lattices, except that suitable
boundedness and nonemptiness assumptions have to be added to most statements.
We introduce two predicates bdd_above and bdd_below to express this boundedness, prove
their basic properties, and then go on to prove most useful properties of Sup and Inf
in conditionally complete lattices.

To differentiate the statements between complete lattices and conditionally complete
lattices, we prefix Inf and Sup in the statements by c, giving cInf and cSup. For instance,
Inf_le is a statement in complete lattices ensuring Inf s ≤ x, while cInf_le is the same
statement in conditionally complete lattices with an additional assumption that s is
bounded below.
-/
import
  order.lattice order.complete_lattice order.bounds
  tactic.finish data.set.finite

set_option old_structure_cmd true

open set lattice

universes u v w
variables {α : Type u} {β : Type v} {ι : Sort w}


section

/-!
Extension of Sup and Inf from a preorder `α` to `with_top α` and `with_bot α`
-/

open_locale classical

noncomputable instance {α : Type*} [preorder α] [has_Sup α] : has_Sup (with_top α) :=
⟨λ S, if ⊤ ∈ S then ⊤ else
  if bdd_above (coe ⁻¹' S : set α) then ↑(Sup (coe ⁻¹' S : set α)) else ⊤⟩

noncomputable instance {α : Type*} [has_Inf α] : has_Inf (with_top α) :=
⟨λ S, if S ⊆ {⊤} then ⊤ else ↑(Inf (coe ⁻¹' S : set α))⟩

noncomputable instance {α : Type*} [has_Sup α] : has_Sup (with_bot α) :=
⟨(@with_top.lattice.has_Inf (order_dual α) _).Inf⟩

noncomputable instance {α : Type*} [preorder α] [has_Inf α] : has_Inf (with_bot α) :=
⟨(@with_top.lattice.has_Sup (order_dual α) _ _).Sup⟩

end -- section

namespace lattice
section prio
set_option default_priority 100 -- see Note [default priority]
/-- A conditionally complete lattice is a lattice in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete lattices, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class conditionally_complete_lattice (α : Type u) extends lattice α, has_Sup α, has_Inf α :=
(le_cSup : ∀s a, bdd_above s → a ∈ s → a ≤ Sup s)
(cSup_le : ∀ s a, set.nonempty s → a ∈ upper_bounds s → Sup s ≤ a)
(cInf_le : ∀s a, bdd_below s → a ∈ s → Inf s ≤ a)
(le_cInf : ∀s a, set.nonempty s → a ∈ lower_bounds s → a ≤ Inf s)

class conditionally_complete_linear_order (α : Type u)
  extends conditionally_complete_lattice α, decidable_linear_order α

class conditionally_complete_linear_order_bot (α : Type u)
  extends conditionally_complete_lattice α, decidable_linear_order α, order_bot α :=
(cSup_empty : Sup ∅ = ⊥)
end prio

/- A complete lattice is a conditionally complete lattice, as there are no restrictions
on the properties of Inf and Sup in a complete lattice.-/

@[priority 100] -- see Note [lower instance priority]
instance conditionally_complete_lattice_of_complete_lattice [complete_lattice α]:
  conditionally_complete_lattice α :=
{ le_cSup := by intros; apply le_Sup; assumption,
  cSup_le := by intros; apply Sup_le; assumption,
  cInf_le := by intros; apply Inf_le; assumption,
  le_cInf := by intros; apply le_Inf; assumption,
  ..‹complete_lattice α› }

@[priority 100] -- see Note [lower instance priority]
instance conditionally_complete_linear_order_of_complete_linear_order [complete_linear_order α]:
  conditionally_complete_linear_order α :=
{ ..lattice.conditionally_complete_lattice_of_complete_lattice, .. ‹complete_linear_order α› }

section conditionally_complete_lattice
variables [conditionally_complete_lattice α] {s t : set α} {a b : α}

theorem le_cSup (h₁ : bdd_above s) (h₂ : a ∈ s) : a ≤ Sup s :=
conditionally_complete_lattice.le_cSup s a h₁ h₂

theorem cSup_le (h₁ : s.nonempty) (h₂ : ∀b∈s, b ≤ a) : Sup s ≤ a :=
conditionally_complete_lattice.cSup_le s a h₁ h₂

theorem cInf_le (h₁ : bdd_below s) (h₂ : a ∈ s) : Inf s ≤ a :=
conditionally_complete_lattice.cInf_le s a h₁ h₂

theorem le_cInf (h₁ : s.nonempty) (h₂ : ∀b∈s, a ≤ b) : a ≤ Inf s :=
conditionally_complete_lattice.le_cInf s a h₁ h₂

theorem le_cSup_of_le (_ : bdd_above s) (hb : b ∈ s) (h : a ≤ b) : a ≤ Sup s :=
le_trans h (le_cSup ‹bdd_above s› hb)

theorem cInf_le_of_le (_ : bdd_below s) (hb : b ∈ s) (h : b ≤ a) : Inf s ≤ a :=
le_trans (cInf_le ‹bdd_below s› hb) h

theorem cSup_le_cSup (_ : bdd_above t) (_ : s.nonempty) (h : s ⊆ t) : Sup s ≤ Sup t :=
cSup_le ‹_› (assume (a) (ha : a ∈ s), le_cSup ‹bdd_above t› (h ha))

theorem cInf_le_cInf (_ : bdd_below t) (_ : s.nonempty) (h : s ⊆ t) : Inf t ≤ Inf s :=
le_cInf ‹_› (assume (a) (ha : a ∈ s), cInf_le ‹bdd_below t› (h ha))

theorem cSup_le_iff (_ : bdd_above s) (_ : s.nonempty) : Sup s ≤ a ↔ (∀b ∈ s, b ≤ a) :=
⟨assume (_ : Sup s ≤ a) (b) (_ : b ∈ s),
  le_trans (le_cSup ‹bdd_above s› ‹b ∈ s›) ‹Sup s ≤ a›,
  cSup_le ‹_›⟩

theorem le_cInf_iff (_ : bdd_below s) (_ : s.nonempty) : a ≤ Inf s ↔ (∀b ∈ s, a ≤ b) :=
⟨assume (_ : a ≤ Inf s) (b) (_ : b ∈ s),
  le_trans ‹a ≤ Inf s› (cInf_le ‹bdd_below s› ‹b ∈ s›),
  le_cInf ‹_›⟩

lemma cSup_lower_bounds_eq_cInf {s : set α} (h : bdd_below s) (hs : s.nonempty) :
  Sup (lower_bounds s) = Inf s :=
le_antisymm
  (cSup_le h $ assume a ha, le_cInf hs ha)
  (le_cSup (hs.mono $ λ a ha y hy, hy ha) $ assume x hx, cInf_le h hx)

lemma cInf_upper_bounds_eq_cSup {s : set α} (h : bdd_above s) (hs : s.nonempty) :
  Inf (upper_bounds s) = Sup s :=
le_antisymm
  (cInf_le (hs.mono $ assume a ha y hy, hy ha) $ assume x hx, le_cSup h hx)
  (le_cInf h $ assume a ha, cSup_le hs ha)

/--Introduction rule to prove that b is the supremum of s: it suffices to check that b
is larger than all elements of s, and that this is not the case of any w<b.-/
theorem cSup_intro (_ : s.nonempty) (_ : ∀a∈s, a ≤ b) (H : ∀w, w < b → (∃a∈s, w < a)) : Sup s = b :=
have bdd_above s := ⟨b, by assumption⟩,
have (Sup s < b) ∨ (Sup s = b) := lt_or_eq_of_le (cSup_le ‹_› ‹∀a∈s, a ≤ b›),
have ¬(Sup s < b) :=
  assume: Sup s < b,
  let ⟨a, _, _⟩ := (H (Sup s) ‹Sup s < b›) in  /- a ∈ s, Sup s < a-/
  have Sup s < Sup s := lt_of_lt_of_le ‹Sup s < a› (le_cSup ‹bdd_above s› ‹a ∈ s›),
  show false, by finish [lt_irrefl (Sup s)],
show Sup s = b, by finish

/--Introduction rule to prove that b is the infimum of s: it suffices to check that b
is smaller than all elements of s, and that this is not the case of any w>b.-/
theorem cInf_intro (_ : s.nonempty) (_ : ∀a∈s, b ≤ a) (H : ∀w, b < w → (∃a∈s, a < w)) : Inf s = b :=
have bdd_below s := ⟨b, by assumption⟩,
have (b < Inf s) ∨ (b = Inf s) := lt_or_eq_of_le (le_cInf ‹_› ‹∀a∈s, b ≤ a›),
have ¬(b < Inf s) :=
  assume: b < Inf s,
  let ⟨a, _, _⟩ := (H (Inf s) ‹b < Inf s›) in  /- a ∈ s, a < Inf s-/
  have Inf s < Inf s := lt_of_le_of_lt (cInf_le ‹bdd_below s› ‹a ∈ s›) ‹a < Inf s› ,
  show false, by finish [lt_irrefl (Inf s)],
show Inf s = b, by finish

/--When an element a of a set s is larger than all other elements of the set, it is Sup s-/
theorem cSup_of_mem_of_le (_ : a ∈ s) (_ : ∀w∈s, w ≤ a) : Sup s = a :=
have bdd_above s := ⟨a, by assumption⟩,
have A : a ≤ Sup s := le_cSup ‹bdd_above s› ‹a ∈ s›,
have B : Sup s ≤ a := cSup_le ⟨a, ‹_›⟩ ‹∀w∈s, w ≤ a›,
le_antisymm B A

/--When an element a of a set s is smaller than all other elements of the set, it is Inf s-/
theorem cInf_of_mem_of_le (_ : a ∈ s) (_ : ∀w∈s, a ≤ w) : Inf s = a :=
have bdd_below s := ⟨a, by assumption⟩,
have A : Inf s ≤ a := cInf_le ‹bdd_below s› ‹a ∈ s›,
have B : a ≤ Inf s := le_cInf ⟨a, ‹_›⟩ ‹∀w∈s, a ≤ w›,
le_antisymm A B

/--b < Sup s when there is an element a in s with b < a, when s is bounded above.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness above for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/
lemma lt_cSup_of_lt (_ : bdd_above s) (_ : a ∈ s) (_ : b < a) : b < Sup s :=
lt_of_lt_of_le ‹b < a› (le_cSup ‹bdd_above s› ‹a ∈ s›)

/--Inf s < b when there is an element a in s with a < b, when s is bounded below.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness below for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/

lemma cInf_lt_of_lt (_ : bdd_below s) (_ : a ∈ s) (_ : a < b) : Inf s < b :=
lt_of_le_of_lt (cInf_le ‹bdd_below s› ‹a ∈ s›) ‹a < b›

/--The supremum of a singleton is the element of the singleton-/
@[simp] theorem cSup_singleton (a : α) : Sup {a} = a :=
cSup_of_mem_of_le (mem_singleton a)
  (λ b hb, set.eq_of_mem_singleton hb ▸ le_refl b)

/--The infimum of a singleton is the element of the singleton-/
@[simp] theorem cInf_singleton (a : α) : Inf {a} = a :=
cInf_of_mem_of_le (mem_singleton a)
  (λ b hb, set.eq_of_mem_singleton hb ▸ le_refl b)

/--If a set is bounded below and above, and nonempty, its infimum is less than or equal to
its supremum.-/
theorem cInf_le_cSup (_ : bdd_below s) (_ : bdd_above s) (_ : s.nonempty) : Inf s ≤ Sup s :=
let ⟨w, hw⟩ := ‹s.nonempty› in   /-hw : w ∈ s-/
have Inf s ≤ w := cInf_le ‹bdd_below s› ‹w ∈ s›,
have w ≤ Sup s := le_cSup ‹bdd_above s› ‹w ∈ s›,
le_trans ‹Inf s ≤ w› ‹w ≤ Sup s›

/--The sup of a union of two sets is the max of the suprema of each subset, under the assumptions
that all sets are bounded above and nonempty.-/
theorem cSup_union (_ : bdd_above s) (sne : s.nonempty) (_ : bdd_above t) (tne : t.nonempty) :
Sup (s ∪ t) = Sup s ⊔ Sup t :=
have A : Sup (s ∪ t) ≤ Sup s ⊔ Sup t :=
  have (s ∪ t).nonempty := sne.inl,
  have F : ∀b∈ s∪t, b ≤ Sup s ⊔ Sup t :=
    begin
      intros,
      cases H,
      apply le_trans (le_cSup ‹bdd_above s› ‹b ∈ s›) _, simp only [lattice.le_sup_left],
      apply le_trans (le_cSup ‹bdd_above t› ‹b ∈ t›) _, simp only [lattice.le_sup_right]
    end,
  cSup_le this F,
have B : Sup s ⊔ Sup t ≤ Sup (s ∪ t) :=
  have Sup s ≤ Sup (s ∪ t),
    from cSup_le_cSup (bdd_above_union.2 ⟨‹_›, ‹_›⟩) sne (set.subset_union_left _ _),
  have Sup t ≤ Sup (s ∪ t),
    from cSup_le_cSup (bdd_above_union.2 ⟨‹_›, ‹_›⟩) tne (set.subset_union_right _ _),
  by simp only [lattice.sup_le_iff]; split; assumption,
le_antisymm A B

/--The inf of a union of two sets is the min of the infima of each subset, under the assumptions
that all sets are bounded below and nonempty.-/
theorem cInf_union (_ : bdd_below s) (sne : s.nonempty) (_ : bdd_below t) (tne : t.nonempty) :
Inf (s ∪ t) = Inf s ⊓ Inf t :=
have A : Inf s ⊓ Inf t ≤ Inf (s ∪ t) :=
  have (s ∪ t).nonempty, from sne.inl,
  have F : ∀b∈ s∪t, Inf s ⊓ Inf t ≤ b :=
    begin
      intros,
      cases H,
      apply le_trans _ (cInf_le ‹bdd_below s› ‹b ∈ s›), simp only [lattice.inf_le_left],
      apply le_trans _ (cInf_le ‹bdd_below t› ‹b ∈ t›), simp only [lattice.inf_le_right]
    end,
  le_cInf this F,
have B : Inf (s ∪ t) ≤ Inf s ⊓ Inf t  :=
  have Inf (s ∪ t) ≤ Inf s,
    from cInf_le_cInf (bdd_below_union.2 ⟨‹_›, ‹_›⟩) sne (set.subset_union_left _ _),
  have Inf (s ∪ t) ≤ Inf t,
    from cInf_le_cInf (bdd_below_union.2 ⟨‹_›, ‹_›⟩) tne (set.subset_union_right _ _),
  by simp only [lattice.le_inf_iff]; split; assumption; assumption,
le_antisymm B A

/--The supremum of an intersection of two sets is bounded by the minimum of the suprema of each
set, if all sets are bounded above and nonempty.-/
theorem cSup_inter_le (_ : bdd_above s) (_ : bdd_above t) (hst : (s ∩ t).nonempty) :
Sup (s ∩ t) ≤ Sup s ⊓ Sup t :=
begin
  apply cSup_le hst, simp only [lattice.le_inf_iff, and_imp, set.mem_inter_eq], intros b _ _, split,
  apply le_cSup ‹bdd_above s› ‹b ∈ s›,
  apply le_cSup ‹bdd_above t› ‹b ∈ t›
end

/--The infimum of an intersection of two sets is bounded below by the maximum of the
infima of each set, if all sets are bounded below and nonempty.-/
theorem le_cInf_inter (_ : bdd_below s) (_ : bdd_below t) (hst : (s ∩ t).nonempty) :
Inf s ⊔ Inf t ≤ Inf (s ∩ t) :=
begin
  apply le_cInf hst, simp only [and_imp, set.mem_inter_eq, lattice.sup_le_iff], intros b _ _, split,
  apply cInf_le ‹bdd_below s› ‹b ∈ s›,
  apply cInf_le ‹bdd_below t› ‹b ∈ t›
end

/-- The supremum of insert a s is the maximum of a and the supremum of s, if s is
nonempty and bounded above.-/
theorem cSup_insert (_ : bdd_above s) (sne : s.nonempty) : Sup (insert a s) = a ⊔ Sup s :=
calc Sup (insert a s)
        = Sup ({a} ∪ s)   : by rw [insert_eq]
    ... = Sup {a} ⊔ Sup s : by apply cSup_union _ _ ‹bdd_above s› sne; simp only [ne.def, not_false_iff, set.singleton_nonempty, bdd_above_singleton]
    ... = a ⊔ Sup s       : by simp only [eq_self_iff_true, lattice.cSup_singleton]

/-- The infimum of insert a s is the minimum of a and the infimum of s, if s is
nonempty and bounded below.-/
theorem cInf_insert (_ : bdd_below s) (sne : s.nonempty) : Inf (insert a s) = a ⊓ Inf s :=
calc Inf (insert a s)
        = Inf ({a} ∪ s)   : by rw [insert_eq]
    ... = Inf {a} ⊓ Inf s : by apply cInf_union _ _ ‹bdd_below s› sne; simp only [ne.def, not_false_iff, set.singleton_nonempty, bdd_below_singleton]
    ... = a ⊓ Inf s       : by simp only [eq_self_iff_true, lattice.cInf_singleton]

@[simp] lemma cInf_interval : Inf {b | a ≤ b} = a :=
cInf_of_mem_of_le (by simp only [set.mem_set_of_eq]) (λw Hw, by simp only [set.mem_set_of_eq] at Hw; apply Hw)

@[simp] lemma cSup_interval : Sup {b | b ≤ a} = a :=
cSup_of_mem_of_le (by simp only [set.mem_set_of_eq]) (λw Hw, by simp only [set.mem_set_of_eq] at Hw; apply Hw)

/--The indexed supremum of two functions are comparable if the functions are pointwise comparable-/
lemma csupr_le_csupr {f g : ι → α} (B : bdd_above (range g)) (H : ∀x, f x ≤ g x) :
  supr f ≤ supr g :=
begin
  classical, by_cases hι : nonempty ι,
  { have Rf : (range f).nonempty := range_nonempty _,
    apply cSup_le Rf,
    rintros y ⟨x, rfl⟩,
    have : g x ∈ range g := ⟨x, rfl⟩,
    exact le_cSup_of_le B this (H x) },
  { have Rf : range f = ∅, from range_eq_empty.2 hι,
    have Rg : range g = ∅, from range_eq_empty.2 hι,
    unfold supr, rw [Rf, Rg] }
end

/--The indexed supremum of a function is bounded above by a uniform bound-/
lemma csupr_le [nonempty ι] {f : ι → α} {c : α} (H : ∀x, f x ≤ c) : supr f ≤ c :=
cSup_le (range_nonempty f) (by rwa forall_range_iff)

/--The indexed supremum of a function is bounded below by the value taken at one point-/
lemma le_csupr {f : ι → α} (H : bdd_above (range f)) {c : ι} : f c ≤ supr f :=
le_cSup H (mem_range_self _)

/--The indexed infimum of two functions are comparable if the functions are pointwise comparable-/
lemma cinfi_le_cinfi {f g : ι → α} (B : bdd_below (range f)) (H : ∀x, f x ≤ g x) :
  infi f ≤ infi g :=
begin
  classical, by_cases hι : nonempty ι,
  { have Rg : (range g).nonempty, from range_nonempty _,
    apply le_cInf Rg,
    rintros y ⟨x, rfl⟩,
    have : f x ∈ range f := ⟨x, rfl⟩,
    exact cInf_le_of_le B this (H x) },
  { have Rf : range f = ∅, from range_eq_empty.2 hι,
    have Rg : range g = ∅, from range_eq_empty.2 hι,
    unfold infi, rw [Rf, Rg] }
end

/--The indexed minimum of a function is bounded below by a uniform lower bound-/
lemma le_cinfi [nonempty ι] {f : ι → α} {c : α} (H : ∀x, c ≤ f x) : c ≤ infi f :=
le_cInf (range_nonempty f) (by rwa forall_range_iff)

/--The indexed infimum of a function is bounded above by the value taken at one point-/
lemma cinfi_le {f : ι → α} (H : bdd_below (range f)) {c : ι} : infi f ≤ f c :=
cInf_le H (mem_range_self _)

lemma is_lub_cSup {s : set α} (ne : s.nonempty) (H : bdd_above s) : is_lub s (Sup s) :=
⟨assume x, le_cSup H, assume x, cSup_le ne⟩

lemma is_glb_cInf {s : set α} (ne : s.nonempty) (H : bdd_below s) : is_glb s (Inf s) :=
⟨assume x, cInf_le H, assume x, le_cInf ne⟩

@[simp] theorem cinfi_const [hι : nonempty ι] {a : α} : (⨅ b:ι, a) = a :=
begin
  refine hι.elim (λ x, _),
  refine le_antisymm (@cinfi_le _ _ _ _ _ x) (le_cinfi (λi, _root_.le_refl _)),
  rw range_const,
  exact bdd_below_singleton
end

@[simp] theorem csupr_const [hι : nonempty ι] {a : α} : (⨆ b:ι, a) = a :=
begin
  refine hι.elim (λ x, _),
  refine le_antisymm (csupr_le (λi, _root_.le_refl _)) (@le_csupr _ _ _ (λ b:ι, a) _ x),
  rw range_const,
  exact bdd_above_singleton
end

end conditionally_complete_lattice


section conditionally_complete_linear_order
variables [conditionally_complete_linear_order α] {s t : set α} {a b : α}

/-- When b < Sup s, there is an element a in s with b < a, if s is nonempty and the order is
a linear order. -/
lemma exists_lt_of_lt_cSup (hs : s.nonempty) (hb : b < Sup s) : ∃a∈s, b < a :=
begin
  classical, contrapose! hb,
  exact cSup_le hs hb
end

/--
Indexed version of the above lemma `exists_lt_of_lt_cSup`.
When `b < supr f`, there is an element `i` such that `b < f i`.
-/
lemma exists_lt_of_lt_csupr [nonempty ι] {f : ι → α} (h : b < supr f) :
  ∃i, b < f i :=
let ⟨_, ⟨i, rfl⟩, h⟩ := exists_lt_of_lt_cSup (range_nonempty f) h in ⟨i, h⟩

/--When Inf s < b, there is an element a in s with a < b, if s is nonempty and the order is
a linear order.-/
lemma exists_lt_of_cInf_lt (hs : s.nonempty) (hb : Inf s < b) : ∃a∈s, a < b :=
begin
  classical, contrapose! hb,
  exact le_cInf hs hb
end

/--
Indexed version of the above lemma `exists_lt_of_cInf_lt`
When `infi f < a`, there is an element `i` such that `f i < a`.
-/
lemma exists_lt_of_cinfi_lt [nonempty ι] {f : ι → α} (h : infi f < a) :
  (∃i, f i < a) :=
let ⟨_, ⟨i, rfl⟩, h⟩ := exists_lt_of_cInf_lt (range_nonempty f) h in ⟨i, h⟩

/--Introduction rule to prove that b is the supremum of s: it suffices to check that
1) b is an upper bound
2) every other upper bound b' satisfies b ≤ b'.-/
theorem cSup_intro' (_ : s.nonempty)
  (h_is_ub : ∀ a ∈ s, a ≤ b) (h_b_le_ub : ∀ub, (∀ a ∈ s, a ≤ ub) → (b ≤ ub)) : Sup s = b :=
le_antisymm
  (show Sup s ≤ b, from cSup_le ‹s.nonempty› h_is_ub)
  (show b ≤ Sup s, from h_b_le_ub _ $ assume a, le_cSup ⟨b, h_is_ub⟩)

end conditionally_complete_linear_order

section conditionally_complete_linear_order_bot

lemma cSup_empty [conditionally_complete_linear_order_bot α] : (Sup ∅ : α) = ⊥ :=
conditionally_complete_linear_order_bot.cSup_empty α

end conditionally_complete_linear_order_bot

section

open_locale classical

noncomputable instance : has_Inf ℕ :=
⟨λs, if h : ∃n, n ∈ s then @nat.find (λn, n ∈ s) _ h else 0⟩

noncomputable instance : has_Sup ℕ :=
⟨λs, if h : ∃n, ∀a∈s, a ≤ n then @nat.find (λn, ∀a∈s, a ≤ n) _ h else 0⟩

lemma Inf_nat_def {s : set ℕ} (h : ∃n, n ∈ s) : Inf s = @nat.find (λn, n ∈ s) _ h :=
dif_pos _

lemma Sup_nat_def {s : set ℕ} (h : ∃n, ∀a∈s, a ≤ n) :
  Sup s = @nat.find (λn, ∀a∈s, a ≤ n) _ h :=
dif_pos _

/-- This instance is necessary, otherwise the lattice operations would be derived via
conditionally_complete_linear_order_bot and marked as noncomputable. -/
instance : lattice ℕ := infer_instance

noncomputable instance : conditionally_complete_linear_order_bot ℕ :=
{ Sup := Sup, Inf := Inf,
  le_cSup    := assume s a hb ha, by rw [Sup_nat_def hb]; revert a ha; exact @nat.find_spec _ _ hb,
  cSup_le    := assume s a hs ha, by rw [Sup_nat_def ⟨a, ha⟩]; exact nat.find_min' _ ha,
  le_cInf    := assume s a hs hb,
    by rw [Inf_nat_def hs]; exact hb (@nat.find_spec (λn, n ∈ s) _ _),
  cInf_le    := assume s a hb ha, by rw [Inf_nat_def ⟨a, ha⟩]; exact nat.find_min' _ ha,
  cSup_empty :=
  begin
    simp only [Sup_nat_def, set.mem_empty_eq, forall_const, forall_prop_of_false, not_false_iff, exists_const],
    apply bot_unique (nat.find_min' _ _),
    trivial
  end,
  .. (infer_instance : order_bot ℕ), .. (infer_instance : lattice ℕ),
  .. (infer_instance : decidable_linear_order ℕ) }

end

end lattice /-end of namespace lattice-/

namespace with_top
open lattice
open_locale classical

variables [conditionally_complete_linear_order_bot α]

/-- The Sup of a non-empty set is its least upper bound for a conditionally
complete lattice with a top. -/
lemma is_lub_Sup' {β : Type*} [conditionally_complete_lattice β]
  {s : set (with_top β)} (hs : s.nonempty) : is_lub s (Sup s) :=
begin
  split,
  { show ite _ _ _ ∈ _,
    split_ifs,
    { intros _ _, exact le_top },
    { rintro (⟨⟩|a) ha,
      { contradiction },
      apply some_le_some.2,
      exact le_cSup h_1 ha },
    { intros _ _, exact le_top } },
  { show ite _ _ _ ∈ _,
    split_ifs,
    { rintro (⟨⟩|a) ha,
      { exact _root_.le_refl _ },
      { exact false.elim (not_top_le_coe a (ha h)) } },
    { rintro (⟨⟩|b) hb,
      { exact le_top },
      refine some_le_some.2 (cSup_le _ _),
      { rcases hs with ⟨⟨⟩|b, hb⟩,
        { exact absurd hb h },
        { exact ⟨b, hb⟩ } },
      { intros a ha, exact some_le_some.1 (hb ha) } },
    { rintro (⟨⟩|b) hb,
      { exact _root_.le_refl _ },
      { exfalso, apply h_1, use b, intros a ha, exact some_le_some.1 (hb ha) } } }
end

lemma is_lub_Sup (s : set (with_top α)) : is_lub s (Sup s) :=
begin
  cases s.eq_empty_or_nonempty with hs hs,
  { rw hs,
    show is_lub ∅ (ite _ _ _),
    split_ifs,
    { cases h },
    { rw [preimage_empty, cSup_empty], exact is_lub_empty },
    { exfalso, apply h_1, use ⊥, rintro a ⟨⟩ } },
  exact is_lub_Sup' hs,
end

/-- The Inf of a bounded-below set is its greatest lower bound for a conditionally
complete lattice with a top. -/
lemma is_glb_Inf' {β : Type*} [conditionally_complete_lattice β]
  {s : set (with_top β)} (hs : bdd_below s) : is_glb s (Inf s) :=
begin
  split,
  { show ite _ _ _ ∈ _,
    split_ifs,
    { intros a ha, exact top_le_iff.2 (set.mem_singleton_iff.1 (h ha)) },
    { rintro (⟨⟩|a) ha,
      { exact le_top },
      refine some_le_some.2 (cInf_le _ ha),
      rcases hs with ⟨⟨⟩|b, hb⟩,
      { exfalso,
        apply h,
        intros c hc,
        rw [mem_singleton_iff, ←top_le_iff],
        exact hb hc },
      use b,
      intros c hc,
      exact some_le_some.1 (hb hc) } },
  { show ite _ _ _ ∈ _,
    split_ifs,
    { intros _ _, exact le_top },
    { rintro (⟨⟩|a) ha,
      { exfalso, apply h, intros b hb, exact set.mem_singleton_iff.2 (top_le_iff.1 (ha hb)) },
      { refine some_le_some.2 (le_cInf _ _),
        { classical, contrapose! h,
          rintros (⟨⟩|a) ha,
          { exact mem_singleton ⊤ },
          { exact (h ⟨a, ha⟩).elim }},
        { intros b hb,
          rw ←some_le_some,
          exact ha hb } } } }
end

lemma is_glb_Inf (s : set (with_top α)) : is_glb s (Inf s) :=
begin
  by_cases hs : bdd_below s,
  { exact is_glb_Inf' hs },
  { exfalso, apply hs, use ⊥, intros _ _, exact bot_le },
end

noncomputable instance : complete_linear_order (with_top α) :=
{ Sup := Sup, le_Sup := assume s, (is_lub_Sup s).1, Sup_le := assume s, (is_lub_Sup s).2,
  Inf := Inf, le_Inf := assume s, (is_glb_Inf s).2, Inf_le := assume s, (is_glb_Inf s).1,
  decidable_le := classical.dec_rel _,
  .. with_top.linear_order, ..with_top.lattice, ..with_top.order_top, ..with_top.order_bot }

lemma coe_Sup {s : set α} (hb : bdd_above s) : (↑(Sup s) : with_top α) = (⨆a∈s, ↑a) :=
begin
  cases s.eq_empty_or_nonempty with hs hs,
  { rw [hs, cSup_empty], simp only [set.mem_empty_eq, lattice.supr_bot, lattice.supr_false], refl },
  apply le_antisymm,
  { refine ((coe_le_iff _ _).2 $ assume b hb, cSup_le hs $ assume a has, coe_le_coe.1 $ hb ▸ _),
    exact (le_supr_of_le a $ le_supr_of_le has $ _root_.le_refl _) },
  { exact (supr_le $ assume a, supr_le $ assume ha, coe_le_coe.2 $ le_cSup hb ha) }
end

lemma coe_Inf {s : set α} (hs : s.nonempty) : (↑(Inf s) : with_top α) = (⨅a∈s, ↑a) :=
let ⟨x, hx⟩ := hs in
have (⨅a∈s, ↑a : with_top α) ≤ x, from infi_le_of_le x $ infi_le_of_le hx $ _root_.le_refl _,
let ⟨r, r_eq, hr⟩ := (le_coe_iff _ _).1 this in
le_antisymm
  (le_infi $ assume a, le_infi $ assume ha, coe_le_coe.2 $ cInf_le (bdd_below_bot s) ha)
  begin
    refine (r_eq.symm ▸ coe_le_coe.2 $ le_cInf hs $ assume a has, coe_le_coe.1 $ _),
    refine (r_eq ▸ infi_le_of_le a _),
    exact (infi_le_of_le has $ _root_.le_refl _),
  end

end with_top

namespace enat
open_locale classical
open lattice

noncomputable instance : complete_linear_order enat :=
{ Sup := λ s, with_top_equiv.symm $ Sup (with_top_equiv '' s),
  Inf := λ s, with_top_equiv.symm $ Inf (with_top_equiv '' s),
  le_Sup := by intros; rw ← with_top_equiv_le; simp; apply le_Sup _; simpa,
  Inf_le := by intros; rw ← with_top_equiv_le; simp; apply Inf_le _; simpa,
  Sup_le := begin
    intros s a h1,
    rw [← with_top_equiv_le, with_top_equiv.right_inverse_symm],
    apply Sup_le _,
    rintros b ⟨x, h2, rfl⟩,
    rw with_top_equiv_le,
    apply h1,
    assumption
  end,
  le_Inf := begin
    intros s a h1,
    rw [← with_top_equiv_le, with_top_equiv.right_inverse_symm],
    apply le_Inf _,
    rintros b ⟨x, h2, rfl⟩,
    rw with_top_equiv_le,
    apply h1,
    assumption
  end,
  ..enat.decidable_linear_order,
  ..enat.lattice.bounded_lattice }

end enat

section order_dual
open lattice

instance (α : Type*) [conditionally_complete_lattice α] :
  conditionally_complete_lattice (order_dual α) :=
{ le_cSup := @cInf_le α _,
  cSup_le := @le_cInf α _,
  le_cInf := @cSup_le α _,
  cInf_le := @le_cSup α _,
  ..order_dual.lattice.has_Inf α,
  ..order_dual.lattice.has_Sup α,
  ..order_dual.lattice.lattice α }

instance (α : Type*) [conditionally_complete_linear_order α] :
  conditionally_complete_linear_order (order_dual α) :=
{ ..order_dual.lattice.conditionally_complete_lattice α,
  ..order_dual.decidable_linear_order α }

end order_dual

section with_top_bot

/-! ### Complete lattice structure on `with_top (with_bot α)`

If `α` is a `conditionally_complete_lattice`, then we show that `with_top α` and `with_bot α`
also inherit the structure of conditionally complete lattices. Furthermore, we show
that `with_top (with_bot α)` naturally inherits the structure of a complete lattice. Note that
for α a conditionally complete lattice, `Sup` and `Inf` both return junk values
for sets which are empty or unbounded. The extension of `Sup` to `with_top α` fixes
the unboundedness problem and the extension to `with_bot α` fixes the problem with
the empty set.

This result can be used to show that the extended reals [-∞, ∞] are a complete lattice.
-/

open lattice

open_locale classical

/-- Adding a top element to a conditionally complete lattice gives a conditionally complete lattice -/
noncomputable instance with_top.conditionally_complete_lattice
  {α : Type*} [conditionally_complete_lattice α] :
  conditionally_complete_lattice (with_top α) :=
{ le_cSup := λ S a hS haS, (with_top.is_lub_Sup' ⟨a, haS⟩).1 haS,
  cSup_le := λ S a hS haS, (with_top.is_lub_Sup' hS).2 haS,
  cInf_le := λ S a hS haS, (with_top.is_glb_Inf' hS).1 haS,
  le_cInf := λ S a hS haS, (with_top.is_glb_Inf' ⟨a, haS⟩).2 haS,
  ..with_top.lattice,
  ..with_top.lattice.has_Sup,
  ..with_top.lattice.has_Inf }

/-- Adding a bottom element to a conditionally complete lattice gives a conditionally complete lattice -/
noncomputable instance with_bot.conditionally_complete_lattice
  {α : Type*} [conditionally_complete_lattice α] :
  conditionally_complete_lattice (with_bot α) :=
{ le_cSup := (@with_top.conditionally_complete_lattice (order_dual α) _).cInf_le,
  cSup_le := (@with_top.conditionally_complete_lattice (order_dual α) _).le_cInf,
  cInf_le := (@with_top.conditionally_complete_lattice (order_dual α) _).le_cSup,
  le_cInf := (@with_top.conditionally_complete_lattice (order_dual α) _).cSup_le,
  ..with_bot.lattice,
  ..with_bot.lattice.has_Sup,
  ..with_bot.lattice.has_Inf }

/-- Adding a bottom and a top to a conditionally complete lattice gives a bounded lattice-/
noncomputable instance {α : Type*} [conditionally_complete_lattice α] : bounded_lattice (with_top (with_bot α)) :=
{ ..with_top.order_bot,
  ..with_top.order_top,
  ..conditionally_complete_lattice.to_lattice _ }

theorem with_bot.cSup_empty {α : Type*} [conditionally_complete_lattice α] :
  Sup (∅ : set (with_bot α)) = ⊥ :=
begin
  show ite _ _ _ = ⊥,
  split_ifs; finish,
end

noncomputable instance {α : Type*} [conditionally_complete_lattice α] :
  complete_lattice (with_top (with_bot α)) :=
{ le_Sup := λ S a haS, (with_top.is_lub_Sup' ⟨a, haS⟩).1 haS,
  Sup_le := λ S a ha,
    begin
      cases S.eq_empty_or_nonempty with h,
      { show ite _ _ _ ≤ a,
        split_ifs,
        { rw h at h_1, cases h_1 },
        { convert bot_le, convert with_bot.cSup_empty, rw h, refl },
        { exfalso, apply h_2, use ⊥, rw h, rintro b ⟨⟩ } },
      { refine (with_top.is_lub_Sup' h).2 ha }
    end,
  Inf_le := λ S a haS,
    show ite _ _ _ ≤ a,
    begin
      split_ifs,
      { cases a with a, exact _root_.le_refl _,
        cases (h haS); tauto },
      { cases a,
        { exact le_top },
        { apply with_top.some_le_some.2, refine cInf_le _ haS, use ⊥, intros b hb, exact bot_le } }
    end,
  le_Inf := λ S a haS, (with_top.is_glb_Inf' ⟨a, haS⟩).2 haS,
  ..with_top.lattice.has_Inf,
  ..with_top.lattice.has_Sup,
  ..with_top.lattice.bounded_lattice }

end with_top_bot
