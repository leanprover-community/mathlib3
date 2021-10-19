/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.list.basic

/-!
# A computable model of ZFA without infinity

In this file we define finite hereditary lists. This is useful for calculations in naive set theory.

We distinguish two kinds of ZFA lists:
* Atoms. Directly correspond to an element of the original type.
* Proper ZFA lists. Can thought of (but aren't implemented) as a list of ZFA lists (not necessarily
  proper).

For example, `lists ℕ` contains stuff like `23`, `[]`, `[37]`, `[1, [[2], 3], 4]`.

## Implementation note

As we want to be able to append both atoms and proper ZFA lists to proper ZFA lists, it's handy that
atoms and proper ZFA lists belong to the same type, even though atoms of `α` could be modelled as
`α` directly. But we don't want to be able to append anything to atoms.

This calls for a two-steps definition of ZFA lists:
* First, define ZFA prelists as atoms and proper ZFA prelists. Those proper ZFA prelists are defined
  by inductive appending of (not necessarily proper) ZFA lists.
* Second, define ZFA lists by rubbing out the distinction between atoms and proper lists.

## Main declarations

* `lists' α ff`: Atoms as ZFA prelists. Basically a copy of `α`.
* `lists' α tt`: Proper ZFA prelists. Defined inductively from the empty ZFA prelist (`lists'.nil`)
  and from appending a ZFA prelist to a proper ZFA prelist (`lists'.cons a l`).
* `lists α`: ZFA lists. Sum of the atoms and proper ZFA prelists.

## TODO

The next step is to define ZFA sets as lists quotiented by `lists.equiv`.
(-/

variables {α : Type*}

/-- Prelists, helper type to define `lists`. `lists' α ff` are the "atoms", a copy of `α`.
`lists' α tt` are the "proper" ZFA prelists, inductively defined from the empty ZFA prelist and from
appending a ZFA prelist to a proper ZFA prelist. It is made so that you can't append anything to an
atom while having only one appending function for appending both atoms and proper ZFC prelists to a
proper ZFA prelist. -/
@[derive decidable_eq]
inductive {u} lists' (α : Type u) : bool → Type u
| atom : α → lists' ff
| nil : lists' tt
| cons' {b} : lists' b → lists' tt → lists' tt

/-- Hereditarily finite list, aka ZFA list. A ZFA list is either an "atom" (`b = ff`), corresponding
to an element of `α`, or a "proper" ZFA list, inductively defined from the empty ZFA list and from
appending a ZFA list to a proper ZFA list. -/
def lists (α : Type*) := Σ b, lists' α b

namespace lists'

instance [inhabited α] : ∀ b, inhabited (lists' α b)
| tt := ⟨nil⟩
| ff := ⟨atom (default _)⟩

/-- Appending a ZFA list to a proper ZFA prelist. -/
def cons : lists α → lists' α tt → lists' α tt
| ⟨b, a⟩ l := cons' a l

/-- Converts a ZFA prelist to a `list` of ZFA lists. Atoms are sent to `[]`. -/
@[simp] def to_list : ∀ {b}, lists' α b → list (lists α)
| _ (atom a)    := []
| _ nil         := []
| _ (cons' a l) := ⟨_, a⟩ :: l.to_list

@[simp] theorem to_list_cons (a : lists α) (l) :
  to_list (cons a l) = a :: l.to_list :=
by cases a; simp [cons]

/-- Converts a `list` of ZFA lists to a proper ZFA prelist. -/
@[simp] def of_list : list (lists α) → lists' α tt
| []       := nil
| (a :: l) := cons a (of_list l)

@[simp] theorem to_of_list (l : list (lists α)) : to_list (of_list l) = l :=
by induction l; simp *

@[simp] theorem of_to_list : ∀ (l : lists' α tt), of_list (to_list l) = l :=
suffices ∀ b (h : tt = b) (l : lists' α b),
  let l' : lists' α tt := by rw h; exact l in
  of_list (to_list l') = l', from this _ rfl,
λ b h l, begin
  induction l, {cases h}, {exact rfl},
  case lists'.cons' : b a l IH₁ IH₂ {
    intro, change l' with cons' a l,
    simpa [cons] using IH₂ rfl }
end

end lists'

mutual inductive lists.equiv, lists'.subset
with lists.equiv : lists α → lists α → Prop
| refl (l) : lists.equiv l l
| antisymm {l₁ l₂ : lists' α tt} :
  lists'.subset l₁ l₂ → lists'.subset l₂ l₁ → lists.equiv ⟨_, l₁⟩ ⟨_, l₂⟩
with lists'.subset : lists' α tt → lists' α tt → Prop
| nil {l} : lists'.subset lists'.nil l
| cons {a a' l l'} : lists.equiv a a' → a' ∈ lists'.to_list l' →
  lists'.subset l l' → lists'.subset (lists'.cons a l) l'
local infix ` ~ `:50 := lists.equiv

/-- Equivalence of ZFA lists. Defined inductively. -/
add_decl_doc lists.equiv

/-- Subset relation for ZFA lists. Defined inductively. -/
add_decl_doc lists'.subset

namespace lists'

instance : has_subset (lists' α tt) := ⟨lists'.subset⟩

/-- ZFA prelist membership. A ZFA list is in a ZFA prelist if some element of this ZFA prelist is
equivalent as a ZFA list to this ZFA list. -/
instance {b} : has_mem (lists α) (lists' α b) :=
⟨λ a l, ∃ a' ∈ l.to_list, a ~ a'⟩

theorem mem_def {b a} {l : lists' α b} :
  a ∈ l ↔ ∃ a' ∈ l.to_list, a ~ a' := iff.rfl

@[simp] theorem mem_cons {a y l} : a ∈ @cons α y l ↔ a ~ y ∨ a ∈ l :=
by simp [mem_def, or_and_distrib_right, exists_or_distrib]

theorem cons_subset {a} {l₁ l₂ : lists' α tt} :
  lists'.cons a l₁ ⊆ l₂ ↔ a ∈ l₂ ∧ l₁ ⊆ l₂ :=
begin
  refine ⟨λ h, _, λ ⟨⟨a', m, e⟩, s⟩, subset.cons e m s⟩,
  generalize_hyp h' : lists'.cons a l₁ = l₁' at h,
  cases h with l a' a'' l l' e m s, {cases a, cases h'},
  cases a, cases a', cases h', exact ⟨⟨_, m, e⟩, s⟩
end

theorem of_list_subset {l₁ l₂ : list (lists α)} (h : l₁ ⊆ l₂) :
  lists'.of_list l₁ ⊆ lists'.of_list l₂ :=
begin
  induction l₁, {exact subset.nil},
  refine subset.cons (lists.equiv.refl _) _ (l₁_ih (list.subset_of_cons_subset h)),
  simp at h, simp [h]
end

@[refl] theorem subset.refl {l : lists' α tt} : l ⊆ l :=
by rw ← lists'.of_to_list l; exact
   of_list_subset (list.subset.refl _)

theorem subset_nil {l : lists' α tt} :
  l ⊆ lists'.nil → l = lists'.nil :=
begin
  rw ← of_to_list l,
  induction to_list l; intro h, {refl},
  rcases cons_subset.1 h with ⟨⟨_, ⟨⟩, _⟩, _⟩
end

theorem mem_of_subset' {a} {l₁ l₂ : lists' α tt}
  (s : l₁ ⊆ l₂) (h : a ∈ l₁.to_list) : a ∈ l₂ :=
begin
  induction s with _ a a' l l' e m s IH, {cases h},
  simp at h, rcases h with rfl|h,
  exacts [⟨_, m, e⟩, IH h]
end

theorem subset_def {l₁ l₂ : lists' α tt} :
  l₁ ⊆ l₂ ↔ ∀ a ∈ l₁.to_list, a ∈ l₂ :=
⟨λ H a, mem_of_subset' H, λ H, begin
  rw ← of_to_list l₁,
  revert H, induction to_list l₁; intro,
  { exact subset.nil },
  { simp at H, exact cons_subset.2 ⟨H.1, ih H.2⟩ }
end⟩

end lists'

namespace lists

/-- Sends `a : α` to the corresponding atom in `lists α`. -/
@[pattern] def atom (a : α) : lists α := ⟨_, lists'.atom a⟩

/-- Converts a proper ZFA prelist to a ZFA list. -/
@[pattern] def of' (l : lists' α tt) : lists α := ⟨_, l⟩

/-- Converts a ZFA list to a `list` of ZFA lists. Atoms are sent to `[]`. -/
@[simp] def to_list : lists α → list (lists α)
| ⟨b, l⟩ := l.to_list

/-- Predicate stating that a ZFA list is proper. -/
def is_list (l : lists α) : Prop := l.1

/-- Converts a `list` of ZFA lists to a ZFA list. -/
def of_list (l : list (lists α)) : lists α := of' (lists'.of_list l)

theorem is_list_to_list (l : list (lists α)) : is_list (of_list l) :=
eq.refl _

theorem to_of_list (l : list (lists α)) : to_list (of_list l) = l :=
by simp [of_list, of']

theorem of_to_list : ∀ {l : lists α}, is_list l → of_list (to_list l) = l
| ⟨tt, l⟩ _ := by simp [of_list, of']

instance : inhabited (lists α) :=
⟨of' lists'.nil⟩

instance [decidable_eq α] : decidable_eq (lists α) :=
by unfold lists; apply_instance

instance [has_sizeof α] : has_sizeof (lists α) :=
by unfold lists; apply_instance

/-- A recursion principle for pairs of ZFA lists and proper ZFA prelists. -/
def induction_mut (C : lists α → Sort*) (D : lists' α tt → Sort*)
  (C0 : ∀ a, C (atom a)) (C1 : ∀ l, D l → C (of' l))
  (D0 : D lists'.nil) (D1 : ∀ a l, C a → D l → D (lists'.cons a l)) :
  pprod (∀ l, C l) (∀ l, D l) :=
begin
  suffices : ∀ {b} (l : lists' α b),
    pprod (C ⟨_, l⟩) (match b, l with
    | tt, l := D l
    | ff, l := punit
    end),
  { exact ⟨λ ⟨b, l⟩, (this _).1, λ l, (this l).2⟩ },
  intros, induction l with a b a l IH₁ IH₂,
  { exact ⟨C0 _, ⟨⟩⟩ },
  { exact ⟨C1 _ D0, D0⟩ },
  { suffices, {exact ⟨C1 _ this, this⟩},
    exact D1 ⟨_, _⟩ _ IH₁.1 IH₂.2 }
end

/-- Membership of ZFA list. A ZFA list belongs to a proper ZFA list if it belongs to the latter as a
proper ZFA prelist. An atom has no members. -/
def mem (a : lists α) : lists α → Prop
| ⟨ff, l⟩ := false
| ⟨tt, l⟩ := a ∈ l

instance : has_mem (lists α) (lists α) := ⟨mem⟩

theorem is_list_of_mem {a : lists α} : ∀ {l : lists α}, a ∈ l → is_list l
| ⟨_, lists'.nil⟩       _ := rfl
| ⟨_, lists'.cons' _ _⟩ _ := rfl

theorem equiv.antisymm_iff {l₁ l₂ : lists' α tt} :
  of' l₁ ~ of' l₂ ↔ l₁ ⊆ l₂ ∧ l₂ ⊆ l₁ :=
begin
  refine ⟨λ h, _, λ ⟨h₁, h₂⟩, equiv.antisymm h₁ h₂⟩,
  cases h with _ _ _ h₁ h₂,
  { simp [lists'.subset.refl] }, { exact ⟨h₁, h₂⟩ }
end

attribute [refl] equiv.refl

theorem equiv_atom {a} {l : lists α} : atom a ~ l ↔ atom a = l :=
⟨λ h, by cases h; refl, λ h, h ▸ equiv.refl _⟩

theorem equiv.symm {l₁ l₂ : lists α} (h : l₁ ~ l₂) : l₂ ~ l₁ :=
by cases h with _ _ _ h₁ h₂; [refl, exact equiv.antisymm h₂ h₁]

theorem equiv.trans : ∀ {l₁ l₂ l₃ : lists α}, l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃ :=
begin
  let trans := λ (l₁ : lists α), ∀ ⦃l₂ l₃⦄, l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃,
  suffices : pprod (∀ l₁, trans l₁)
    (∀ (l : lists' α tt) (l' ∈ l.to_list), trans l'), {exact this.1},
  apply induction_mut,
  { intros a l₂ l₃ h₁ h₂,
    rwa ← equiv_atom.1 h₁ at h₂ },
  { intros l₁ IH l₂ l₃ h₁ h₂,
    cases h₁ with _ _ l₂, {exact h₂},
    cases h₂ with _ _ l₃, {exact h₁},
    cases equiv.antisymm_iff.1 h₁ with hl₁ hr₁,
    cases equiv.antisymm_iff.1 h₂ with hl₂ hr₂,
    apply equiv.antisymm_iff.2; split; apply lists'.subset_def.2,
    { intros a₁ m₁,
      rcases lists'.mem_of_subset' hl₁ m₁ with ⟨a₂, m₂, e₁₂⟩,
      rcases lists'.mem_of_subset' hl₂ m₂ with ⟨a₃, m₃, e₂₃⟩,
      exact ⟨a₃, m₃, IH _ m₁ e₁₂ e₂₃⟩ },
    { intros a₃ m₃,
      rcases lists'.mem_of_subset' hr₂ m₃ with ⟨a₂, m₂, e₃₂⟩,
      rcases lists'.mem_of_subset' hr₁ m₂ with ⟨a₁, m₁, e₂₁⟩,
      exact ⟨a₁, m₁, (IH _ m₁ e₂₁.symm e₃₂.symm).symm⟩ } },
  { rintro _ ⟨⟩ },
  { intros a l IH₁ IH₂, simpa [IH₁] using IH₂ }
end

instance : setoid (lists α) :=
⟨(~), equiv.refl, @equiv.symm _, @equiv.trans _⟩

section decidable

@[simp] def equiv.decidable_meas :
  (psum (Σ' (l₁ : lists α), lists α) $
   psum (Σ' (l₁ : lists' α tt), lists' α tt)
   Σ' (a : lists α), lists' α tt) → ℕ
| (psum.inl ⟨l₁, l₂⟩) := sizeof l₁ + sizeof l₂
| (psum.inr $ psum.inl ⟨l₁, l₂⟩) := sizeof l₁ + sizeof l₂
| (psum.inr $ psum.inr ⟨l₁, l₂⟩) := sizeof l₁ + sizeof l₂

open well_founded_tactics

theorem sizeof_pos {b} (l : lists' α b) : 0 < sizeof l :=
by cases l; unfold_sizeof; trivial_nat_lt

theorem lt_sizeof_cons' {b} (a : lists' α b) (l) :
  sizeof (⟨b, a⟩ : lists α) < sizeof (lists'.cons' a l) :=
by {unfold_sizeof, apply sizeof_pos}

@[instance] mutual def equiv.decidable, subset.decidable, mem.decidable [decidable_eq α]
with equiv.decidable : ∀ l₁ l₂ : lists α, decidable (l₁ ~ l₂)
| ⟨ff, l₁⟩ ⟨ff, l₂⟩ := decidable_of_iff' (l₁ = l₂) $
  by cases l₁; refine equiv_atom.trans (by simp [atom])
| ⟨ff, l₁⟩ ⟨tt, l₂⟩ := is_false $ by rintro ⟨⟩
| ⟨tt, l₁⟩ ⟨ff, l₂⟩ := is_false $ by rintro ⟨⟩
| ⟨tt, l₁⟩ ⟨tt, l₂⟩ := begin
  haveI :=
    have sizeof l₁ + sizeof l₂ <
         sizeof (⟨tt, l₁⟩ : lists α) + sizeof (⟨tt, l₂⟩ : lists α),
    by default_dec_tac,
    subset.decidable l₁ l₂,
  haveI :=
    have sizeof l₂ + sizeof l₁ <
         sizeof (⟨tt, l₁⟩ : lists α) + sizeof (⟨tt, l₂⟩ : lists α),
    by default_dec_tac,
    subset.decidable l₂ l₁,
  exact decidable_of_iff' _ equiv.antisymm_iff,
end
with subset.decidable : ∀ l₁ l₂ : lists' α tt, decidable (l₁ ⊆ l₂)
| lists'.nil l₂ := is_true subset.nil
| (@lists'.cons' _ b a l₁) l₂ := begin
  haveI :=
    have sizeof (⟨b, a⟩ : lists α) + sizeof l₂ <
         sizeof (lists'.cons' a l₁) + sizeof l₂,
    from add_lt_add_right (lt_sizeof_cons' _ _) _,
    mem.decidable ⟨b, a⟩ l₂,
  haveI :=
    have sizeof l₁ + sizeof l₂ <
         sizeof (lists'.cons' a l₁) + sizeof l₂,
    by default_dec_tac,
    subset.decidable l₁ l₂,
  exact decidable_of_iff' _ (@lists'.cons_subset _ ⟨_, _⟩ _ _)
end
with mem.decidable : ∀ (a : lists α) (l : lists' α tt), decidable (a ∈ l)
| a lists'.nil := is_false $ by rintro ⟨_, ⟨⟩, _⟩
| a (lists'.cons' b l₂) := begin
  haveI :=
    have sizeof a + sizeof (⟨_, b⟩ : lists α) <
         sizeof a + sizeof (lists'.cons' b l₂),
    from add_lt_add_left (lt_sizeof_cons' _ _) _,
    equiv.decidable a ⟨_, b⟩,
  haveI :=
    have sizeof a + sizeof l₂ <
         sizeof a + sizeof (lists'.cons' b l₂),
    by default_dec_tac,
    mem.decidable a l₂,
  refine decidable_of_iff' (a ~ ⟨_, b⟩ ∨ a ∈ l₂) _,
  rw ← lists'.mem_cons, refl
end
using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf equiv.decidable_meas⟩],
  dec_tac := `[assumption] }

end decidable

end lists

namespace lists'

theorem mem_equiv_left {l : lists' α tt} :
  ∀ {a a'}, a ~ a' → (a ∈ l ↔ a' ∈ l) :=
suffices ∀ {a a'}, a ~ a' → a ∈ l → a' ∈ l,
  from λ a a' e, ⟨this e, this e.symm⟩,
λ a₁ a₂ e₁ ⟨a₃, m₃, e₂⟩, ⟨_, m₃, e₁.symm.trans e₂⟩

theorem mem_of_subset {a} {l₁ l₂ : lists' α tt}
  (s : l₁ ⊆ l₂) : a ∈ l₁ → a ∈ l₂ | ⟨a', m, e⟩ :=
(mem_equiv_left e).2 (mem_of_subset' s m)

theorem subset.trans {l₁ l₂ l₃ : lists' α tt}
  (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ :=
subset_def.2 $ λ a₁ m₁, mem_of_subset h₂ $ mem_of_subset' h₁ m₁

end lists'

def finsets (α : Type*) := quotient (@lists.setoid α)

namespace finsets

instance : has_emptyc (finsets α) := ⟨⟦lists.of' lists'.nil⟧⟩

instance : inhabited (finsets α) := ⟨∅⟩

instance [decidable_eq α] : decidable_eq (finsets α) :=
by unfold finsets; apply_instance

end finsets
