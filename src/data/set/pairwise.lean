/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.set.lattice
import tactic.wlog

/-!
# Relations holding pairwise

This file defines pairwise relations and pairwise disjoint sets.

## Main declarations

* `pairwise p`: States that `p i j` for all `i ≠ j`.
* `pairwise_disjoint`: `pairwise_disjoint s` states that all elements in `s` are either equal or
  `disjoint`.
-/

open set

universes u v
variables {α : Type u} {β : Type v} {ι : Type*}

section pairwise
variables {s t u : set α}

/-- A relation `p` holds pairwise if `p i j` for all `i ≠ j`. -/
def pairwise {α : Type*} (p : α → α → Prop) := ∀ i j, i ≠ j → p i j

theorem set.pairwise_on_univ {r : α → α → Prop} :
  (univ : set α).pairwise_on r ↔ pairwise r :=
by simp only [pairwise_on, pairwise, mem_univ, forall_const]

theorem set.pairwise_on.on_injective {s : set α} {r : α → α → Prop} (hs : pairwise_on s r)
  {f : β → α} (hf : function.injective f) (hfs : ∀ x, f x ∈ s) :
  pairwise (r on f) :=
λ i j hij, hs _ (hfs i) _ (hfs j) (hf.ne hij)

theorem pairwise.mono {p q : α → α → Prop} (hp : pairwise p) (h : ∀ ⦃i j⦄, p i j → q i j) :
  pairwise q :=
λ i j hij, h (hp i j hij)

theorem pairwise_on_bool {r} (hr : symmetric r) {a b : α} :
  pairwise (r on (λ c, cond c a b)) ↔ r a b :=
by simpa [pairwise, function.on_fun] using @hr a b

theorem pairwise_disjoint_on_bool [semilattice_inf_bot α] {a b : α} :
  pairwise (disjoint on (λ c, cond c a b)) ↔ disjoint a b :=
pairwise_on_bool disjoint.symm

lemma symmetric.pairwise_on [linear_order β] {r} (hr : symmetric r) (f : β → α) :
  pairwise (r on f) ↔ ∀ m n, m < n → r (f m) (f n) :=
⟨λ h m n hmn, h m n hmn.ne, λ h m n hmn, begin
  obtain hmn' | hmn' := hmn.lt_or_lt,
  { exact h _ _ hmn' },
  { exact hr (h _ _ hmn') }
end⟩

theorem pairwise_disjoint_on [semilattice_inf_bot α] [linear_order β] (f : β → α) :
  pairwise (disjoint on f) ↔ ∀ m n, m < n → disjoint (f m) (f n) :=
symmetric.pairwise_on disjoint.symm f

theorem pairwise.pairwise_on {p : α → α → Prop} (h : pairwise p) (s : set α) : s.pairwise_on p :=
λ x hx y hy, h x y

theorem pairwise_disjoint_fiber (f : α → β) : pairwise (disjoint on (λ y : β, f ⁻¹' {y})) :=
set.pairwise_on_univ.1 $ pairwise_on_disjoint_fiber f univ

end pairwise

namespace set
section semilattice_inf_bot
variables [semilattice_inf_bot α] {s t : set ι} {f g : ι → α}

/-- Elements of a set is `pairwise_disjoint`, if any distinct two are disjoint. -/
def pairwise_disjoint (s : set ι) (f : ι → α) : Prop :=
pairwise_on s (disjoint on f)

lemma pairwise_disjoint.subset (ht : t.pairwise_disjoint f) (h : s ⊆ t) : s.pairwise_disjoint f :=
pairwise_on.mono h ht

lemma pairwise_disjoint.mono (hs : s.pairwise_disjoint f) (h : g ≤ f) :  s.pairwise_disjoint g :=
λ a ha b hb hab, (hs a ha b hb hab).mono (h a) (h b)

lemma pairwise_disjoint_empty : (∅ : set ι).pairwise_disjoint f := pairwise_on_empty _

lemma pairwise_disjoint_singleton (i : ι) (f : ι → α) : pairwise_disjoint {i} f :=
pairwise_on_singleton i _

lemma pairwise_disjoint_insert {i : ι} :
  (insert i s).pairwise_disjoint f
    ↔ s.pairwise_disjoint f ∧ ∀ j ∈ s, i ≠ j → disjoint (f i) (f j) :=
set.pairwise_on_insert_of_symmetric $ symmetric_disjoint.comap f

lemma pairwise_disjoint.insert (hs : s.pairwise_disjoint f) {i : ι}
  (h : ∀ j ∈ s, i ≠ j → disjoint (f i) (f j)) :
  (insert i s).pairwise_disjoint f :=
set.pairwise_disjoint_insert.2 ⟨hs, h⟩

lemma pairwise_disjoint.image_of_le (hs : s.pairwise_disjoint f) {g : ι → ι} (hg : f ∘ g ≤ f) :
  (g '' s).pairwise_disjoint f :=
begin
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h,
  exact (hs a ha b hb $ ne_of_apply_ne _ h).mono (hg a) (hg b),
end

lemma pairwise_disjoint.range (g : s → ι) (hg : ∀ (i : s), f (g i) ≤ f i)
  (ht : s.pairwise_disjoint f) :
  (range g).pairwise_disjoint f :=
begin
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy,
  exact (ht _ x.2 _ y.2 $ λ h, hxy $ congr_arg g $ subtype.ext h).mono (hg x) (hg y),
end

-- classical
lemma pairwise_disjoint.elim (hs : s.pairwise_disjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
  (h : ¬ disjoint (f i) (f j)) :
  i = j :=
of_not_not $ λ hij, h $ hs _ hi _ hj hij

-- classical
lemma pairwise_disjoint.elim' (hs : s.pairwise_disjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
  (h : f i ⊓ f j ≠ ⊥) :
  i = j :=
hs.elim hi hj $ λ hij, h hij.eq_bot

end semilattice_inf_bot

/-! ### Pairwise disjoint set of sets -/

lemma pairwise_disjoint_range_singleton :
  (set.range (singleton : ι → set ι)).pairwise_disjoint id :=
begin
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h,
  exact disjoint_singleton.2 (ne_of_apply_ne _ h),
end

-- classical
lemma pairwise_disjoint.elim_set {s : set ι} {f : ι → set α} (hs : s.pairwise_disjoint f) {i j : ι}
  (hi : i ∈ s) (hj : j ∈ s) (a : α) (hai : a ∈ f i) (haj : a ∈ f j) : i = j :=
hs.elim hi hj $ not_disjoint_iff.2 ⟨a, hai, haj⟩

end set
