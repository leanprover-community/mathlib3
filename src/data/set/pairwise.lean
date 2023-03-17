/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import logic.relation
import logic.pairwise
import data.set.lattice

/-!
# Relations holding pairwise

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file develops pairwise relations and defines pairwise disjoint indexed sets.

We also prove many basic facts about `pairwise`. It is possible that an intermediate file,
with more imports than `logic.pairwise` but not importing `data.set.lattice` would be appropriate
to hold many of these basic facts.

## Main declarations

* `set.pairwise_disjoint`: `s.pairwise_disjoint f` states that images under `f` of distinct elements
  of `s` are either equal or `disjoint`.

## Notes

The spelling `s.pairwise_disjoint id` is preferred over `s.pairwise disjoint` to permit dot notation
on `set.pairwise_disjoint`, even though the latter unfolds to something nicer.
-/

open set function

variables {α β γ ι ι' : Type*} {r p q : α → α → Prop}

section pairwise
variables {f g : ι → α} {s t u : set α} {a b : α}

lemma pairwise_on_bool (hr : symmetric r) {a b : α} : pairwise (r on (λ c, cond c a b)) ↔ r a b :=
by simpa [pairwise, function.on_fun] using @hr a b

lemma pairwise_disjoint_on_bool [semilattice_inf α] [order_bot α] {a b : α} :
  pairwise (disjoint on (λ c, cond c a b)) ↔ disjoint a b :=
pairwise_on_bool disjoint.symm

lemma symmetric.pairwise_on [linear_order ι] (hr : symmetric r) (f : ι → α) :
  pairwise (r on f) ↔ ∀ ⦃m n⦄, m < n → r (f m) (f n) :=
⟨λ h m n hmn, h hmn.ne, λ h m n hmn, hmn.lt_or_lt.elim (@h _ _) (λ h', hr (h h'))⟩

lemma pairwise_disjoint_on [semilattice_inf α] [order_bot α] [linear_order ι] (f : ι → α) :
  pairwise (disjoint on f) ↔ ∀ ⦃m n⦄, m < n → disjoint (f m) (f n) :=
symmetric.pairwise_on disjoint.symm f

lemma pairwise_disjoint.mono [semilattice_inf α] [order_bot α]
  (hs : pairwise (disjoint on f)) (h : g ≤ f) : pairwise (disjoint on g) :=
hs.mono (λ i j hij, disjoint.mono (h i) (h j) hij)

alias function.injective_iff_pairwise_ne ↔ function.injective.pairwise_ne _

namespace set

lemma pairwise.mono (h : t ⊆ s) (hs : s.pairwise r) : t.pairwise r :=
λ x xt y yt, hs (h xt) (h yt)

lemma pairwise.mono' (H : r ≤ p) (hr : s.pairwise r) : s.pairwise p := hr.imp H

lemma pairwise_top (s : set α) : s.pairwise ⊤ := pairwise_of_forall s _ (λ a b, trivial)

protected lemma subsingleton.pairwise (h : s.subsingleton) (r : α → α → Prop) :
  s.pairwise r :=
λ x hx y hy hne, (hne (h hx hy)).elim

@[simp] lemma pairwise_empty (r : α → α → Prop) : (∅ : set α).pairwise r :=
subsingleton_empty.pairwise r

@[simp] lemma pairwise_singleton (a : α) (r : α → α → Prop) : set.pairwise {a} r :=
subsingleton_singleton.pairwise r

lemma pairwise_iff_of_refl [is_refl α r] : s.pairwise r ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → r a b :=
forall₄_congr $ λ a _ b _, or_iff_not_imp_left.symm.trans $ or_iff_right_of_imp of_eq

alias pairwise_iff_of_refl ↔ pairwise.of_refl _

lemma nonempty.pairwise_iff_exists_forall [is_equiv α r] {s : set ι} (hs : s.nonempty) :
  (s.pairwise (r on f)) ↔ ∃ z, ∀ x ∈ s, r (f x) z :=
begin
  fsplit,
  { rcases hs with ⟨y, hy⟩,
    refine λ H, ⟨f y, λ x hx, _⟩,
    rcases eq_or_ne x y with rfl|hne,
    { apply is_refl.refl },
    { exact H hx hy hne } },
  { rintro ⟨z, hz⟩ x hx y hy hne,
    exact @is_trans.trans α r _ (f x) z (f y) (hz _ hx) (is_symm.symm _ _ $ hz _ hy) }
end

/-- For a nonempty set `s`, a function `f` takes pairwise equal values on `s` if and only if
for some `z` in the codomain, `f` takes value `z` on all `x ∈ s`. See also
`set.pairwise_eq_iff_exists_eq` for a version that assumes `[nonempty ι]` instead of
`set.nonempty s`. -/
lemma nonempty.pairwise_eq_iff_exists_eq {s : set α} (hs : s.nonempty) {f : α → ι} :
  (s.pairwise (λ x y, f x = f y)) ↔ ∃ z, ∀ x ∈ s, f x = z :=
hs.pairwise_iff_exists_forall

lemma pairwise_iff_exists_forall [nonempty ι] (s : set α) (f : α → ι) {r : ι → ι → Prop}
  [is_equiv ι r] :
  (s.pairwise (r on f)) ↔ ∃ z, ∀ x ∈ s, r (f x) z :=
begin
  rcases s.eq_empty_or_nonempty with rfl|hne,
  { simp },
  { exact hne.pairwise_iff_exists_forall }
end

/-- A function `f : α → ι` with nonempty codomain takes pairwise equal values on a set `s` if and
only if for some `z` in the codomain, `f` takes value `z` on all `x ∈ s`. See also
`set.nonempty.pairwise_eq_iff_exists_eq` for a version that assumes `set.nonempty s` instead of
`[nonempty ι]`. -/
lemma pairwise_eq_iff_exists_eq [nonempty ι] (s : set α) (f : α → ι) :
  (s.pairwise (λ x y, f x = f y)) ↔ ∃ z, ∀ x ∈ s, f x = z :=
pairwise_iff_exists_forall s f

lemma pairwise_union :
  (s ∪ t).pairwise r ↔
    s.pairwise r ∧ t.pairwise r ∧ ∀ (a ∈ s) (b ∈ t), a ≠ b → r a b ∧ r b a :=
begin
  simp only [set.pairwise, mem_union, or_imp_distrib, forall_and_distrib],
  exact ⟨λ H, ⟨H.1.1, H.2.2, H.2.1, λ x hx y hy hne, H.1.2 y hy x hx hne.symm⟩,
    λ H, ⟨⟨H.1, λ x hx y hy hne, H.2.2.2 y hy x hx hne.symm⟩, H.2.2.1, H.2.1⟩⟩
end

lemma pairwise_union_of_symmetric (hr : symmetric r) :
  (s ∪ t).pairwise r ↔
    s.pairwise r ∧ t.pairwise r ∧ ∀ (a ∈ s) (b ∈ t), a ≠ b → r a b :=
pairwise_union.trans $ by simp only [hr.iff, and_self]

lemma pairwise_insert :
  (insert a s).pairwise r ↔ s.pairwise r ∧ ∀ b ∈ s, a ≠ b → r a b ∧ r b a :=
by simp only [insert_eq, pairwise_union, pairwise_singleton, true_and,
  mem_singleton_iff, forall_eq]

lemma pairwise_insert_of_not_mem (ha : a ∉ s) :
  (insert a s).pairwise r ↔ s.pairwise r ∧ ∀ b ∈ s, r a b ∧ r b a :=
pairwise_insert.trans $ and_congr_right' $ forall₂_congr $ λ b hb,
  by simp [(ne_of_mem_of_not_mem hb ha).symm]

lemma pairwise.insert (hs : s.pairwise r) (h : ∀ b ∈ s, a ≠ b → r a b ∧ r b a) :
  (insert a s).pairwise r :=
pairwise_insert.2 ⟨hs, h⟩

lemma pairwise.insert_of_not_mem (ha : a ∉ s) (hs : s.pairwise r) (h : ∀ b ∈ s, r a b ∧ r b a) :
  (insert a s).pairwise r :=
(pairwise_insert_of_not_mem ha).2 ⟨hs, h⟩

lemma pairwise_insert_of_symmetric (hr : symmetric r) :
  (insert a s).pairwise r ↔ s.pairwise r ∧ ∀ b ∈ s, a ≠ b → r a b :=
by simp only [pairwise_insert, hr.iff a, and_self]

lemma pairwise_insert_of_symmetric_of_not_mem (hr : symmetric r) (ha : a ∉ s) :
  (insert a s).pairwise r ↔ s.pairwise r ∧ ∀ b ∈ s, r a b :=
by simp only [pairwise_insert_of_not_mem ha, hr.iff a, and_self]

lemma pairwise.insert_of_symmetric (hs : s.pairwise r) (hr : symmetric r)
  (h : ∀ b ∈ s, a ≠ b → r a b) :
  (insert a s).pairwise r :=
(pairwise_insert_of_symmetric hr).2 ⟨hs, h⟩

lemma pairwise.insert_of_symmetric_of_not_mem (hs : s.pairwise r) (hr : symmetric r) (ha : a ∉ s)
  (h : ∀ b ∈ s, r a b) :
  (insert a s).pairwise r :=
(pairwise_insert_of_symmetric_of_not_mem hr ha).2 ⟨hs, h⟩

lemma pairwise_pair : set.pairwise {a, b} r ↔ (a ≠ b → r a b ∧ r b a) :=
by simp [pairwise_insert]

lemma pairwise_pair_of_symmetric (hr : symmetric r) : set.pairwise {a, b} r ↔ (a ≠ b → r a b) :=
by simp [pairwise_insert_of_symmetric hr]

lemma pairwise_univ : (univ : set α).pairwise r ↔ pairwise r :=
by simp only [set.pairwise, pairwise, mem_univ, forall_const]

@[simp] lemma pairwise_bot_iff : s.pairwise (⊥ : α → α → Prop) ↔ (s : set α).subsingleton :=
⟨λ h a ha b hb, h.eq ha hb id, λ h, h.pairwise _⟩

alias pairwise_bot_iff ↔ pairwise.subsingleton _

lemma inj_on.pairwise_image {s : set ι} (h : s.inj_on f) :
  (f '' s).pairwise r ↔ s.pairwise (r on f) :=
by simp [h.eq_iff, set.pairwise] {contextual := tt}

lemma pairwise_Union {f : ι → set α} (h : directed (⊆) f) :
  (⋃ n, f n).pairwise r ↔ ∀ n, (f n).pairwise r :=
begin
  split,
  { assume H n,
    exact pairwise.mono (subset_Union _ _) H },
  { assume H i hi j hj hij,
    rcases mem_Union.1 hi with ⟨m, hm⟩,
    rcases mem_Union.1 hj with ⟨n, hn⟩,
    rcases h m n with ⟨p, mp, np⟩,
    exact H p (mp hm) (np hn) hij }
end

lemma pairwise_sUnion {r : α → α → Prop} {s : set (set α)} (h : directed_on (⊆) s) :
  (⋃₀ s).pairwise r ↔ (∀ a ∈ s, set.pairwise a r) :=
by { rw [sUnion_eq_Union, pairwise_Union (h.directed_coe), set_coe.forall], refl }

end set

end pairwise

lemma pairwise_subtype_iff_pairwise_set (s : set α) (r : α → α → Prop) :
  pairwise (λ (x : s) (y : s), r x y) ↔ s.pairwise r :=
by simp only [pairwise, set.pairwise, set_coe.forall, ne.def, subtype.ext_iff, subtype.coe_mk]

alias pairwise_subtype_iff_pairwise_set ↔ pairwise.set_of_subtype set.pairwise.subtype

namespace set
section partial_order_bot
variables [partial_order α] [order_bot α] {s t : set ι} {f g : ι → α}

/-- A set is `pairwise_disjoint` under `f`, if the images of any distinct two elements under `f`
are disjoint.

`s.pairwise disjoint` is (definitionally) the same as `s.pairwise_disjoint id`. We prefer the latter
in order to allow dot notation on `set.pairwise_disjoint`, even though the former unfolds more
nicely. -/
def pairwise_disjoint (s : set ι) (f : ι → α) : Prop := s.pairwise (disjoint on f)

lemma pairwise_disjoint.subset (ht : t.pairwise_disjoint f) (h : s ⊆ t) : s.pairwise_disjoint f :=
pairwise.mono h ht

lemma pairwise_disjoint.mono_on (hs : s.pairwise_disjoint f) (h : ∀ ⦃i⦄, i ∈ s → g i ≤ f i) :
  s.pairwise_disjoint g :=
λ a ha b hb hab, (hs ha hb hab).mono (h ha) (h hb)

lemma pairwise_disjoint.mono (hs : s.pairwise_disjoint f) (h : g ≤ f) : s.pairwise_disjoint g :=
hs.mono_on (λ i _, h i)

@[simp] lemma pairwise_disjoint_empty : (∅ : set ι).pairwise_disjoint f := pairwise_empty _

@[simp] lemma pairwise_disjoint_singleton (i : ι) (f : ι → α) : pairwise_disjoint {i} f :=
pairwise_singleton i _

lemma pairwise_disjoint_insert {i : ι} :
  (insert i s).pairwise_disjoint f
    ↔ s.pairwise_disjoint f ∧ ∀ j ∈ s, i ≠ j → disjoint (f i) (f j) :=
set.pairwise_insert_of_symmetric $ symmetric_disjoint.comap f

lemma pairwise_disjoint_insert_of_not_mem {i : ι} (hi : i ∉ s) :
  (insert i s).pairwise_disjoint f ↔ s.pairwise_disjoint f ∧ ∀ j ∈ s, disjoint (f i) (f j) :=
pairwise_insert_of_symmetric_of_not_mem (symmetric_disjoint.comap f) hi

lemma pairwise_disjoint.insert (hs : s.pairwise_disjoint f) {i : ι}
  (h : ∀ j ∈ s, i ≠ j → disjoint (f i) (f j)) :
  (insert i s).pairwise_disjoint f :=
set.pairwise_disjoint_insert.2 ⟨hs, h⟩

lemma pairwise_disjoint.insert_of_not_mem (hs : s.pairwise_disjoint f) {i : ι} (hi : i ∉ s)
  (h : ∀ j ∈ s, disjoint (f i) (f j)) :
  (insert i s).pairwise_disjoint f :=
(set.pairwise_disjoint_insert_of_not_mem hi).2 ⟨hs, h⟩

lemma pairwise_disjoint.image_of_le (hs : s.pairwise_disjoint f) {g : ι → ι} (hg : f ∘ g ≤ f) :
  (g '' s).pairwise_disjoint f :=
begin
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h,
  exact (hs ha hb $ ne_of_apply_ne _ h).mono (hg a) (hg b),
end

lemma inj_on.pairwise_disjoint_image {g : ι' → ι} {s : set ι'} (h : s.inj_on g) :
  (g '' s).pairwise_disjoint f ↔ s.pairwise_disjoint (f ∘ g) :=
h.pairwise_image

lemma pairwise_disjoint.range (g : s → ι) (hg : ∀ (i : s), f (g i) ≤ f i)
  (ht : s.pairwise_disjoint f) :
  (range g).pairwise_disjoint f :=
begin
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy,
  exact (ht x.2 y.2 $ λ h, hxy $ congr_arg g $ subtype.ext h).mono (hg x) (hg y),
end

lemma pairwise_disjoint_union :
  (s ∪ t).pairwise_disjoint f ↔ s.pairwise_disjoint f ∧ t.pairwise_disjoint f ∧
    ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ t → i ≠ j → disjoint (f i) (f j) :=
pairwise_union_of_symmetric $ symmetric_disjoint.comap f

lemma pairwise_disjoint.union (hs : s.pairwise_disjoint f) (ht : t.pairwise_disjoint f)
  (h : ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ t → i ≠ j → disjoint (f i) (f j)) :
  (s ∪ t).pairwise_disjoint f :=
pairwise_disjoint_union.2 ⟨hs, ht, h⟩

lemma pairwise_disjoint_Union {g : ι' → set ι} (h : directed (⊆) g) :
  (⋃ n, g n).pairwise_disjoint f ↔ ∀ ⦃n⦄, (g n).pairwise_disjoint f :=
pairwise_Union h

lemma pairwise_disjoint_sUnion {s : set (set ι)} (h : directed_on (⊆) s) :
  (⋃₀ s).pairwise_disjoint f ↔ ∀ ⦃a⦄, a ∈ s → set.pairwise_disjoint a f :=
pairwise_sUnion h

-- classical
lemma pairwise_disjoint.elim (hs : s.pairwise_disjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
  (h : ¬ disjoint (f i) (f j)) :
  i = j :=
hs.eq hi hj h

end partial_order_bot

section semilattice_inf_bot
variables [semilattice_inf α] [order_bot α] {s t : set ι} {f g : ι → α}
-- classical
lemma pairwise_disjoint.elim' (hs : s.pairwise_disjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
  (h : f i ⊓ f j ≠ ⊥) :
  i = j :=
hs.elim hi hj $ λ hij, h hij.eq_bot

lemma pairwise_disjoint.eq_of_le (hs : s.pairwise_disjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
  (hf : f i ≠ ⊥) (hij : f i ≤ f j) :
  i = j :=
hs.elim' hi hj $ λ h, hf $ (inf_of_le_left hij).symm.trans h

end semilattice_inf_bot

section complete_lattice
variables [complete_lattice α]

/-- Bind operation for `set.pairwise_disjoint`. If you want to only consider finsets of indices, you
can use `set.pairwise_disjoint.bUnion_finset`. -/
lemma pairwise_disjoint.bUnion {s : set ι'} {g : ι' → set ι} {f : ι → α}
  (hs : s.pairwise_disjoint (λ i' : ι', ⨆ i ∈ g i', f i))
  (hg : ∀ i ∈ s, (g i).pairwise_disjoint f) :
  (⋃ i ∈ s, g i).pairwise_disjoint f :=
begin
  rintro a ha b hb hab,
  simp_rw set.mem_Union at ha hb,
  obtain ⟨c, hc, ha⟩ := ha,
  obtain ⟨d, hd, hb⟩ := hb,
  obtain hcd | hcd := eq_or_ne (g c) (g d),
  { exact hg d hd (hcd.subst ha) hb hab },
  { exact (hs hc hd $ ne_of_apply_ne _ hcd).mono (le_supr₂ a ha) (le_supr₂ b hb) }
end

end complete_lattice

/-! ### Pairwise disjoint set of sets -/

lemma pairwise_disjoint_range_singleton :
  (set.range (singleton : ι → set ι)).pairwise_disjoint id :=
begin
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h,
  exact disjoint_singleton.2 (ne_of_apply_ne _ h),
end

lemma pairwise_disjoint_fiber (f : ι → α) (s : set α) : s.pairwise_disjoint (λ a, f ⁻¹' {a}) :=
λ a _ b _ h, disjoint_iff_inf_le.mpr $ λ i ⟨hia, hib⟩, h $ (eq.symm hia).trans hib

-- classical
lemma pairwise_disjoint.elim_set {s : set ι} {f : ι → set α} (hs : s.pairwise_disjoint f) {i j : ι}
  (hi : i ∈ s) (hj : j ∈ s) (a : α) (hai : a ∈ f i) (haj : a ∈ f j) : i = j :=
hs.elim hi hj $ not_disjoint_iff.2 ⟨a, hai, haj⟩

lemma bUnion_diff_bUnion_eq {s t : set ι} {f : ι → set α} (h : (s ∪ t).pairwise_disjoint f) :
  (⋃ i ∈ s, f i) \ (⋃ i ∈ t, f i) = (⋃ i ∈ s \ t, f i) :=
begin
  refine (bUnion_diff_bUnion_subset f s t).antisymm
    (Union₂_subset $ λ i hi a ha, (mem_diff _).2 ⟨mem_bUnion hi.1 ha, _⟩),
  rw mem_Union₂, rintro ⟨j, hj, haj⟩,
  exact (h (or.inl hi.1) (or.inr hj) (ne_of_mem_of_not_mem hj hi.2).symm).le_bot ⟨ha, haj⟩,
end

/-- Equivalence between a disjoint bounded union and a dependent sum. -/
noncomputable def bUnion_eq_sigma_of_disjoint {s : set ι} {f : ι → set α}
  (h : s.pairwise_disjoint f) :
  (⋃ i ∈ s, f i) ≃ (Σ i : s, f i) :=
(equiv.set_congr (bUnion_eq_Union _ _)).trans $ Union_eq_sigma_of_disjoint $
  λ ⟨i, hi⟩ ⟨j, hj⟩ ne, h hi hj $ λ eq, ne $ subtype.eq eq

/-- The partial images of a binary function `f` whose partial evaluations are injective are pairwise
disjoint iff `f` is injective . -/
lemma pairwise_disjoint_image_right_iff {f : α → β → γ} {s : set α} {t : set β}
  (hf : ∀ a ∈ s, injective (f a)) :
  s.pairwise_disjoint (λ a, f a '' t) ↔ (s ×ˢ t).inj_on (λ p, f p.1 p.2) :=
begin
  refine ⟨λ hs x hx y hy (h : f _ _ = _), _, λ hs x hx y hy h, _⟩,
  { suffices : x.1 = y.1,
    { exact prod.ext this (hf _ hx.1 $ h.trans $ by rw this) },
    refine hs.elim hx.1 hy.1 (not_disjoint_iff.2 ⟨_, mem_image_of_mem _ hx.2, _⟩),
    rw h,
    exact mem_image_of_mem _ hy.2 },
  { refine disjoint_iff_inf_le.mpr _,
    rintro _ ⟨⟨a, ha, hab⟩, b, hb, rfl⟩,
    exact h (congr_arg prod.fst $ hs (mk_mem_prod hx ha) (mk_mem_prod hy hb) hab) }
end

/-- The partial images of a binary function `f` whose partial evaluations are injective are pairwise
disjoint iff `f` is injective . -/
lemma pairwise_disjoint_image_left_iff {f : α → β → γ} {s : set α} {t : set β}
  (hf : ∀ b ∈ t, injective (λ a, f a b)) :
  t.pairwise_disjoint (λ b, (λ a, f a b) '' s) ↔ (s ×ˢ t).inj_on (λ p, f p.1 p.2) :=
begin
  refine ⟨λ ht x hx y hy (h : f _ _ = _), _, λ ht x hx y hy h, _⟩,
  { suffices : x.2 = y.2,
    { exact prod.ext (hf _ hx.2 $ h.trans $ by rw this) this },
    refine ht.elim hx.2 hy.2 (not_disjoint_iff.2 ⟨_, mem_image_of_mem _ hx.1, _⟩),
    rw h,
    exact mem_image_of_mem _ hy.1 },
  { refine disjoint_iff_inf_le.mpr _,
    rintro _ ⟨⟨a, ha, hab⟩, b, hb, rfl⟩,
    exact h (congr_arg prod.snd $ ht (mk_mem_prod ha hx) (mk_mem_prod hb hy) hab) }
end

end set

lemma pairwise_disjoint_fiber (f : ι → α) : pairwise (disjoint on (λ a : α, f ⁻¹' {a})) :=
set.pairwise_univ.1 $ set.pairwise_disjoint_fiber f univ


section
variables {f : ι → set α} {s t : set ι}

lemma set.pairwise_disjoint.subset_of_bUnion_subset_bUnion (h₀ : (s ∪ t).pairwise_disjoint f)
  (h₁ : ∀ i ∈ s, (f i).nonempty) (h : (⋃ i ∈ s, f i) ⊆ ⋃ i ∈ t, f i) :
  s ⊆ t :=
begin
  rintro i hi,
  obtain ⟨a, hai⟩ := h₁ i hi,
  obtain ⟨j, hj, haj⟩ := mem_Union₂.1 (h $ mem_Union₂_of_mem hi hai),
  rwa h₀.eq (subset_union_left _ _ hi) (subset_union_right _ _ hj)
    (not_disjoint_iff.2 ⟨a, hai, haj⟩),
end

lemma pairwise.subset_of_bUnion_subset_bUnion (h₀ : pairwise (disjoint on f))
  (h₁ : ∀ i ∈ s, (f i).nonempty) (h : (⋃ i ∈ s, f i) ⊆ ⋃ i ∈ t, f i) :
  s ⊆ t :=
set.pairwise_disjoint.subset_of_bUnion_subset_bUnion (h₀.set_pairwise _) h₁ h

lemma pairwise.bUnion_injective (h₀ : pairwise (disjoint on f)) (h₁ : ∀ i, (f i).nonempty) :
  injective (λ s : set ι, ⋃ i ∈ s, f i) :=
λ s t h, (h₀.subset_of_bUnion_subset_bUnion (λ _ _, h₁ _) $ h.subset).antisymm $
  h₀.subset_of_bUnion_subset_bUnion (λ _ _, h₁ _) $ h.superset

end
