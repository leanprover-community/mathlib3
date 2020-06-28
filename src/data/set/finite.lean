/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import data.fintype.basic
import algebra.big_operators

/-!
# Finite sets

This file defines predicates `finite : set α → Prop` and `infinite : set α → Prop` and proves some
basic facts about finite sets.
-/

open set function
open_locale big_operators

universes u v w x
variables {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace set

/-- A set is finite if the subtype is a fintype, i.e. there is a
  list that enumerates its members. -/
def finite (s : set α) : Prop := nonempty (fintype s)

/-- A set is infinite if it is not finite. -/
def infinite (s : set α) : Prop := ¬ finite s

/-- The subtype corresponding to a finite set is a finite type. Note
that because `finite` isn't a typeclass, this will not fire if it
is made into an instance -/
noncomputable def finite.fintype {s : set α} (h : finite s) : fintype s :=
classical.choice h

/-- Get a finset from a finite set -/
noncomputable def finite.to_finset {s : set α} (h : finite s) : finset α :=
@set.to_finset _ _ h.fintype

@[simp] theorem finite.mem_to_finset {s : set α} {h : finite s} {a : α} : a ∈ h.to_finset ↔ a ∈ s :=
@mem_to_finset _ _ h.fintype _

@[simp] lemma finite.coe_to_finset {α} {s : set α} (h : finite s) : ↑h.to_finset = s :=
@set.coe_to_finset _ s h.fintype

theorem finite.exists_finset {s : set α} : finite s →
  ∃ s' : finset α, ∀ a : α, a ∈ s' ↔ a ∈ s
| ⟨h⟩ := by exactI ⟨to_finset s, λ _, mem_to_finset⟩

theorem finite.exists_finset_coe {s : set α} (hs : finite s) :
  ∃ s' : finset α, ↑s' = s :=
⟨hs.to_finset, hs.coe_to_finset⟩

/-- Finite sets can be lifted to finsets. -/
instance : can_lift (set α) (finset α) :=
{ coe := coe,
  cond := finite,
  prf := λ s hs, hs.exists_finset_coe }

theorem finite_mem_finset (s : finset α) : finite {a | a ∈ s} :=
⟨fintype.of_finset s (λ _, iff.rfl)⟩

theorem finite.of_fintype [fintype α] (s : set α) : finite s :=
by classical; exact ⟨set_fintype s⟩

/-- Membership of a subset of a finite type is decidable.

Using this as an instance leads to potential loops with `subtype.fintype` under certain decidability
assumptions, so it should only be declared a local instance. -/
def decidable_mem_of_fintype [decidable_eq α] (s : set α) [fintype s] (a) : decidable (a ∈ s) :=
decidable_of_iff _ mem_to_finset

instance fintype_empty : fintype (∅ : set α) :=
fintype.of_finset ∅ $ by simp

theorem empty_card : fintype.card (∅ : set α) = 0 := rfl

@[simp] theorem empty_card' {h : fintype.{u} (∅ : set α)} :
  @fintype.card (∅ : set α) h = 0 :=
eq.trans (by congr) empty_card

@[simp] theorem finite_empty : @finite α ∅ := ⟨set.fintype_empty⟩

/-- A `fintype` structure on `insert a s`. -/
def fintype_insert' {a : α} (s : set α) [fintype s] (h : a ∉ s) : fintype (insert a s : set α) :=
fintype.of_finset ⟨a :: s.to_finset.1,
  multiset.nodup_cons_of_nodup (by simp [h]) s.to_finset.2⟩ $ by simp

theorem card_fintype_insert' {a : α} (s : set α) [fintype s] (h : a ∉ s) :
  @fintype.card _ (fintype_insert' s h) = fintype.card s + 1 :=
by rw [fintype_insert', fintype.card_of_finset];
   simp [finset.card, to_finset]; refl

@[simp] theorem card_insert {a : α} (s : set α)
  [fintype s] (h : a ∉ s) {d : fintype.{u} (insert a s : set α)} :
  @fintype.card _ d = fintype.card s + 1 :=
by rw ← card_fintype_insert' s h; congr

lemma card_image_of_inj_on {s : set α} [fintype s]
  {f : α → β} [fintype (f '' s)] (H : ∀x∈s, ∀y∈s, f x = f y → x = y) :
  fintype.card (f '' s) = fintype.card s :=
by haveI := classical.prop_decidable; exact
calc fintype.card (f '' s) = (s.to_finset.image f).card : fintype.card_of_finset' _ (by simp)
... = s.to_finset.card : finset.card_image_of_inj_on
    (λ x hx y hy hxy, H x (mem_to_finset.1 hx) y (mem_to_finset.1 hy) hxy)
... = fintype.card s : (fintype.card_of_finset' _ (λ a, mem_to_finset)).symm

lemma card_image_of_injective (s : set α) [fintype s]
  {f : α → β} [fintype (f '' s)] (H : function.injective f) :
  fintype.card (f '' s) = fintype.card s :=
card_image_of_inj_on $ λ _ _ _ _ h, H h

section

local attribute [instance] decidable_mem_of_fintype

instance fintype_insert [decidable_eq α] (a : α) (s : set α) [fintype s] : fintype (insert a s : set α) :=
if h : a ∈ s then by rwa [insert_eq, union_eq_self_of_subset_left (singleton_subset_iff.2 h)]
else fintype_insert' _ h

end

@[simp] theorem finite.insert (a : α) {s : set α} : finite s → finite (insert a s)
| ⟨h⟩ := ⟨@set.fintype_insert _ (classical.dec_eq α) _ _ h⟩

lemma to_finset_insert [decidable_eq α] {a : α} {s : set α} (hs : finite s) :
  (hs.insert a).to_finset = insert a hs.to_finset :=
finset.ext $ by simp

@[elab_as_eliminator]
theorem finite.induction_on {C : set α → Prop} {s : set α} (h : finite s)
  (H0 : C ∅) (H1 : ∀ {a s}, a ∉ s → finite s → C s → C (insert a s)) : C s :=
let ⟨t⟩ := h in by exactI
match s.to_finset, @mem_to_finset _ s _ with
| ⟨l, nd⟩, al := begin
    change ∀ a, a ∈ l ↔ a ∈ s at al,
    clear _let_match _match t h, revert s nd al,
    refine multiset.induction_on l _ (λ a l IH, _); intros s nd al,
    { rw show s = ∅, from eq_empty_iff_forall_not_mem.2 (by simpa using al),
      exact H0 },
    { rw ← show insert a {x | x ∈ l} = s, from set.ext (by simpa using al),
      cases multiset.nodup_cons.1 nd with m nd',
      refine H1 _ ⟨finset.subtype.fintype ⟨l, nd'⟩⟩ (IH nd' (λ _, iff.rfl)),
      exact m }
  end
end

@[elab_as_eliminator]
theorem finite.dinduction_on {C : ∀s:set α, finite s → Prop} {s : set α} (h : finite s)
  (H0 : C ∅ finite_empty)
  (H1 : ∀ {a s}, a ∉ s → ∀h:finite s, C s h → C (insert a s) (h.insert a)) :
  C s h :=
have ∀h:finite s, C s h,
  from finite.induction_on h (assume h, H0) (assume a s has hs ih h, H1 has hs (ih _)),
this h

instance fintype_singleton (a : α) : fintype ({a} : set α) :=
unique.fintype

@[simp] theorem card_singleton (a : α) :
  fintype.card ({a} : set α) = 1 :=
fintype.card_of_subsingleton _

@[simp] theorem finite_singleton (a : α) : finite ({a} : set α) :=
⟨set.fintype_singleton _⟩

instance fintype_pure : ∀ a : α, fintype (pure a : set α) :=
set.fintype_singleton

theorem finite_pure (a : α) : finite (pure a : set α) :=
⟨set.fintype_pure a⟩

instance fintype_univ [fintype α] : fintype (@univ α) :=
fintype.of_equiv α $ (equiv.set.univ α).symm

theorem finite_univ [fintype α] : finite (@univ α) := ⟨set.fintype_univ⟩

theorem infinite_univ_iff : (@univ α).infinite ↔ _root_.infinite α :=
⟨λ h₁, ⟨λ h₂, h₁ $ @finite_univ α h₂⟩,
  λ ⟨h₁⟩ ⟨h₂⟩, h₁ $ @fintype.of_equiv _ _ h₂ $ equiv.set.univ _⟩

theorem infinite_univ [h : _root_.infinite α] : infinite (@univ α) :=
infinite_univ_iff.2 h

instance fintype_union [decidable_eq α] (s t : set α) [fintype s] [fintype t] : fintype (s ∪ t : set α) :=
fintype.of_finset (s.to_finset ∪ t.to_finset) $ by simp

theorem finite.union {s t : set α} : finite s → finite t → finite (s ∪ t)
| ⟨hs⟩ ⟨ht⟩ := ⟨@set.fintype_union _ (classical.dec_eq α) _ _ hs ht⟩

instance fintype_sep (s : set α) (p : α → Prop) [fintype s] [decidable_pred p] : fintype ({a ∈ s | p a} : set α) :=
fintype.of_finset (s.to_finset.filter p) $ by simp

instance fintype_inter (s t : set α) [fintype s] [decidable_pred t] : fintype (s ∩ t : set α) :=
set.fintype_sep s t

/-- A `fintype` structure on a set defines a `fintype` structure on its subset. -/
def fintype_subset (s : set α) {t : set α} [fintype s] [decidable_pred t] (h : t ⊆ s) : fintype t :=
by rw ← inter_eq_self_of_subset_right h; apply_instance

theorem finite.subset {s : set α} : finite s → ∀ {t : set α}, t ⊆ s → finite t
| ⟨hs⟩ t h := ⟨@set.fintype_subset _ _ _ hs (classical.dec_pred t) h⟩

instance fintype_image [decidable_eq β] (s : set α) (f : α → β) [fintype s] : fintype (f '' s) :=
fintype.of_finset (s.to_finset.image f) $ by simp

instance fintype_range [decidable_eq β] (f : α → β) [fintype α] : fintype (range f) :=
fintype.of_finset (finset.univ.image f) $ by simp [range]

theorem finite_range (f : α → β) [fintype α] : finite (range f) :=
by haveI := classical.dec_eq β; exact ⟨by apply_instance⟩

theorem finite.image {s : set α} (f : α → β) : finite s → finite (f '' s)
| ⟨h⟩ := ⟨@set.fintype_image _ _ (classical.dec_eq β) _ _ h⟩

lemma finite.dependent_image {s : set α} (hs : finite s) {F : Π i ∈ s, β} {t : set β}
  (H : ∀ y ∈ t, ∃ x (hx : x ∈ s), y = F x hx) : set.finite t :=
begin
  let G : s → β := λ x, F x.1 x.2,
  have A : t ⊆ set.range G,
  { assume y hy,
    rcases H y hy with ⟨x, hx, xy⟩,
    refine ⟨⟨x, hx⟩, xy.symm⟩ },
  letI : fintype s := finite.fintype hs,
  exact (finite_range G).subset A
end

instance fintype_map {α β} [decidable_eq β] :
  ∀ (s : set α) (f : α → β) [fintype s], fintype (f <$> s) := set.fintype_image

theorem finite.map {α β} {s : set α} :
  ∀ (f : α → β), finite s → finite (f <$> s) := finite.image

/-- If a function `f` has a partial inverse and sends a set `s` to a set with `[fintype]` instance,
then `s` has a `fintype` structure as well. -/
def fintype_of_fintype_image (s : set α)
  {f : α → β} {g} (I : is_partial_inv f g) [fintype (f '' s)] : fintype s :=
fintype.of_finset ⟨_, @multiset.nodup_filter_map β α g _
  (@injective_of_partial_inv_right _ _ f g I) (f '' s).to_finset.2⟩ $ λ a,
begin
  suffices : (∃ b x, f x = b ∧ g b = some a ∧ x ∈ s) ↔ a ∈ s,
  by simpa [exists_and_distrib_left.symm, and.comm, and.left_comm, and.assoc],
  rw exists_swap,
  suffices : (∃ x, x ∈ s ∧ g (f x) = some a) ↔ a ∈ s, {simpa [and.comm, and.left_comm, and.assoc]},
  simp [I _, (injective_of_partial_inv I).eq_iff]
end

theorem finite_of_finite_image {s : set α} {f : α → β} (hi : set.inj_on f s) :
  finite (f '' s) → finite s | ⟨h⟩ :=
⟨@fintype.of_injective _ _ h (λa:s, ⟨f a.1, mem_image_of_mem f a.2⟩) $
  assume a b eq, subtype.eq $ hi a.2 b.2 $ subtype.ext_iff_val.1 eq⟩

theorem finite_image_iff {s : set α} {f : α → β} (hi : inj_on f s) :
  finite (f '' s) ↔ finite s :=
⟨finite_of_finite_image hi, finite.image _⟩

theorem finite.preimage {s : set β} {f : α → β}
  (I : set.inj_on f (f⁻¹' s)) (h : finite s) : finite (f ⁻¹' s) :=
finite_of_finite_image I (h.subset (image_preimage_subset f s))

instance fintype_Union [decidable_eq α] {ι : Type*} [fintype ι]
  (f : ι → set α) [∀ i, fintype (f i)] : fintype (⋃ i, f i) :=
fintype.of_finset (finset.univ.bind (λ i, (f i).to_finset)) $ by simp

theorem finite_Union {ι : Type*} [fintype ι] {f : ι → set α} (H : ∀i, finite (f i)) : finite (⋃ i, f i) :=
⟨@set.fintype_Union _ (classical.dec_eq α) _ _ _ (λ i, finite.fintype (H i))⟩

/-- A union of sets with `fintype` structure over a set with `fintype` structure has a `fintype`
structure. -/
def fintype_bUnion [decidable_eq α] {ι : Type*} {s : set ι} [fintype s]
  (f : ι → set α) (H : ∀ i ∈ s, fintype (f i)) : fintype (⋃ i ∈ s, f i) :=
by rw bUnion_eq_Union; exact
@set.fintype_Union _ _ _ _ _ (by rintro ⟨i, hi⟩; exact H i hi)

instance fintype_bUnion' [decidable_eq α] {ι : Type*} {s : set ι} [fintype s]
  (f : ι → set α) [H : ∀ i, fintype (f i)] : fintype (⋃ i ∈ s, f i) :=
fintype_bUnion _ (λ i _, H i)

theorem finite.sUnion {s : set (set α)} (h : finite s) (H : ∀t∈s, finite t) : finite (⋃₀ s) :=
by rw sUnion_eq_Union; haveI := finite.fintype h;
   apply finite_Union; simpa using H

theorem finite.bUnion {α} {ι : Type*} {s : set ι} {f : Π i ∈ s, set α} :
  finite s → (∀ i ∈ s, finite (f i ‹_›)) → finite (⋃ i∈s, f i ‹_›)
| ⟨hs⟩ h := by rw [bUnion_eq_Union]; exactI finite_Union (λ i, h _ _)

instance fintype_lt_nat (n : ℕ) : fintype {i | i < n} :=
fintype.of_finset (finset.range n) $ by simp

instance fintype_le_nat (n : ℕ) : fintype {i | i ≤ n} :=
by simpa [nat.lt_succ_iff] using set.fintype_lt_nat (n+1)

lemma finite_le_nat (n : ℕ) : finite {i | i ≤ n} := ⟨set.fintype_le_nat _⟩

lemma finite_lt_nat (n : ℕ) : finite {i | i < n} := ⟨set.fintype_lt_nat _⟩

instance fintype_prod (s : set α) (t : set β) [fintype s] [fintype t] : fintype (set.prod s t) :=
fintype.of_finset (s.to_finset.product t.to_finset) $ by simp

lemma finite.prod {s : set α} {t : set β} : finite s → finite t → finite (set.prod s t)
| ⟨hs⟩ ⟨ht⟩ := by exactI ⟨set.fintype_prod s t⟩

/-- If `s : set α` is a set with `fintype` instance and `f : α → set β` is a function such that
each `f a`, `a ∈ s`, has a `fintype` structure, then `s >>= f` has a `fintype` structure. -/
def fintype_bind {α β} [decidable_eq β] (s : set α) [fintype s]
  (f : α → set β) (H : ∀ a ∈ s, fintype (f a)) : fintype (s >>= f) :=
set.fintype_bUnion _ H

instance fintype_bind' {α β} [decidable_eq β] (s : set α) [fintype s]
  (f : α → set β) [H : ∀ a, fintype (f a)] : fintype (s >>= f) :=
fintype_bind _ _ (λ i _, H i)

theorem finite_bind {α β} {s : set α} {f : α → set β} :
  finite s → (∀ a ∈ s, finite (f a)) → finite (s >>= f)
| ⟨hs⟩ H := ⟨@fintype_bind _ _ (classical.dec_eq β) _ hs _ (λ a ha, (H a ha).fintype)⟩

instance fintype_seq {α β : Type u} [decidable_eq β]
  (f : set (α → β)) (s : set α) [fintype f] [fintype s] :
  fintype (f <*> s) :=
by rw seq_eq_bind_map; apply set.fintype_bind'

theorem finite.seq {α β : Type u} {f : set (α → β)} {s : set α} :
  finite f → finite s → finite (f <*> s)
| ⟨hf⟩ ⟨hs⟩ := by { haveI := classical.dec_eq β, exactI ⟨set.fintype_seq _ _⟩ }

/-- There are finitely many subsets of a given finite set -/
lemma finite.finite_subsets {α : Type u} {a : set α} (h : finite a) : finite {b | b ⊆ a} :=
begin
  -- we just need to translate the result, already known for finsets,
  -- to the language of finite sets
  let s : set (set α) := coe '' (↑(finset.powerset (finite.to_finset h)) : set (finset α)),
  have : finite s := (finite_mem_finset _).image _,
  apply this.subset,
  refine λ b hb, ⟨(h.subset hb).to_finset, _, finite.coe_to_finset _⟩,
  simpa [finset.subset_iff]
end

lemma exists_min_image [linear_order β] (s : set α) (f : α → β) (h1 : finite s) :
  s.nonempty → ∃ a ∈ s, ∀ b ∈ s, f a ≤ f b
| ⟨x, hx⟩ := by simpa only [exists_prop, finite.mem_to_finset]
  using (finite.to_finset h1).exists_min_image f ⟨x, finite.mem_to_finset.2 hx⟩

lemma exists_max_image [linear_order β] (s : set α) (f : α → β) (h1 : finite s) :
  s.nonempty → ∃ a ∈ s, ∀ b ∈ s, f b ≤ f a
| ⟨x, hx⟩ := by simpa only [exists_prop, finite.mem_to_finset]
  using (finite.to_finset h1).exists_max_image f ⟨x, finite.mem_to_finset.2 hx⟩

end set

namespace finset
variables [decidable_eq β]
variables {s : finset α}

lemma finite_to_set (s : finset α) : set.finite (↑s : set α) :=
set.finite_mem_finset s

@[simp] lemma coe_bind {f : α → finset β} : ↑(s.bind f) = (⋃x ∈ (↑s : set α), ↑(f x) : set β) :=
by simp [set.ext_iff]

@[simp] lemma finite_to_set_to_finset {α : Type*} (s : finset α) :
  (finite_to_set s).to_finset = s :=
by { ext, rw [set.finite.mem_to_finset, mem_coe] }

end finset

namespace set

lemma finite_subset_Union {s : set α} (hs : finite s)
  {ι} {t : ι → set α} (h : s ⊆ ⋃ i, t i) : ∃ I : set ι, finite I ∧ s ⊆ ⋃ i ∈ I, t i :=
begin
  casesI hs,
  choose f hf using show ∀ x : s, ∃ i, x.1 ∈ t i, {simpa [subset_def] using h},
  refine ⟨range f, finite_range f, _⟩,
  rintro x hx,
  simp,
  exact ⟨x, ⟨hx, hf _⟩⟩,
end

lemma eq_finite_Union_of_finite_subset_Union  {ι} {s : ι → set α} {t : set α} (tfin : finite t) (h : t ⊆ ⋃ i, s i) :
  ∃ I : set ι, (finite I) ∧ ∃ σ : {i | i ∈ I} → set α,
     (∀ i, finite (σ i)) ∧ (∀ i, σ i ⊆ s i) ∧ t = ⋃ i, σ i :=
let ⟨I, Ifin, hI⟩ := finite_subset_Union tfin h in
⟨I, Ifin, λ x, s x ∩ t,
    λ i, tfin.subset (inter_subset_right _ _),
    λ i, inter_subset_left _ _,
    begin
      ext x,
      rw mem_Union,
      split,
      { intro x_in,
        rcases mem_Union.mp (hI x_in) with ⟨i, _, ⟨hi, rfl⟩, H⟩,
        use [i, hi, H, x_in] },
      { rintros ⟨i, hi, H⟩,
        exact H }
    end⟩

instance nat.fintype_Iio (n : ℕ) : fintype (Iio n) :=
fintype.of_finset (finset.range n) $ by simp

/--
If `P` is some relation between terms of `γ` and sets in `γ`,
such that every finite set `t : set γ` has some `c : γ` related to it,
then there is a recursively defined sequence `u` in `γ`
so `u n` is related to the image of `{0, 1, ..., n-1}` under `u`.

(We use this later to show sequentially compact sets
are totally bounded.)
-/
lemma seq_of_forall_finite_exists  {γ : Type*}
  {P : γ → set γ → Prop} (h : ∀ t,  finite t → ∃ c, P c t) :
  ∃ u : ℕ → γ, ∀ n, P (u n) (u '' Iio n) :=
⟨λ n, @nat.strong_rec_on' (λ _, γ) n $ λ n ih, classical.some $ h
    (range $ λ m : Iio n, ih m.1 m.2)
    (finite_range _),
λ n, begin
  classical,
  refine nat.strong_rec_on' n (λ n ih, _),
  rw nat.strong_rec_on_beta', convert classical.some_spec (h _ _),
  ext x, split,
  { rintros ⟨m, hmn, rfl⟩, exact ⟨⟨m, hmn⟩, rfl⟩ },
  { rintros ⟨⟨m, hmn⟩, rfl⟩, exact ⟨m, hmn, rfl⟩ }
end⟩

lemma finite_range_ite {p : α → Prop} [decidable_pred p] {f g : α → β} (hf : finite (range f))
  (hg : finite (range g)) : finite (range (λ x, if p x then f x else g x)) :=
(hf.union hg).subset range_ite_subset

lemma finite_range_const {c : β} : finite (range (λ x : α, c)) :=
(finite_singleton c).subset range_const_subset

lemma range_find_greatest_subset {P : α → ℕ → Prop} [∀ x, decidable_pred (P x)] {b : ℕ}:
  range (λ x, nat.find_greatest (P x) b) ⊆ ↑(finset.range (b + 1)) :=
by { rw range_subset_iff, assume x, simp [nat.lt_succ_iff, nat.find_greatest_le] }

lemma finite_range_find_greatest {P : α → ℕ → Prop} [∀ x, decidable_pred (P x)] {b : ℕ} :
  finite (range (λ x, nat.find_greatest (P x) b)) :=
(finset.range (b + 1)).finite_to_set.subset range_find_greatest_subset

lemma card_lt_card {s t : set α} [fintype s] [fintype t] (h : s ⊂ t) :
  fintype.card s < fintype.card t :=
begin
  rw [← s.coe_to_finset, ← t.coe_to_finset, finset.coe_ssubset] at h,
  rw [fintype.card_of_finset' _ (λ x, mem_to_finset),
      fintype.card_of_finset' _ (λ x, mem_to_finset)],
  exact finset.card_lt_card h,
end

lemma card_le_of_subset {s t : set α} [fintype s] [fintype t] (hsub : s ⊆ t) :
  fintype.card s ≤ fintype.card t :=
calc fintype.card s = s.to_finset.card : fintype.card_of_finset' _ (by simp)
... ≤ t.to_finset.card : finset.card_le_of_subset (λ x hx, by simp [set.subset_def, *] at *)
... = fintype.card t : eq.symm (fintype.card_of_finset' _ (by simp))

lemma eq_of_subset_of_card_le {s t : set α} [fintype s] [fintype t]
   (hsub : s ⊆ t) (hcard : fintype.card t ≤ fintype.card s) : s = t :=
(eq_or_ssubset_of_subset hsub).elim id
  (λ h, absurd hcard $ not_le_of_lt $ card_lt_card h)

lemma card_range_of_injective [fintype α] {f : α → β} (hf : injective f)
  [fintype (range f)] : fintype.card (range f) = fintype.card α :=
eq.symm $ fintype.card_congr $ equiv.set.range f hf

lemma finite.exists_maximal_wrt [partial_order β] (f : α → β) (s : set α) (h : set.finite s) :
  s.nonempty → ∃a∈s, ∀a'∈s, f a ≤ f a' → f a = f a' :=
begin
  classical,
  refine h.induction_on _ _,
  { assume h, exact absurd h empty_not_nonempty },
  assume a s his _ ih _,
  cases s.eq_empty_or_nonempty with h h,
  { use a, simp [h] },
  rcases ih h with ⟨b, hb, ih⟩,
  by_cases f b ≤ f a,
  { refine ⟨a, set.mem_insert _ _, assume c hc hac, le_antisymm hac _⟩,
    rcases set.mem_insert_iff.1 hc with rfl | hcs,
    { refl },
    { rwa [← ih c hcs (le_trans h hac)] } },
  { refine ⟨b, set.mem_insert_of_mem _ hb, assume c hc hbc, _⟩,
    rcases set.mem_insert_iff.1 hc with rfl | hcs,
    { exact (h hbc).elim },
    { exact ih c hcs hbc } }
end

lemma finite.card_to_finset {s : set α} [fintype s] (h : s.finite) :
  h.to_finset.card = fintype.card s :=
by { rw [← finset.card_attach, finset.attach_eq_univ, ← fintype.card], congr' 2, funext,
     rw set.finite.mem_to_finset }

section

local attribute [instance, priority 1] classical.prop_decidable

lemma to_finset_inter {α : Type*} [fintype α] (s t : set α) :
  (s ∩ t).to_finset = s.to_finset ∩ t.to_finset :=
by ext; simp

end

section

variables [semilattice_sup α] [nonempty α] {s : set α}

/--A finite set is bounded above.-/
protected lemma finite.bdd_above (hs : finite s) : bdd_above s :=
finite.induction_on hs bdd_above_empty $ λ a s _ _ h, h.insert a

/--A finite union of sets which are all bounded above is still bounded above.-/
lemma finite.bdd_above_bUnion {I : set β} {S : β → set α} (H : finite I) :
  (bdd_above (⋃i∈I, S i)) ↔ (∀i ∈ I, bdd_above (S i)) :=
finite.induction_on H
  (by simp only [bUnion_empty, bdd_above_empty, ball_empty_iff])
  (λ a s ha _ hs, by simp only [bUnion_insert, ball_insert_iff, bdd_above_union, hs])

end

section

variables [semilattice_inf α] [nonempty α] {s : set α}

/--A finite set is bounded below.-/
protected lemma finite.bdd_below (hs : finite s) : bdd_below s :=
@finite.bdd_above (order_dual α) _ _ _ hs

/--A finite union of sets which are all bounded below is still bounded below.-/
lemma finite.bdd_below_bUnion {I : set β} {S : β → set α} (H : finite I) :
  (bdd_below (⋃i∈I, S i)) ↔ (∀i ∈ I, bdd_below (S i)) :=
@finite.bdd_above_bUnion (order_dual α) _ _ _ _ _ H

end

end set

namespace finset

section preimage

/-- Preimage of `s : finset β` under a map `f` injective of `f ⁻¹' s` as a `finset`.  -/
noncomputable def preimage {f : α → β} (s : finset β)
  (hf : set.inj_on f (f ⁻¹' ↑s)) : finset α :=
(s.finite_to_set.preimage hf).to_finset

@[simp] lemma mem_preimage {f : α → β} {s : finset β} {hf : set.inj_on f (f ⁻¹' ↑s)} {x : α} :
  x ∈ preimage s hf ↔ f x ∈ s :=
set.finite.mem_to_finset

@[simp, norm_cast] lemma coe_preimage {f : α → β} (s : finset β)
  (hf : set.inj_on f (f ⁻¹' ↑s)) : (↑(preimage s hf) : set α) = f ⁻¹' ↑s :=
set.finite.coe_to_finset _

lemma image_preimage [decidable_eq β] (f : α → β) (s : finset β)
  (hf : set.bij_on f (f ⁻¹' ↑s) ↑s) :
  image f (preimage s hf.inj_on) = s :=
finset.coe_inj.1 $
suffices f '' (f ⁻¹' ↑s) = ↑s, by simpa,
(set.subset.antisymm (image_preimage_subset _ _) hf.surj_on)

end preimage

@[to_additive]
lemma prod_preimage [comm_monoid β] (f : α → γ) (s : finset γ)
  (hf : set.bij_on f (f ⁻¹' ↑s) ↑s) (g : γ → β) :
  ∏ x in preimage s hf.inj_on, g (f x) = ∏ x in s, g x :=
by classical;
calc
  ∏ x in preimage s hf.inj_on, g (f x)
      = ∏ x in image f (preimage s hf.inj_on), g x :
          begin
            rw prod_image,
            intros x hx y hy hxy,
            apply hf.inj_on,
            repeat { try { rw mem_preimage at hx hy,
                          rw [set.mem_preimage, mem_coe] },
                    assumption },
          end
  ... = ∏ x in s, g x : by rw [image_preimage]

/-- A finset is bounded above. -/
protected lemma bdd_above [semilattice_sup α] [nonempty α] (s : finset α) :
  bdd_above (↑s : set α) :=
s.finite_to_set.bdd_above

/-- A finset is bounded below. -/
protected lemma bdd_below [semilattice_inf α] [nonempty α] (s : finset α) :
  bdd_below (↑s : set α) :=
s.finite_to_set.bdd_below

end finset

lemma fintype.exists_max [fintype α] [nonempty α]
  {β : Type*} [linear_order β] (f : α → β) :
  ∃ x₀ : α, ∀ x, f x ≤ f x₀ :=
begin
  rcases set.finite_univ.exists_maximal_wrt f _ univ_nonempty with ⟨x, _, hx⟩,
  exact ⟨x, λ y, (le_total (f x) (f y)).elim (λ h, ge_of_eq $ hx _ trivial h) id⟩
end
