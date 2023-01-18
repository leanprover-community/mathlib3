/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import algebra.hom.embedding
import data.fin.basic
import data.finset.basic
import data.int.order.basic

/-! # Image and map operations on finite sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Thie file provides the finite analog of `set.image`, along with some other similar functions.

Note there are two ways to take the image over a finset; via `finset.image` which applies the
function then removes duplicates (requiring `decidable_eq`), or via `finset.map` which exploits
injectivity of the function to avoid needing to deduplicate. Choosing between these is similar to
choosing between `insert` and `finset.cons`, or between `finset.union` and `finset.disj_union`.

## Main definitions

* `finset.image`: Given a function `f : α → β`, `s.image f` is the image finset in `β`.
* `finset.map`: Given an embedding `f : α ↪ β`, `s.map f` is the image finset in `β`.
* `finset.subtype`: `s.subtype p` is the the finset of `subtype p` whose elements belong to `s`.
* `finset.fin`:`s.fin n` is the finset of all elements of `s` less than `n`.

-/

variables {α β γ : Type*}
open multiset
open function

namespace finset

/-! ### map -/
section map
open function

/-- When `f` is an embedding of `α` in `β` and `s` is a finset in `α`, then `s.map f` is the image
finset in `β`. The embedding condition guarantees that there are no duplicates in the image. -/
def map (f : α ↪ β) (s : finset α) : finset β := ⟨s.1.map f, s.2.map f.2⟩

@[simp] theorem map_val (f : α ↪ β) (s : finset α) : (map f s).1 = s.1.map f := rfl

@[simp] theorem map_empty (f : α ↪ β) : (∅ : finset α).map f = ∅ := rfl

variables {f : α ↪ β} {s : finset α}

@[simp] theorem mem_map {b : β} : b ∈ s.map f ↔ ∃ a ∈ s, f a = b :=
mem_map.trans $ by simp only [exists_prop]; refl

@[simp] lemma mem_map_equiv {f : α ≃ β} {b : β} : b ∈ s.map f.to_embedding ↔ f.symm b ∈ s :=
by { rw mem_map, exact ⟨by { rintro ⟨a, H, rfl⟩, simpa }, λ h, ⟨_, h, by simp⟩⟩ }

lemma mem_map' (f : α ↪ β) {a} {s : finset α} : f a ∈ s.map f ↔ a ∈ s := mem_map_of_injective f.2

lemma mem_map_of_mem (f : α ↪ β) {a} {s : finset α} : a ∈ s → f a ∈ s.map f := (mem_map' _).2

lemma forall_mem_map {f : α ↪ β} {s : finset α} {p : Π a, a ∈ s.map f → Prop} :
  (∀ y ∈ s.map f, p y H) ↔ ∀ x ∈ s, p (f x) (mem_map_of_mem _ H) :=
⟨λ h y hy, h (f y) (mem_map_of_mem _ hy), λ h x hx,
  by { obtain ⟨y, hy, rfl⟩ := mem_map.1 hx, exact h _ hy }⟩

lemma apply_coe_mem_map (f : α ↪ β) (s : finset α) (x : s) : f x ∈ s.map f :=
mem_map_of_mem f x.prop

@[simp, norm_cast] theorem coe_map (f : α ↪ β) (s : finset α) : (s.map f : set β) = f '' s :=
set.ext $ λ x, mem_map.trans set.mem_image_iff_bex.symm

theorem coe_map_subset_range (f : α ↪ β) (s : finset α) : (s.map f : set β) ⊆ set.range f :=
calc ↑(s.map f) = f '' s      : coe_map f s
            ... ⊆ set.range f : set.image_subset_range f ↑s

/-- If the only elements outside `s` are those left fixed by `σ`, then mapping by `σ` has no effect.
-/
lemma map_perm {σ : equiv.perm α} (hs : {a | σ a ≠ a} ⊆ s) : s.map (σ : α ↪ α) = s :=
coe_injective $ (coe_map _ _).trans $ set.image_perm hs

theorem map_to_finset [decidable_eq α] [decidable_eq β] {s : multiset α} :
  s.to_finset.map f = (s.map f).to_finset :=
ext $ λ _, by simp only [mem_map, multiset.mem_map, exists_prop, multiset.mem_to_finset]

@[simp] theorem map_refl : s.map (embedding.refl _) = s :=
ext $ λ _, by simpa only [mem_map, exists_prop] using exists_eq_right

@[simp] theorem map_cast_heq {α β} (h : α = β) (s : finset α) :
  s.map (equiv.cast h).to_embedding == s :=
by { subst h, simp }

theorem map_map (f : α ↪ β) (g : β ↪ γ) (s : finset α) : (s.map f).map g = s.map (f.trans g) :=
eq_of_veq $ by simp only [map_val, multiset.map_map]; refl

lemma map_comm {β'} {f : β ↪ γ} {g : α ↪ β} {f' : α ↪ β'} {g' : β' ↪ γ}
  (h_comm : ∀ a, f (g a) = g' (f' a)) :
  (s.map g).map f = (s.map f').map g' :=
by simp_rw [map_map, embedding.trans, function.comp, h_comm]

lemma _root_.function.semiconj.finset_map {f : α ↪ β} {ga : α ↪ α} {gb : β ↪ β}
  (h : function.semiconj f ga gb) :
  function.semiconj (map f) (map ga) (map gb) :=
λ s, map_comm h

lemma _root_.function.commute.finset_map {f g : α ↪ α} (h : function.commute f g) :
  function.commute (map f) (map g) :=
h.finset_map

@[simp] theorem map_subset_map {s₁ s₂ : finset α} : s₁.map f ⊆ s₂.map f ↔ s₁ ⊆ s₂ :=
⟨λ h x xs, (mem_map' _).1 $ h $ (mem_map' f).2 xs,
 λ h, by simp [subset_def, map_subset_map h]⟩

/-- Associate to an embedding `f` from `α` to `β` the order embedding that maps a finset to its
image under `f`. -/
def map_embedding (f : α ↪ β) : finset α ↪o finset β :=
order_embedding.of_map_le_iff (map f) (λ _ _, map_subset_map)

@[simp] theorem map_inj {s₁ s₂ : finset α} : s₁.map f = s₂.map f ↔ s₁ = s₂ :=
(map_embedding f).injective.eq_iff

lemma map_injective (f : α ↪ β) : injective (map f) := (map_embedding f).injective

@[simp] theorem map_embedding_apply : map_embedding f s = map f s := rfl

lemma filter_map {p : β → Prop} [decidable_pred p] :
  (s.map f).filter p = (s.filter (p ∘ f)).map f :=
eq_of_veq (map_filter _ _ _)

lemma map_filter {f : α ≃ β} {p : α → Prop} [decidable_pred p] :
  (s.filter p).map f.to_embedding = (s.map f.to_embedding).filter (p ∘ f.symm) :=
by simp only [filter_map, function.comp, equiv.to_embedding_apply, equiv.symm_apply_apply]

@[simp] lemma disjoint_map {s t : finset α} (f : α ↪ β) :
  disjoint (s.map f) (t.map f) ↔ disjoint s t :=
begin
  simp only [disjoint_iff_ne, mem_map, exists_prop, exists_imp_distrib, and_imp],
  refine ⟨λ h a ha b hb hab, h _ _ ha rfl _ _ hb rfl $ congr_arg _ hab, _⟩,
  rintro h _ a ha rfl _ b hb rfl,
  exact f.injective.ne (h _ ha _ hb),
end

theorem map_disj_union {f : α ↪ β} (s₁ s₂ : finset α) (h) (h' := (disjoint_map _).mpr h) :
  (s₁.disj_union s₂ h).map f = (s₁.map f).disj_union (s₂.map f) h' :=
eq_of_veq $ multiset.map_add _ _ _

/-- A version of `finset.map_disj_union` for writing in the other direction. -/
theorem map_disj_union' {f : α ↪ β} (s₁ s₂ : finset α) (h') (h := (disjoint_map _).mp h') :
  (s₁.disj_union s₂ h).map f = (s₁.map f).disj_union (s₂.map f) h' :=
map_disj_union _ _ _

theorem map_union [decidable_eq α] [decidable_eq β]
  {f : α ↪ β} (s₁ s₂ : finset α) : (s₁ ∪ s₂).map f = s₁.map f ∪ s₂.map f :=
coe_injective $ by simp only [coe_map, coe_union, set.image_union]

theorem map_inter [decidable_eq α] [decidable_eq β]
  {f : α ↪ β} (s₁ s₂ : finset α) : (s₁ ∩ s₂).map f = s₁.map f ∩ s₂.map f :=
coe_injective $ by simp only [coe_map, coe_inter, set.image_inter f.injective]

@[simp] theorem map_singleton (f : α ↪ β) (a : α) : map f {a} = {f a} :=
coe_injective $ by simp only [coe_map, coe_singleton, set.image_singleton]

@[simp] lemma map_insert [decidable_eq α] [decidable_eq β] (f : α ↪ β) (a : α) (s : finset α) :
  (insert a s).map f = insert (f a) (s.map f) :=
by simp only [insert_eq, map_union, map_singleton]

@[simp] lemma map_cons (f : α ↪ β) (a : α) (s : finset α) (ha : a ∉ s) :
  (cons a s ha).map f = cons (f a) (s.map f) (by simpa using ha) :=
eq_of_veq $ multiset.map_cons f a s.val

@[simp] theorem map_eq_empty : s.map f = ∅ ↔ s = ∅ :=
⟨λ h, eq_empty_of_forall_not_mem $
 λ a m, ne_empty_of_mem (mem_map_of_mem _ m) h, λ e, e.symm ▸ rfl⟩

@[simp] lemma map_nonempty : (s.map f).nonempty ↔ s.nonempty :=
by rw [nonempty_iff_ne_empty, nonempty_iff_ne_empty, ne.def, map_eq_empty]

alias map_nonempty ↔ _ nonempty.map

lemma attach_map_val {s : finset α} : s.attach.map (embedding.subtype _) = s :=
eq_of_veq $ by rw [map_val, attach_val]; exact attach_map_val _

lemma disjoint_range_add_left_embedding (a b : ℕ) :
  disjoint (range a) (map (add_left_embedding a) (range b)) :=
begin
  refine disjoint_iff_inf_le.mpr _,
  intros k hk,
  simp only [exists_prop, mem_range, inf_eq_inter, mem_map, add_left_embedding_apply,
    mem_inter] at hk,
  obtain ⟨a, haQ, ha⟩ := hk.2,
  simpa [← ha] using hk.1,
end

lemma disjoint_range_add_right_embedding (a b : ℕ) :
  disjoint (range a) (map (add_right_embedding a) (range b)) :=
begin
  refine disjoint_iff_inf_le.mpr _,
  intros k hk,
  simp only [exists_prop, mem_range, inf_eq_inter, mem_map, add_left_embedding_apply,
    mem_inter] at hk,
  obtain ⟨a, haQ, ha⟩ := hk.2,
  simpa [← ha] using hk.1,
end

theorem map_disj_Union {f : α ↪ β} {s : finset α} {t : β → finset γ} {h} :
  (s.map f).disj_Union t h = s.disj_Union (λa, t (f a))
    (λ a ha b hb hab, h (mem_map_of_mem _ ha) (mem_map_of_mem _ hb) (f.injective.ne hab)) :=
eq_of_veq $ multiset.bind_map _ _ _

theorem disj_Union_map {s : finset α} {t : α → finset β} {f : β ↪ γ} {h} :
  (s.disj_Union t h).map f = s.disj_Union (λa, (t a).map f)
    (λ a ha b hb hab, disjoint_left.mpr $ λ x hxa hxb, begin
      obtain ⟨xa, hfa, rfl⟩ := mem_map.mp hxa,
      obtain ⟨xb, hfb, hfab⟩ := mem_map.mp hxb,
      obtain rfl := f.injective hfab,
      exact disjoint_left.mp (h ha hb hab) hfa hfb,
    end) :=
eq_of_veq $ multiset.map_bind _ _ _

end map

lemma range_add_one' (n : ℕ) :
  range (n + 1) = insert 0 ((range n).map ⟨λi, i + 1, assume i j, nat.succ.inj⟩) :=
by ext (⟨⟩ | ⟨n⟩); simp [nat.succ_eq_add_one, nat.zero_lt_succ n]

/-! ### image -/

section image
variables [decidable_eq β]

/-- `image f s` is the forward image of `s` under `f`. -/
def image (f : α → β) (s : finset α) : finset β := (s.1.map f).to_finset

@[simp] theorem image_val (f : α → β) (s : finset α) : (image f s).1 = (s.1.map f).dedup := rfl

@[simp] theorem image_empty (f : α → β) : (∅ : finset α).image f = ∅ := rfl

variables {f g : α → β} {s : finset α} {t : finset β} {a : α} {b c : β}

@[simp] lemma mem_image : b ∈ s.image f ↔ ∃ a ∈ s, f a = b :=
by simp only [mem_def, image_val, mem_dedup, multiset.mem_map, exists_prop]

lemma mem_image_of_mem (f : α → β) {a} (h : a ∈ s) : f a ∈ s.image f := mem_image.2 ⟨_, h, rfl⟩

lemma forall_image {p : β → Prop} : (∀ b ∈ s.image f, p b) ↔ ∀ a ∈ s, p (f a) :=
by simp only [mem_image, forall_exists_index, forall_apply_eq_imp_iff₂]

@[simp] lemma mem_image_const : c ∈ s.image (const α b) ↔ s.nonempty ∧ b = c :=
by { rw mem_image, simp only [exists_prop, const_apply, exists_and_distrib_right], refl }

lemma mem_image_const_self : b ∈ s.image (const α b) ↔ s.nonempty :=
mem_image_const.trans $ and_iff_left rfl

instance can_lift (c) (p) [can_lift β α c p] :
  can_lift (finset β) (finset α) (image c) (λ s, ∀ x ∈ s, p x) :=
{ prf :=
    begin
      rintro ⟨⟨l⟩, hd : l.nodup⟩ hl,
      lift l to list α using hl,
      exact ⟨⟨l, hd.of_map _⟩, ext $ λ a, by simp⟩,
    end }

lemma image_congr (h : (s : set α).eq_on f g) : finset.image f s = finset.image g s :=
by { ext, simp_rw mem_image, exact bex_congr (λ x hx, by rw h hx) }

lemma _root_.function.injective.mem_finset_image (hf : injective f) : f a ∈ s.image f ↔ a ∈ s :=
begin
  refine ⟨λ h, _, finset.mem_image_of_mem f⟩,
  obtain ⟨y, hy, heq⟩ := mem_image.1 h,
  exact hf heq ▸ hy,
end

lemma filter_mem_image_eq_image (f : α → β) (s : finset α) (t : finset β) (h : ∀ x ∈ s, f x ∈ t) :
  t.filter (λ y, y ∈ s.image f) = s.image f :=
by { ext, rw [mem_filter, mem_image],
     simp only [and_imp, exists_prop, and_iff_right_iff_imp, exists_imp_distrib],
     rintros x xel rfl, exact h _ xel }

lemma fiber_nonempty_iff_mem_image (f : α → β) (s : finset α) (y : β) :
  (s.filter (λ x, f x = y)).nonempty ↔ y ∈ s.image f :=
by simp [finset.nonempty]

@[simp, norm_cast] lemma coe_image {f : α → β} : ↑(s.image f) = f '' ↑s :=
set.ext $ λ _, mem_image.trans set.mem_image_iff_bex.symm

protected lemma nonempty.image (h : s.nonempty) (f : α → β) : (s.image f).nonempty :=
let ⟨a, ha⟩ := h in ⟨f a, mem_image_of_mem f ha⟩

@[simp] lemma nonempty.image_iff (f : α → β) : (s.image f).nonempty ↔ s.nonempty :=
⟨λ ⟨y, hy⟩, let ⟨x, hx, _⟩ := mem_image.mp hy in ⟨x, hx⟩, λ h, h.image f⟩

theorem image_to_finset [decidable_eq α] {s : multiset α} :
  s.to_finset.image f = (s.map f).to_finset :=
ext $ λ _, by simp only [mem_image, multiset.mem_to_finset, exists_prop, multiset.mem_map]

lemma image_val_of_inj_on (H : set.inj_on f s) : (image f s).1 = s.1.map f := (s.2.map_on H).dedup

@[simp] lemma image_id [decidable_eq α] : s.image id = s :=
ext $ λ _, by simp only [mem_image, exists_prop, id, exists_eq_right]

@[simp] theorem image_id' [decidable_eq α] : s.image (λ x, x) = s := image_id

theorem image_image [decidable_eq γ] {g : β → γ} : (s.image f).image g = s.image (g ∘ f) :=
eq_of_veq $ by simp only [image_val, dedup_map_dedup_eq, multiset.map_map]

lemma image_comm {β'} [decidable_eq β'] [decidable_eq γ] {f : β → γ} {g : α → β}
  {f' : α → β'} {g' : β' → γ} (h_comm : ∀ a, f (g a) = g' (f' a)) :
  (s.image g).image f = (s.image f').image g' :=
by simp_rw [image_image, comp, h_comm]

lemma _root_.function.semiconj.finset_image [decidable_eq α] {f : α → β} {ga : α → α} {gb : β → β}
  (h : function.semiconj f ga gb) :
  function.semiconj (image f) (image ga) (image gb) :=
λ s, image_comm h

lemma _root_.function.commute.finset_image [decidable_eq α] {f g : α → α}
  (h : function.commute f g) :
  function.commute (image f) (image g) :=
h.finset_image

theorem image_subset_image {s₁ s₂ : finset α} (h : s₁ ⊆ s₂) : s₁.image f ⊆ s₂.image f :=
by simp only [subset_def, image_val, subset_dedup', dedup_subset',
  multiset.map_subset_map h]

lemma image_subset_iff : s.image f ⊆ t ↔ ∀ x ∈ s, f x ∈ t :=
calc s.image f ⊆ t ↔ f '' ↑s ⊆ ↑t : by norm_cast
               ... ↔ _ : set.image_subset_iff

theorem image_mono (f : α → β) : monotone (finset.image f) := λ _ _, image_subset_image

lemma image_subset_image_iff {t : finset α} (hf : injective f) : s.image f ⊆ t.image f ↔ s ⊆ t :=
by { simp_rw ←coe_subset, push_cast, exact set.image_subset_image_iff hf }

theorem coe_image_subset_range : ↑(s.image f) ⊆ set.range f :=
calc ↑(s.image f) = f '' ↑s     : coe_image
              ... ⊆ set.range f : set.image_subset_range f ↑s

theorem image_filter {p : β → Prop} [decidable_pred p] :
  (s.image f).filter p = (s.filter (p ∘ f)).image f :=
ext $ λ b, by simp only [mem_filter, mem_image, exists_prop]; exact
⟨by rintro ⟨⟨x, h1, rfl⟩, h2⟩; exact ⟨x, ⟨h1, h2⟩, rfl⟩,
 by rintro ⟨x, ⟨h1, h2⟩, rfl⟩; exact ⟨⟨x, h1, rfl⟩, h2⟩⟩

theorem image_union [decidable_eq α] {f : α → β} (s₁ s₂ : finset α) :
  (s₁ ∪ s₂).image f = s₁.image f ∪ s₂.image f :=
ext $ λ _, by simp only [mem_image, mem_union, exists_prop, or_and_distrib_right,
  exists_or_distrib]

lemma image_inter_subset [decidable_eq α] (f : α → β) (s t : finset α) :
  (s ∩ t).image f ⊆ s.image f ∩ t.image f :=
subset_inter (image_subset_image $ inter_subset_left _ _) $
  image_subset_image $ inter_subset_right _ _

lemma image_inter_of_inj_on [decidable_eq α] {f : α → β} (s t : finset α)
  (hf : set.inj_on f (s ∪ t)) :
  (s ∩ t).image f = s.image f ∩ t.image f :=
(image_inter_subset _ _ _).antisymm $ λ x, begin
  simp only [mem_inter, mem_image],
  rintro ⟨⟨a, ha, rfl⟩, b, hb, h⟩,
  exact ⟨a, ⟨ha, by rwa ←hf (or.inr hb) (or.inl ha) h⟩, rfl⟩,
end

lemma image_inter [decidable_eq α] (s₁ s₂ : finset α) (hf : injective f) :
  (s₁ ∩ s₂).image f = s₁.image f ∩ s₂.image f :=
image_inter_of_inj_on _ _ $ hf.inj_on _

@[simp] theorem image_singleton (f : α → β) (a : α) : image f {a} = {f a} :=
ext $ λ x, by simpa only [mem_image, exists_prop, mem_singleton, exists_eq_left] using eq_comm

@[simp] theorem image_insert [decidable_eq α] (f : α → β) (a : α) (s : finset α) :
  (insert a s).image f = insert (f a) (s.image f) :=
by simp only [insert_eq, image_singleton, image_union]

lemma erase_image_subset_image_erase [decidable_eq α] (f : α → β) (s : finset α) (a : α) :
  (s.image f).erase (f a) ⊆ (s.erase a).image f :=
begin
  simp only [subset_iff, and_imp, exists_prop, mem_image, exists_imp_distrib, mem_erase],
  rintro b hb x hx rfl,
  exact ⟨_, ⟨ne_of_apply_ne f hb, hx⟩, rfl⟩,
end

@[simp] lemma image_erase [decidable_eq α] {f : α → β} (hf : injective f) (s : finset α) (a : α) :
  (s.erase a).image f = (s.image f).erase (f a) :=
begin
  refine (erase_image_subset_image_erase _ _ _).antisymm' (λ b, _),
  simp only [mem_image, exists_prop, mem_erase],
  rintro ⟨a', ⟨haa', ha'⟩, rfl⟩,
  exact ⟨hf.ne haa', a', ha', rfl⟩,
end

@[simp] theorem image_eq_empty : s.image f = ∅ ↔ s = ∅ :=
⟨λ h, eq_empty_of_forall_not_mem $
 λ a m, ne_empty_of_mem (mem_image_of_mem _ m) h, λ e, e.symm ▸ rfl⟩

@[simp] lemma _root_.disjoint.of_image_finset
  {s t : finset α} {f : α → β} (h : disjoint (s.image f) (t.image f)) :
  disjoint s t :=
disjoint_iff_ne.2 $ λ a ha b hb, ne_of_apply_ne f $ h.forall_ne_finset
  (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)

lemma mem_range_iff_mem_finset_range_of_mod_eq' [decidable_eq α] {f : ℕ → α} {a : α} {n : ℕ}
  (hn : 0 < n) (h : ∀ i, f (i % n) = f i) :
  a ∈ set.range f ↔ a ∈ (finset.range n).image (λi, f i) :=
begin
  split,
  { rintros ⟨i, hi⟩,
    simp only [mem_image, exists_prop, mem_range],
    exact ⟨i % n, nat.mod_lt i hn, (rfl.congr hi).mp (h i)⟩ },
  { rintro h,
    simp only [mem_image, exists_prop, set.mem_range, mem_range] at *,
    rcases h with ⟨i, hi, ha⟩,
    exact ⟨i, ha⟩ }
end

lemma mem_range_iff_mem_finset_range_of_mod_eq [decidable_eq α] {f : ℤ → α} {a : α} {n : ℕ}
  (hn : 0 < n) (h : ∀ i, f (i % n) = f i) :
  a ∈ set.range f ↔ a ∈ (finset.range n).image (λi, f i) :=
suffices (∃ i, f (i % n) = a) ↔ ∃ i, i < n ∧ f ↑i = a, by simpa [h],
have hn' : 0 < (n : ℤ), from int.coe_nat_lt.mpr hn,
iff.intro
  (assume ⟨i, hi⟩,
    have 0 ≤ i % ↑n, from int.mod_nonneg _ (ne_of_gt hn'),
    ⟨int.to_nat (i % n),
      by rw [←int.coe_nat_lt, int.to_nat_of_nonneg this]; exact ⟨int.mod_lt_of_pos i hn', hi⟩⟩)
  (assume ⟨i, hi, ha⟩,
    ⟨i, by rw [int.mod_eq_of_lt (int.coe_zero_le _) (int.coe_nat_lt_coe_nat_of_lt hi), ha]⟩)

lemma range_add (a b : ℕ) : range (a + b) = range a ∪ (range b).map (add_left_embedding a) :=
by { rw [←val_inj, union_val], exact multiset.range_add_eq_union a b }

@[simp] lemma attach_image_val [decidable_eq α] {s : finset α} : s.attach.image subtype.val = s :=
eq_of_veq $ by rw [image_val, attach_val, multiset.attach_map_val, dedup_eq_self]

@[simp] lemma attach_image_coe [decidable_eq α] {s : finset α} : s.attach.image coe = s :=
finset.attach_image_val

@[simp] lemma attach_insert [decidable_eq α] {a : α} {s : finset α} :
  attach (insert a s) = insert (⟨a, mem_insert_self a s⟩ : {x // x ∈ insert a s})
    ((attach s).image (λx, ⟨x.1, mem_insert_of_mem x.2⟩)) :=
ext $ λ ⟨x, hx⟩, ⟨or.cases_on (mem_insert.1 hx)
  (λ h : x = a, λ _, mem_insert.2 $ or.inl $ subtype.eq h)
  (λ h : x ∈ s, λ _, mem_insert_of_mem $ mem_image.2 $ ⟨⟨x, h⟩, mem_attach _ _, subtype.eq rfl⟩),
λ _, finset.mem_attach _ _⟩

theorem map_eq_image (f : α ↪ β) (s : finset α) : s.map f = s.image f :=
eq_of_veq (s.map f).2.dedup.symm

@[simp] lemma disjoint_image
  {s t : finset α} {f : α → β} (hf : injective f) :
  disjoint (s.image f) (t.image f) ↔ disjoint s t :=
by convert disjoint_map ⟨_, hf⟩; simp [map_eq_image]

lemma image_const {s : finset α} (h : s.nonempty) (b : β) : s.image (λa, b) = singleton b :=
ext $ assume b', by simp only [mem_image, exists_prop, exists_and_distrib_right,
  h.bex, true_and, mem_singleton, eq_comm]

@[simp] lemma map_erase [decidable_eq α] (f : α ↪ β) (s : finset α) (a : α) :
  (s.erase a).map f = (s.map f).erase (f a) :=
by { simp_rw map_eq_image, exact s.image_erase f.2 a }

theorem image_bUnion [decidable_eq γ] {f : α → β} {s : finset α} {t : β → finset γ} :
  (s.image f).bUnion t = s.bUnion (λa, t (f a)) :=
by haveI := classical.dec_eq α; exact
finset.induction_on s rfl (λ a s has ih,
  by simp only [image_insert, bUnion_insert, ih])

theorem bUnion_image [decidable_eq γ] {s : finset α} {t : α → finset β} {f : β → γ} :
  (s.bUnion t).image f = s.bUnion (λa, (t a).image f) :=
by haveI := classical.dec_eq α; exact
finset.induction_on s rfl (λ a s has ih,
  by simp only [bUnion_insert, image_union, ih])

lemma image_bUnion_filter_eq [decidable_eq α] (s : finset β) (g : β → α) :
  (s.image g).bUnion (λa, s.filter $ (λc, g c = a)) = s :=
bUnion_filter_eq_of_maps_to (λ x, mem_image_of_mem g)

lemma bUnion_singleton {f : α → β} : s.bUnion (λa, {f a}) = s.image f :=
ext $ λ x, by simp only [mem_bUnion, mem_image, mem_singleton, eq_comm]

end image

/-! ### Subtype -/
section subtype

/-- Given a finset `s` and a predicate `p`, `s.subtype p` is the finset of `subtype p` whose
elements belong to `s`. -/
protected def subtype {α} (p : α → Prop) [decidable_pred p] (s : finset α) : finset (subtype p) :=
(s.filter p).attach.map ⟨λ x, ⟨x.1, (finset.mem_filter.1 x.2).2⟩,
λ x y H, subtype.eq $ subtype.mk.inj H⟩

@[simp] lemma mem_subtype {p : α → Prop} [decidable_pred p] {s : finset α} :
  ∀ {a : subtype p}, a ∈ s.subtype p ↔ (a : α) ∈ s
| ⟨a, ha⟩ := by simp [finset.subtype, ha]

lemma subtype_eq_empty {p : α → Prop} [decidable_pred p] {s : finset α} :
  s.subtype p = ∅ ↔ ∀ x, p x → x ∉ s :=
by simp [ext_iff, subtype.forall, subtype.coe_mk]; refl

@[mono] lemma subtype_mono {p : α → Prop} [decidable_pred p] : monotone (finset.subtype p) :=
λ s t h x hx, mem_subtype.2 $ h $ mem_subtype.1 hx

/-- `s.subtype p` converts back to `s.filter p` with
`embedding.subtype`. -/
@[simp] lemma subtype_map (p : α → Prop) [decidable_pred p] {s : finset α} :
  (s.subtype p).map (embedding.subtype _) = s.filter p :=
begin
  ext x,
  simp [and_comm _ (_ = _), @and.left_comm _ (_ = _), and_comm (p x) (x ∈ s)]
end

/-- If all elements of a `finset` satisfy the predicate `p`,
`s.subtype p` converts back to `s` with `embedding.subtype`. -/
lemma subtype_map_of_mem {p : α → Prop} [decidable_pred p] {s : finset α} (h : ∀ x ∈ s, p x) :
  (s.subtype p).map (embedding.subtype _) = s :=
by rw [subtype_map, filter_true_of_mem h]

/-- If a `finset` of a subtype is converted to the main type with
`embedding.subtype`, all elements of the result have the property of
the subtype. -/
lemma property_of_mem_map_subtype {p : α → Prop} (s : finset {x // p x}) {a : α}
  (h : a ∈ s.map (embedding.subtype _)) : p a :=
begin
  rcases mem_map.1 h with ⟨x, hx, rfl⟩,
  exact x.2
end

/-- If a `finset` of a subtype is converted to the main type with
`embedding.subtype`, the result does not contain any value that does
not satisfy the property of the subtype. -/
lemma not_mem_map_subtype_of_not_property {p : α → Prop} (s : finset {x // p x})
  {a : α} (h : ¬ p a) : a ∉ (s.map (embedding.subtype _)) :=
mt s.property_of_mem_map_subtype h

/-- If a `finset` of a subtype is converted to the main type with
`embedding.subtype`, the result is a subset of the set giving the
subtype. -/
lemma map_subtype_subset {t : set α} (s : finset t) : ↑(s.map (embedding.subtype _)) ⊆ t :=
begin
  intros a ha,
  rw mem_coe at ha,
  convert property_of_mem_map_subtype s ha
end

end subtype

/-! ### Fin -/

/--
Given a finset `s` of natural numbers and a bound `n`,
`s.fin n` is the finset of all elements of `s` less than `n`.
-/
protected def fin (n : ℕ) (s : finset ℕ) : finset (fin n) :=
(s.subtype _).map fin.equiv_subtype.symm.to_embedding

@[simp] lemma mem_fin {n} {s : finset ℕ} :
  ∀ a : fin n, a ∈ s.fin n ↔ (a : ℕ) ∈ s
| ⟨a, ha⟩ := by simp [finset.fin]

@[mono] lemma fin_mono {n} : monotone (finset.fin n) :=
λ s t h x, by simpa using @h x

@[simp] lemma fin_map {n} {s : finset ℕ} : (s.fin n).map fin.coe_embedding = s.filter (< n) :=
by simp [finset.fin, finset.map_map]

lemma subset_image_iff [decidable_eq β] {s : set α} {t : finset β} {f : α → β}:
  ↑t ⊆ f '' s ↔ ∃ s' : finset α, ↑s' ⊆ s ∧ s'.image f = t :=
begin
  split, swap,
  { rintro ⟨t, ht, rfl⟩, rw [coe_image], exact set.image_subset f ht },
  intro h,
  letI : can_lift β s (f ∘ coe) (λ y, y ∈ f '' s) := ⟨λ y ⟨x, hxt, hy⟩, ⟨⟨x, hxt⟩, hy⟩⟩,
  lift t to finset s using h,
  refine ⟨t.map (embedding.subtype _), map_subtype_subset _, _⟩,
  ext y, simp
end

lemma range_sdiff_zero {n : ℕ} : range (n + 1) \ {0} = (range n).image nat.succ :=
begin
  induction n with k hk,
  { simp },
  nth_rewrite 1 range_succ,
  rw [range_succ, image_insert, ←hk, insert_sdiff_of_not_mem],
  simp
end

end finset

lemma _root_.multiset.to_finset_map [decidable_eq α] [decidable_eq β] (f : α → β) (m : multiset α) :
  (m.map f).to_finset = m.to_finset.image f :=
finset.val_inj.1 (multiset.dedup_map_dedup_eq _ _).symm


namespace equiv

/-- Given an equivalence `α` to `β`, produce an equivalence between `finset α` and `finset β`. -/
protected def finset_congr (e : α ≃ β) : finset α ≃ finset β :=
{ to_fun := λ s, s.map e.to_embedding,
  inv_fun := λ s, s.map e.symm.to_embedding,
  left_inv := λ s, by simp [finset.map_map],
  right_inv := λ s, by simp [finset.map_map] }

@[simp] lemma finset_congr_apply (e : α ≃ β) (s : finset α) :
  e.finset_congr s = s.map e.to_embedding :=
rfl

@[simp] lemma finset_congr_refl : (equiv.refl α).finset_congr = equiv.refl _ := by { ext, simp }
@[simp] lemma finset_congr_symm (e : α ≃ β) : e.finset_congr.symm = e.symm.finset_congr := rfl

@[simp] lemma finset_congr_trans (e : α ≃ β) (e' : β ≃ γ) :
  e.finset_congr.trans (e'.finset_congr) = (e.trans e').finset_congr :=
by { ext, simp [-finset.mem_map, -equiv.trans_to_embedding] }

lemma finset_congr_to_embedding (e : α ≃ β) :
  e.finset_congr.to_embedding = (finset.map_embedding e.to_embedding).to_embedding := rfl

end equiv
