/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Countable sets.
-/

import data.equiv.list data.set.finite logic.function data.set.function
noncomputable theory

open function set encodable

open classical (hiding some)
local attribute [instance] prop_decidable
universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

namespace set

/-- Countable sets

A set is countable if there exists an encoding of the set into the natural numbers.
An encoding is an injection with a partial inverse, which can be viewed as a
constructive analogue of countability. (For the most part, theorems about
`countable` will be classical and `encodable` will be constructive.)
-/
def countable (s : set α) : Prop := nonempty (encodable s)

lemma countable_iff_exists_injective {s : set α} :
  countable s ↔ ∃f:s → ℕ, injective f :=
⟨λ ⟨h⟩, by exactI ⟨encode, encode_injective⟩,
 λ ⟨f, h⟩, ⟨⟨f, partial_inv f, partial_inv_left h⟩⟩⟩

lemma countable_iff_exists_inj_on {s : set α} :
  countable s ↔ ∃ f : α → ℕ, inj_on f s :=
countable_iff_exists_injective.trans
⟨λ ⟨f, hf⟩, ⟨λ a, if h : a ∈ s then f ⟨a, h⟩ else 0,
   λ a b as bs h, congr_arg subtype.val $
     hf $ by simpa [as, bs] using h⟩,
 λ ⟨f, hf⟩, ⟨_, inj_on_iff_injective.1 hf⟩⟩

lemma countable_iff_exists_surjective [ne : inhabited α] {s : set α} :
  countable s ↔ ∃f:ℕ → α, s ⊆ range f :=
⟨λ ⟨h⟩, by exactI ⟨λ n, ((decode s n).map subtype.val).iget,
  λ a as, ⟨encode (⟨a, as⟩ : s), by simp [encodek]⟩⟩,
 λ ⟨f, hf⟩, ⟨⟨
  λ x, inv_fun f x.1,
  λ n, if h : f n ∈ s then some ⟨f n, h⟩ else none,
  λ ⟨x, hx⟩, begin
    have := inv_fun_eq (hf hx), dsimp at this ⊢,
    simp [this, hx]
  end⟩⟩⟩

def countable.to_encodable {s : set α} : countable s → encodable s :=
classical.choice

lemma countable_encodable' (s : set α) [H : encodable s] : countable s :=
⟨H⟩

lemma countable_encodable [encodable α] (s : set α) : countable s :=
⟨by apply_instance⟩

lemma exists_surjective_of_countable {s : set α} (hs : s ≠ ∅) (hc : countable s) :
  ∃f:ℕ → α, s = range f :=
begin
  rcases ne_empty_iff_exists_mem.1 hs with ⟨x, hx⟩,
  letI : encodable s := countable.to_encodable hc,
  letI : inhabited s := ⟨⟨x, hx⟩⟩,
  have : countable (univ : set s) := countable_encodable _,
  rcases countable_iff_exists_surjective.1 this with ⟨g, hg⟩,
  have : range g = univ := univ_subset_iff.1 hg,
  use subtype.val ∘ g,
  rw [range_comp, this],
  simp
end

@[simp] lemma countable_empty : countable (∅ : set α) :=
⟨⟨λ x, x.2.elim, λ n, none, λ x, x.2.elim⟩⟩

@[simp] lemma countable_singleton (a : α) : countable ({a} : set α) :=
⟨of_equiv _ (equiv.set.singleton a)⟩

lemma countable_subset {s₁ s₂ : set α} (h : s₁ ⊆ s₂) : countable s₂ → countable s₁
| ⟨H⟩ := ⟨@of_inj _ _ H _ (embedding_of_subset h).2⟩

lemma countable_image {s : set α} (f : α → β) (hs : countable s) : countable (f '' s) :=
let f' : s → f '' s := λ⟨a, ha⟩, ⟨f a, mem_image_of_mem f ha⟩ in
have hf' : surjective f', from assume ⟨b, a, ha, hab⟩, ⟨⟨a, ha⟩, subtype.eq hab⟩,
⟨@encodable.of_inj _ _ hs.to_encodable (surj_inv hf') (injective_surj_inv hf')⟩

lemma countable_range [encodable α] (f : α → β) : countable (range f) :=
by rw ← image_univ; exact countable_image _ (countable_encodable _)

lemma countable_of_injective_of_countable_image {s : set α} {f : α → β}
  (hf : inj_on f s) (hs : countable (f '' s)) : countable s :=
let ⟨g, hg⟩ := countable_iff_exists_inj_on.1 hs in
countable_iff_exists_inj_on.2 ⟨g ∘ f, inj_on_comp (maps_to_image _ _) hg hf⟩

lemma countable_Union {t : α → set β} [encodable α] (ht : ∀a, countable (t a)) :
  countable (⋃a, t a) :=
by haveI := (λ a, (ht a).to_encodable);
   rw Union_eq_range_sigma; apply countable_range

lemma countable_bUnion {s : set α} {t : α → set β} (hs : countable s) (ht : ∀a∈s, countable (t a)) :
  countable (⋃a∈s, t a) :=
begin
  rw bUnion_eq_Union,
  haveI := hs.to_encodable,
  exact countable_Union (by simpa using ht)
end

lemma countable_sUnion {s : set (set α)} (hs : countable s) (h : ∀a∈s, countable a) :
  countable (⋃₀ s) :=
by rw sUnion_eq_bUnion; exact countable_bUnion hs h

lemma countable_Union_Prop {p : Prop} {t : p → set β} (ht : ∀h:p, countable (t h)) :
  countable (⋃h:p, t h) :=
by by_cases p; simp [h, ht]

lemma countable_union {s₁ s₂ : set α} (h₁ : countable s₁) (h₂ : countable s₂) : countable (s₁ ∪ s₂) :=
by rw union_eq_Union; exact
countable_Union (bool.forall_bool.2 ⟨h₂, h₁⟩)

lemma countable_insert {s : set α} {a : α} (h : countable s) : countable (insert a s) :=
by rw [set.insert_eq]; from countable_union (countable_singleton _) h

lemma countable_finite {s : set α} : finite s → countable s
| ⟨h⟩ := nonempty_of_trunc (by exactI trunc_encodable_of_fintype s)

lemma countable_set_of_finite_subset {s : set α} : countable s →
  countable {t | finite t ∧ t ⊆ s} | ⟨h⟩ :=
begin
  resetI,
  refine countable_subset _ (countable_range
    (λ t : finset s, {a | ∃ h:a ∈ s, subtype.mk a h ∈ t})),
  rintro t ⟨⟨ht⟩, ts⟩,
  refine ⟨finset.univ.map (embedding_of_subset ts),
    set.ext $ λ a, _⟩,
  simp, split,
  { rintro ⟨as, b, bt, e⟩,
    cases congr_arg subtype.val e, exact bt },
  { exact λ h, ⟨ts h, _, h, rfl⟩ }
end

lemma countable_pi {π : α → Type*} [fintype α] {s : Πa, set (π a)} (hs : ∀a, countable (s a)) :
  countable {f : Πa, π a | ∀a, f a ∈ s a} :=
countable_subset
  (show {f : Πa, π a | ∀a, f a ∈ s a} ⊆ range (λf : Πa, s a, λa, (f a).1), from
    assume f hf, ⟨λa, ⟨f a, hf a⟩, funext $ assume a, rfl⟩) $
have trunc (encodable (Π (a : α), s a)), from
  @encodable.fintype_pi α _ _ _ (assume a, (hs a).to_encodable),
trunc.induction_on this $ assume h,
@countable_range _ _ h _

lemma countable_prod {s : set α} {t : set β} (hs : countable s) (ht : countable t) :
  countable (set.prod s t) :=
begin
  haveI : encodable s := hs.to_encodable,
  haveI : encodable t := ht.to_encodable,
  haveI : encodable (s × t) := by apply_instance,
  have : range (λp, ⟨p.1, p.2⟩ : s × t → α × β) = set.prod s t,
  { ext z,
    rcases z with ⟨x, y⟩,
    simp only [exists_prop, set.mem_range, set_coe.exists, prod.mk.inj_iff,
               set.prod_mk_mem_set_prod_eq, subtype.coe_mk, prod.exists],
    split,
    { rintros ⟨x', x's, y', y't, x'x, y'y⟩,
      simp [x'x.symm, y'y.symm, x's, y't] },
    { rintros ⟨xs, yt⟩,
      exact ⟨x, xs, y, yt, rfl, rfl⟩ }},
  rw ← this,
  exact countable_range _
end

section enumerate

/-- Enumerate elements in a countable set.-/
def enumerate_countable {s : set α} (h : countable s) (default : α) : ℕ → α :=
assume n, match @encodable.decode s (h.to_encodable) n with
        | (some y) := y
        | (none)   := default
        end

lemma subset_range_enumerate {s : set α} (h : countable s) (default : α) :
   s ⊆ range (enumerate_countable h default) :=
assume x hx,
⟨@encodable.encode s h.to_encodable ⟨x, hx⟩,
by simp [enumerate_countable, encodable.encodek]⟩

end enumerate

end set
