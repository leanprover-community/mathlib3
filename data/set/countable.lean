/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Countable sets.
-/

import data.encodable data.set.finite data.set.lattice data.set.prod logic.function_inverse
noncomputable theory

open function set encodable

open classical (hiding some)
local attribute [instance] decidable_inhabited prop_decidable
universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

namespace set

section encodable

def encodable_of_inj [encodable β] (f : α → β) (hf : injective f) : encodable α :=
let g : β → option α := λb, if h : ∃a, f a = b then some (classical.some h) else none in
encodable_of_left_injection f g $ assume a,
  have h : ∃a', f a' = f a, from ⟨a, rfl⟩,
  have f (classical.some h) = f a, from some_spec h,
  have classical.some h = a, from hf this,
  by simp [g, h, this]

end encodable

/-- Countable sets

A set is countable if there exists a injective functions from the set into the natural numbers.
This is choosen instead of surjective functions, as this would require that α is non empty.
-/
def countable (s : set α) : Prop := ∃f:α → ℕ, ∀x∈s, ∀y∈s, f x = f y → x = y

lemma countable_iff_exists_surjective [ne : inhabited α] {s : set α} :
  countable s ↔ (∃f:ℕ → α, s ⊆ range f) :=
iff.intro
  (assume ⟨f, hf⟩, ⟨inv_fun_on f s, assume a ha, ⟨f a, inv_fun_on_eq' hf ha⟩⟩)
  (assume ⟨f, hf⟩, ⟨inv_fun f, assume x hx y hy h,
    calc x = f (inv_fun f x) : (inv_fun_eq $ hf hx).symm
      ... = f (inv_fun f y) : by rw [h]
      ... = y : inv_fun_eq $ hf hy⟩)

lemma countable.to_encodable {s : set α} (h : countable s) : encodable {a // a ∈ s} :=
let f := classical.some h in
have hf : ∀x∈s, ∀y∈s, f x = f y → x = y, from classical.some_spec h,
let f' : {a // a ∈ s} → ℕ := f ∘ subtype.val in
encodable_of_inj f' $ assume ⟨a, ha⟩ ⟨b, hb⟩ (h : f a = f b), subtype.eq $ hf a ha b hb h

lemma countable_encodable' {s : set α} (e : encodable {a // a∈s}) : countable s :=
⟨λx, if h : x ∈ s then @encode _ e ⟨x, h⟩ else 0, assume x hx y hy h,
  have @encode _ e ⟨x, hx⟩ = @encode _ e ⟨y, hy⟩,
    by simp [hx, hy] at h; assumption,
  have decode {a // a∈s} (@encode _ e ⟨x, hx⟩) = decode {a // a∈s} (@encode _ e ⟨y, hy⟩),
    from congr_arg _ this,
  begin simp [encodek] at this, injection this with h, injection h end⟩

lemma countable_encodable [e : encodable α] {s : set α} : countable s :=
⟨encode, assume x _ y _ eq,
  have decode α (encode x) = decode α (encode y), from congr_arg _ eq,
  by simp [encodek] at this; exact option.some.inj this⟩

lemma countable_empty : countable (∅ : set α) :=
⟨λ_, 0, by simp⟩

lemma countable_singleton {a : α} : countable ({a} : set α) :=
⟨λ_, 0, by simp⟩

lemma countable_subset {s₁ s₂ : set α} (h : s₁ ⊆ s₂) : countable s₂ → countable s₁
| ⟨f, hf⟩ := ⟨f, assume x hx y hy eq, hf x (h hx) y (h hy) eq⟩

lemma countable_image {s : set α} {f : α → β} (hs : countable s) : countable (f '' s) :=
let f' : {a // a ∈ s} → {b // b ∈ f '' s} := λ⟨a, ha⟩, ⟨f a, mem_image_of_mem f ha⟩ in
have hf' : surjective f', from assume ⟨b, a, ha, hab⟩, ⟨⟨a, ha⟩, subtype.eq hab⟩,
countable_encodable' $ @encodable_of_inj _ _ hs.to_encodable (surj_inv hf') (injective_surj_inv hf')

lemma countable_sUnion {s : set (set α)} (hs : countable s) (h : ∀a∈s, countable a) :
  countable (⋃₀ s) :=
by_cases
  (assume : nonempty α, let ⟨a⟩ := this, inh : inhabited α := ⟨a⟩ in
    let ⟨fs, hfs⟩ := countable_iff_exists_surjective.mp hs in
    have ∀t, ∃ft:ℕ → α, t ∈ s → t ⊆ range ft,
      from assume t,
      by_cases
        (assume : t ∈ s,
          let ⟨ft, hft⟩ := (@countable_iff_exists_surjective α inh _).mp $ h t this in
          ⟨ft, assume _, hft⟩)
        (assume : t ∉ s, ⟨λ_, a, assume h, (this h).elim⟩),
    have ∃ft:(∀t:set α, ℕ → α), ∀t∈s, t ⊆ range (ft t),
      by simp [classical.skolem] at this; assumption,
    let ⟨ft, hft⟩ := this in
    (@countable_iff_exists_surjective α inh _).mpr
      ⟨(λp:ℕ×ℕ, ft (fs p.1) p.2) ∘ nat.unpair,
        by simp [subset_def];
        from assume a t ha ht,
        let ⟨i, hi⟩ := hfs ht, ⟨j, hj⟩ := hft t ht ha in
        ⟨nat.mkpair i j, by simp [function.comp, nat.unpair_mkpair, hi, hj]⟩⟩)
  (assume : ¬ nonempty α, ⟨λ_, 0, assume a, (this ⟨a⟩).elim⟩)

end set
