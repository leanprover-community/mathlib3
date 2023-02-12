/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.finset.image
import data.multiset.pi

/-!
# The cartesian product of finsets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

namespace finset
open multiset

/-! ### pi -/
section pi
variables {α : Type*}

/-- The empty dependent product function, defined on the empty set. The assumption `a ∈ ∅` is never
satisfied. -/
def pi.empty (β : α → Sort*) (a : α) (h : a ∈ (∅ : finset α)) : β a :=
multiset.pi.empty β a h

variables {β : α → Type*} {δ : α → Sort*} [decidable_eq α]

/-- Given a finset `s` of `α` and for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `s.pi t` of all functions defined on elements of `s` taking values in `t a` for `a ∈ s`.
Note that the elements of `s.pi t` are only partially defined, on `s`. -/
def pi (s : finset α) (t : Πa, finset (β a)) : finset (Πa∈s, β a) :=
⟨s.1.pi (λ a, (t a).1), s.nodup.pi $ λ a _, (t a).nodup⟩

@[simp] lemma pi_val (s : finset α) (t : Πa, finset (β a)) :
  (s.pi t).1 = s.1.pi (λ a, (t a).1) := rfl

@[simp] lemma mem_pi {s : finset α} {t : Πa, finset (β a)} {f : Πa∈s, β a} :
  f ∈ s.pi t ↔ (∀a (h : a ∈ s), f a h ∈ t a) :=
mem_pi _ _ _

/-- Given a function `f` defined on a finset `s`, define a new function on the finset `s ∪ {a}`,
equal to `f` on `s` and sending `a` to a given value `b`. This function is denoted
`s.pi.cons a b f`. -/
def pi.cons (s : finset α) (a : α) (ha : a ∉ s) (b : δ a) (f : Πa, a ∈ s → δ a) (a' : α)
  (h : a' ∈ cons a s ha) :
  δ a' :=
multiset.pi.cons s.1 a b f _ h

@[simp]
lemma pi.cons_same (s : finset α) (a : α) (ha : a ∉ s) (b : δ a) (f : Πa, a ∈ s → δ a) (h : a ∈ cons a s ha) :
  pi.cons s a ha b f a h = b :=
multiset.pi.cons_same _

lemma pi.cons_ne {s : finset α} {a a' : α} (ha' : a ∉ s) {b : δ a} {f : Πa, a ∈ s → δ a} {h : a' ∈ cons a s ha'}
  (ha : a ≠ a') :
  pi.cons s a ha' b f a' h = f a' ((mem_cons.1 h).resolve_left ha.symm) :=
multiset.pi.cons_ne _ _

lemma pi_cons_injective  {a : α} {b : δ a} {s : finset α} (hs : a ∉ s) :
  function.injective (pi.cons s a hs b) :=
multiset.pi_cons_injective hs

@[simp] lemma pi_empty {t : Πa:α, finset (β a)} :
  pi (∅ : finset α) t = singleton (pi.empty β) := rfl

@[simp] lemma pi_cons [∀a, decidable_eq (β a)]
  {s : finset α} {t : Πa:α, finset (β a)} {a : α} (ha : a ∉ s) :
  pi (cons a s ha) t = (t a).disj_Union (λb,
    (pi s t).map ⟨pi.cons s a ha b, pi_cons_injective _⟩)
    (λ i hi j hj hij, begin
      simp only [function.on_fun, disjoint_iff_ne, mem_map, function.embedding.coe_fn_mk],
      rintros _ ⟨p₂, hp, eq₂⟩ _ ⟨p₃, hp₃, eq₃⟩ eq,
      have : pi.cons s a ha i p₂ a (mem_cons_self _ _) = pi.cons s a ha j p₃ a (mem_cons_self _ _),
      { rw [eq₂, eq₃, eq] },
      rw [pi.cons_same, pi.cons_same] at this,
      exact hij this
    end) :=
eq_of_veq (pi_cons s.val (λ i, (t i).val) a)

lemma pi_singletons {β : Type*} (s : finset α) (f : α → β) :
  s.pi (λ a, ({f a} : finset β)) = {λ a _, f a} :=
begin
  rw eq_singleton_iff_unique_mem,
  split,
  { simp },
  intros a ha,
  ext i hi,
  rw [mem_pi] at ha,
  simpa using ha i hi,
end

lemma pi_const_singleton {β : Type*} (s : finset α) (i : β) :
  s.pi (λ _, ({i} : finset β)) = {λ _ _, i} :=
pi_singletons s (λ _, i)

lemma pi_subset {s : finset α} (t₁ t₂ : Πa, finset (β a)) (h : ∀ a ∈ s, t₁ a ⊆ t₂ a) :
  s.pi t₁ ⊆ s.pi t₂ :=
λ g hg, mem_pi.2 $ λ a ha, h a ha (mem_pi.mp hg a ha)


lemma pi_disjoint_of_disjoint {δ : α → Type*}
  {s : finset α} (t₁ t₂ : Πa, finset (δ a)) {a : α} (ha : a ∈ s) (h : disjoint (t₁ a) (t₂ a)) :
  disjoint (s.pi t₁) (s.pi t₂) :=
disjoint_iff_ne.2 $ λ f₁ hf₁ f₂ hf₂ eq₁₂,
  disjoint_iff_ne.1 h (f₁ a ha) (mem_pi.mp hf₁ a ha) (f₂ a ha) (mem_pi.mp hf₂ a ha)
  $ congr_fun (congr_fun eq₁₂ a) ha

end pi
end finset
