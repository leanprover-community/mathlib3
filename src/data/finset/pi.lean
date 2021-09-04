/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.finset.basic
import data.multiset.pi

/-!
# The cartesian product of finsets
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

variables {δ : α → Type*} [decidable_eq α]

/-- Given a finset `s` of `α` and for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `s.pi t` of all functions defined on elements of `s` taking values in `t a` for `a ∈ s`.
Note that the elements of `s.pi t` are only partially defined, on `s`. -/
def pi (s : finset α) (t : Πa, finset (δ a)) : finset (Πa∈s, δ a) :=
⟨s.1.pi (λ a, (t a).1), nodup_pi s.2 (λ a _, (t a).2)⟩

@[simp] lemma pi_val (s : finset α) (t : Πa, finset (δ a)) :
  (s.pi t).1 = s.1.pi (λ a, (t a).1) := rfl

@[simp] lemma mem_pi {s : finset α} {t : Πa, finset (δ a)} {f : Πa∈s, δ a} :
  f ∈ s.pi t ↔ (∀a (h : a ∈ s), f a h ∈ t a) :=
mem_pi _ _ _

/-- Given a function `f` defined on a finset `s`, define a new function on the finset `s ∪ {a}`,
equal to `f` on `s` and sending `a` to a given value `b`. This function is denoted
`s.pi.cons a b f`. If `a` already belongs to `s`, the new function takes the value `b` at `a`
anyway. -/
def pi.cons (s : finset α) (a : α) (b : δ a) (f : Πa, a ∈ s → δ a) (a' : α) (h : a' ∈ insert a s) :
  δ a' :=
multiset.pi.cons s.1 a b f _ (multiset.mem_cons.2 $ mem_insert.symm.2 h)

@[simp]
lemma pi.cons_same (s : finset α) (a : α) (b : δ a) (f : Πa, a ∈ s → δ a) (h : a ∈ insert a s) :
  pi.cons s a b f a h = b :=
multiset.pi.cons_same _

lemma pi.cons_ne {s : finset α} {a a' : α} {b : δ a} {f : Πa, a ∈ s → δ a} {h : a' ∈ insert a s}
  (ha : a ≠ a') :
  pi.cons s a b f a' h = f a' ((mem_insert.1 h).resolve_left ha.symm) :=
multiset.pi.cons_ne _ _

lemma pi_cons_injective  {a : α} {b : δ a} {s : finset α} (hs : a ∉ s) :
  function.injective (pi.cons s a b) :=
assume e₁ e₂ eq,
@multiset.pi_cons_injective α _ δ a b s.1 hs _ _ $
  funext $ assume e, funext $ assume h,
  have pi.cons s a b e₁ e (by simpa only [multiset.mem_cons, mem_insert] using h) =
    pi.cons s a b e₂ e (by simpa only [multiset.mem_cons, mem_insert] using h),
  { rw [eq] },
  this

@[simp] lemma pi_empty {t : Πa:α, finset (δ a)} :
  pi (∅ : finset α) t = singleton (pi.empty δ) := rfl

@[simp] lemma pi_insert [∀a, decidable_eq (δ a)]
  {s : finset α} {t : Πa:α, finset (δ a)} {a : α} (ha : a ∉ s) :
  pi (insert a s) t = (t a).bUnion (λb, (pi s t).image (pi.cons s a b)) :=
begin
  apply eq_of_veq,
  rw ← multiset.erase_dup_eq_self.2 (pi (insert a s) t).2,
  refine (λ s' (h : s' = a ::ₘ s.1), (_ : erase_dup (multiset.pi s' (λ a, (t a).1)) =
    erase_dup ((t a).1.bind $ λ b,
    erase_dup $ (multiset.pi s.1 (λ (a : α), (t a).val)).map $
      λ f a' h', multiset.pi.cons s.1 a b f a' (h ▸ h')))) _ (insert_val_of_not_mem ha),
  subst s', rw pi_cons,
  congr, funext b,
  rw multiset.erase_dup_eq_self.2,
  exact multiset.nodup_map (multiset.pi_cons_injective ha) (pi s t).2,
end

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

lemma pi_subset {s : finset α} (t₁ t₂ : Πa, finset (δ a)) (h : ∀ a ∈ s, t₁ a ⊆ t₂ a) :
  s.pi t₁ ⊆ s.pi t₂ :=
λ g hg, mem_pi.2 $ λ a ha, h a ha (mem_pi.mp hg a ha)


lemma pi_disjoint_of_disjoint {δ : α → Type*} [∀a, decidable_eq (δ a)]
  {s : finset α} [decidable_eq (Πa∈s, δ a)]
  (t₁ t₂ : Πa, finset (δ a)) {a : α} (ha : a ∈ s) (h : disjoint (t₁ a) (t₂ a)) :
  disjoint (s.pi t₁) (s.pi t₂) :=
disjoint_iff_ne.2 $ λ f₁ hf₁ f₂ hf₂ eq₁₂,
  disjoint_iff_ne.1 h (f₁ a ha) (mem_pi.mp hf₁ a ha) (f₂ a ha) (mem_pi.mp hf₂ a ha)
  $ congr_fun (congr_fun eq₁₂ a) ha

end pi
end finset
