/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.multiset.nodup

/-!
# The cartesian product of multisets
-/

namespace multiset

section pi
variables {α : Type*}
open function

/-- Given `δ : α → Type*`, `pi.empty δ` is the trivial dependent function out of the empty
multiset. -/
def pi.empty (δ : α → Type*) : (Πa∈(0:multiset α), δ a) .

variables [decidable_eq α] {δ : α → Type*}

/-- Given `δ : α → Type*`, a multiset `m` and a term `a`, as well as a term `b : δ a` and a
function `f` such that `f a' : δ a'` for all `a'` in `m`, `pi.cons m a b f` is a function `g` such
that `g a'' : δ a''` for all `a''` in `a ::ₘ m`. -/
def pi.cons (m : multiset α) (a : α) (b : δ a) (f : Πa∈m, δ a) : Πa'∈a ::ₘ m, δ a' :=
λa' ha', if h : a' = a then eq.rec b h.symm else f a' $ (mem_cons.1 ha').resolve_left h

lemma pi.cons_same {m : multiset α} {a : α} {b : δ a} {f : Πa∈m, δ a} (h : a ∈ a ::ₘ m) :
  pi.cons m a b f a h = b :=
dif_pos rfl

lemma pi.cons_ne {m : multiset α} {a a' : α} {b : δ a} {f : Πa∈m, δ a}
  (h' : a' ∈ a ::ₘ m) (h : a' ≠ a) :
  pi.cons m a b f a' h' = f a' ((mem_cons.1 h').resolve_left h) :=
dif_neg h

lemma pi.cons_swap {a a' : α} {b : δ a} {b' : δ a'} {m : multiset α} {f : Πa∈m, δ a} (h : a ≠ a') :
  pi.cons (a' ::ₘ m) a b (pi.cons m a' b' f) == pi.cons (a ::ₘ m) a' b' (pi.cons m a b f) :=
begin
  apply hfunext, { refl }, intros a'' _ h, subst h,
  apply hfunext, { rw [cons_swap] }, intros ha₁ ha₂ h,
  by_cases h₁ : a'' = a; by_cases h₂ : a'' = a';
    simp [*, pi.cons_same, pi.cons_ne] at *,
  { subst h₁, rw [pi.cons_same, pi.cons_same] },
  { subst h₂, rw [pi.cons_same, pi.cons_same] }
end

/-- `pi m t` constructs the Cartesian product over `t` indexed by `m`. -/
def pi (m : multiset α) (t : Πa, multiset (δ a)) : multiset (Πa∈m, δ a) :=
m.rec_on {pi.empty δ} (λa m (p : multiset (Πa∈m, δ a)), (t a).bind $ λb, p.map $ pi.cons m a b)
begin
  intros a a' m n,
  by_cases eq : a = a',
  { subst eq },
  { simp [map_bind, bind_bind (t a') (t a)],
    apply bind_hcongr, { rw [cons_swap a a'] },
    intros b hb,
    apply bind_hcongr, { rw [cons_swap a a'] },
    intros b' hb',
    apply map_hcongr, { rw [cons_swap a a'] },
    intros f hf,
    exact pi.cons_swap eq }
end

@[simp] lemma pi_zero (t : Πa, multiset (δ a)) : pi 0 t = {pi.empty δ} := rfl

@[simp] lemma pi_cons (m : multiset α) (t : Πa, multiset (δ a)) (a : α) :
  pi (a ::ₘ m) t = ((t a).bind $ λb, (pi m t).map $ pi.cons m a b) :=
rec_on_cons a m

lemma pi_cons_injective {a : α} {b : δ a} {s : multiset α} (hs : a ∉ s) :
  function.injective (pi.cons s a b) :=
assume f₁ f₂ eq, funext $ assume a', funext $ assume h',
have ne : a ≠ a', from assume h, hs $ h.symm ▸ h',
have a' ∈ a ::ₘ s, from mem_cons_of_mem h',
calc f₁ a' h' = pi.cons s a b f₁ a' this : by rw [pi.cons_ne this ne.symm]
  ... = pi.cons s a b f₂ a' this : by rw [eq]
  ... = f₂ a' h' : by rw [pi.cons_ne this ne.symm]

lemma card_pi (m : multiset α) (t : Πa, multiset (δ a)) :
  card (pi m t) = prod (m.map $ λa, card (t a)) :=
multiset.induction_on m (by simp) (by simp [mul_comm] {contextual := tt})

lemma nodup_pi {s : multiset α} {t : Πa, multiset (δ a)} :
  nodup s → (∀a∈s, nodup (t a)) → nodup (pi s t) :=
multiset.induction_on s (assume _ _, nodup_singleton _)
begin
  assume a s ih hs ht,
  have has : a ∉ s, by simp at hs; exact hs.1,
  have hs : nodup s, by simp at hs; exact hs.2,
  simp,
  split,
  { assume b hb,
    from nodup_map (pi_cons_injective has) (ih hs $ assume a' h', ht a' $ mem_cons_of_mem h') },
  { apply pairwise_of_nodup _ (ht a $ mem_cons_self _ _),
    from assume b₁ hb₁ b₂ hb₂ neb, disjoint_map_map.2 (assume f hf g hg eq,
      have pi.cons s a b₁ f a (mem_cons_self _ _) = pi.cons s a b₂ g a (mem_cons_self _ _),
        by rw [eq],
      neb $ show b₁ = b₂, by rwa [pi.cons_same, pi.cons_same] at this) }
end

lemma mem_pi (m : multiset α) (t : Πa, multiset (δ a)) :
  ∀f:Πa∈m, δ a, (f ∈ pi m t) ↔ (∀a (h : a ∈ m), f a h ∈ t a) :=
begin
  refine multiset.induction_on m (λ f, _) (λ a m ih f, _),
  { simpa using show f = pi.empty δ, by funext a ha; exact ha.elim },
  simp only [mem_bind, exists_prop, mem_cons, pi_cons, mem_map], split,
  { rintro ⟨b, hb, f', hf', rfl⟩ a' ha',
    rw [ih] at hf',
    by_cases a' = a,
    { subst h, rwa [pi.cons_same] },
    { rw [pi.cons_ne _ h], apply hf' } },
  { intro hf,
    refine ⟨_, hf a (mem_cons_self a _), λa ha, f a (mem_cons_of_mem ha),
      (ih _).2 (λ a' h', hf _ _), _⟩,
    funext a' h',
    by_cases a' = a,
    { subst h, rw [pi.cons_same] },
    { rw [pi.cons_ne _ h] } }
end

end pi

end multiset
