/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.multiset.nodup

/-!
# The cartesian product of multisets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

namespace multiset

section pi
open function

namespace pi
variables {ι : Type*} [decidable_eq ι] {α : ι → Sort*}

/-- Given `β : α → Type*`, `pi.empty β` is the trivial dependent function out of the empty
multiset. -/
def empty {ι : Type*} (α : ι → Sort*) : (Π i ∈ (0 : multiset ι), α i).

variables {i : ι} {m : multiset ι}

/-- Given `α : ι → Sort*`, a multiset `m` and a term `i`, as well as a term `a : α i` and a
function `f` such that `f j : α j` for all `j` in `m`, `pi.cons a f` is a function `g` such
that `g k : α k` for all `k` in `i ::ₘ m`. -/
def cons (a : α i) (f : Π j ∈ m, α j) : Π j ∈ (i ::ₘ m), α j :=
λ j hj, if h : j = i then h.symm.rec a else f j $ (mem_cons.1 hj).resolve_left h

lemma cons_same {a : α i} {f : Π j ∈ m, α j} (h : i ∈ i ::ₘ m) :
  pi.cons a f i h = a :=
dif_pos rfl

lemma cons_ne {a : α i} {f : Π j ∈ m, α j} {j : ι} (hj : j ∈ i ::ₘ m) (h : j ≠ i) :
  pi.cons a f j hj = f j ((mem_cons.1 hj).resolve_left h) :=
dif_neg h

lemma cons_swap {i i' : ι} {a : α i} {a' : α i'} {f : Π j ∈ m, α j} (h : i ≠ i') :
  pi.cons a (pi.cons a' f) == pi.cons a' (pi.cons a f) :=
begin
  apply hfunext rfl,
  rintro j _ rfl,
  refine hfunext (by rw [cons_swap]) (λ ha₁ ha₂ _, _),
  rcases ne_or_eq j i with h₁ | rfl,
  rcases eq_or_ne j i' with rfl | h₂,
  all_goals { simp [*, pi.cons_same, pi.cons_ne] },
end

@[simp] lemma cons_eta (f : Π j ∈ (i ::ₘ m), α j) :
  cons (f i (mem_cons_self _ _)) (λ j hj, f j (mem_cons_of_mem hj)) = f :=
by { ext j hj, dsimp [cons], split_ifs with H, { cases H, refl }, { refl }, }

lemma cons_map (a : α i) (f : Π j ∈ m, α j)
  {α' : ι → Sort*} (φ : ∀ ⦃j⦄, α j → α' j) :
  cons (φ a) (λ j hj, φ (f j hj)) = (λ j hj, φ ((cons a f) j hj)) :=
begin
  ext j hj,
  refine (congr_arg2 _ _ rfl).trans (apply_dite (@φ _) _ _ _).symm,
  ext rfl,
  refl,
end

lemma forall_rel_cons_ext (r : Π ⦃i⦄, α i → α i → Prop) {a₁ a₂ : α i} {f₁ f₂ : Π j ∈ m, α j}
  (ha : r a₁ a₂) (hf : ∀ (i : ι) (hi : i ∈ m), r (f₁ i hi) (f₂ i hi)) :
  ∀ j hj, r (cons a₁ f₁ j hj) (cons a₂ f₂ j hj) :=
by { intros j hj, dsimp [cons], split_ifs with H, { cases H, exact ha }, { exact hf _ _, } }

lemma cons_injective {i : ι} {a : α i} {s : multiset ι} (hs : i ∉ s) :
  function.injective (@pi.cons _ _ _ _ s a) :=
assume f₁ f₂ eq, funext $ assume j, funext $ assume h',
have ne : i ≠ j, from assume h, hs $ h.symm ▸ h',
have j ∈ i ::ₘ s, from mem_cons_of_mem h',
calc f₁ j h' = pi.cons a f₁ j this : by rw [pi.cons_ne this ne.symm]
  ... = pi.cons a f₂ j this : by rw [eq]
  ... = f₂ j h' : by rw [pi.cons_ne this ne.symm]
end pi

section
variables {α : Type*} [decidable_eq α] {β : α → Type*}

/-- `pi m t` constructs the Cartesian product over `t` indexed by `m`. -/
def pi (m : multiset α) (t : Π a, multiset (β a)) : multiset (Π a ∈ m, β a) :=
m.rec_on {pi.empty β} (λ a m (p : multiset (Π a ∈ m, β a)), (t a).bind $ λ b, p.map $ pi.cons b)
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

@[simp] lemma pi_zero (t : Π a, multiset (β a)) : pi 0 t = {pi.empty β} := rfl

@[simp] lemma pi_cons (m : multiset α) (t : Π a, multiset (β a)) (a : α) :
  pi (a ::ₘ m) t = ((t a).bind $ λ b, (pi m t).map $ pi.cons b) :=
rec_on_cons a m

lemma card_pi (m : multiset α) (t : Π a, multiset (β a)) :
  card (pi m t) = prod (m.map $ λ a, card (t a)) :=
multiset.induction_on m (by simp) (by simp [mul_comm] {contextual := tt})

protected lemma nodup.pi {s : multiset α} {t : Π a, multiset (β a)} :
  nodup s → (∀ a ∈ s, nodup (t a)) → nodup (pi s t) :=
multiset.induction_on s (assume _ _, nodup_singleton _)
begin
  assume a s ih hs ht,
  have has : a ∉ s, by simp at hs; exact hs.1,
  have hs : nodup s, by simp at hs; exact hs.2,
  simp,
  refine ⟨λ b hb, (ih hs $ λ a' h', ht a' $ mem_cons_of_mem h').map (pi.cons_injective has), _⟩,
  refine (ht a $ mem_cons_self _ _).pairwise _,
  from assume b₁ hb₁ b₂ hb₂ neb, disjoint_map_map.2 (assume f hf g hg eq,
    have pi.cons b₁ f a (mem_cons_self _ _) = pi.cons b₂ g a (mem_cons_self _ _),
      by rw [eq],
    neb $ show b₁ = b₂, by rwa [pi.cons_same, pi.cons_same] at this)
end

lemma mem_pi {m : multiset α} (t : Π a, multiset (β a)) :
  ∀ f : Π a ∈ m, β a, (f ∈ pi m t) ↔ (∀ a (h : a ∈ m), f a h ∈ t a) :=
begin
  intro f,
  induction m using multiset.induction_on with a m ih,
  { simpa using show f = pi.empty β, by funext a ha; exact ha.elim },
  simp_rw [pi_cons, mem_bind, mem_map, ih],
  split,
  { rintro ⟨b, hb, f', hf', rfl⟩ a' ha',
    by_cases a' = a,
    { subst h, rwa [pi.cons_same] },
    { rw [pi.cons_ne _ h], apply hf' } },
  { intro hf,
    refine ⟨_, hf a (mem_cons_self _ _), _, λ a ha, hf a (mem_cons_of_mem ha), _⟩,
    rw pi.cons_eta }
end

end

end pi

end multiset
