/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.fintype.card
import group_theory.perm.basic

/-!
# fintype instances for `equiv` and `perm`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Main declarations:
* `perms_of_finset s`: The finset of permutations of the finset `s`.

-/

open function
open_locale nat

universes u v

variables {α β γ : Type*}

open finset function list equiv equiv.perm

variables [decidable_eq α] [decidable_eq β]

/-- Given a list, produce a list of all permutations of its elements. -/
def perms_of_list : list α → list (perm α)
| []       := [1]
| (a :: l) := perms_of_list l ++ l.bind (λ b, (perms_of_list l).map (λ f, swap a b * f))

lemma length_perms_of_list : ∀ l : list α, length (perms_of_list l) = l.length!
| []       := rfl
| (a :: l) :=
begin
  rw [length_cons, nat.factorial_succ],
  simp [perms_of_list, length_bind, length_perms_of_list, function.comp, nat.succ_mul],
  cc
end

lemma mem_perms_of_list_of_mem {l : list α} {f : perm α} (h : ∀ x, f x ≠ x → x ∈ l) :
  f ∈ perms_of_list l :=
begin
  induction l with a l IH generalizing f h,
  { exact list.mem_singleton.2 (equiv.ext $ λ x, decidable.by_contradiction $ h _) },
  by_cases hfa : f a = a,
  { refine mem_append_left _ (IH (λ x hx, mem_of_ne_of_mem _ (h x hx))),
    rintro rfl, exact hx hfa },
  have hfa' : f (f a) ≠ f a := mt (λ h, f.injective h) hfa,
  have : ∀ (x : α), (swap a (f a) * f) x ≠ x → x ∈ l,
  { intros x hx,
    have hxa : x ≠ a,
    { rintro rfl, apply hx, simp only [mul_apply, swap_apply_right] },
    refine list.mem_of_ne_of_mem hxa (h x (λ h, _)),
    simp only [h, mul_apply, swap_apply_def, mul_apply, ne.def, apply_eq_iff_eq] at hx;
    split_ifs at hx, exacts [hxa (h.symm.trans h_1), hx h] },
  suffices : f ∈ perms_of_list l ∨ ∃ (b ∈ l) (g ∈ perms_of_list l), swap a b * g = f,
  { simpa only [perms_of_list, exists_prop, list.mem_map, mem_append, list.mem_bind] },
  refine or_iff_not_imp_left.2 (λ hfl, ⟨f a, _, swap a (f a) * f, IH this, _⟩),
  { exact mem_of_ne_of_mem hfa (h _ hfa') },
  { rw [←mul_assoc, mul_def (swap a (f a)) (swap a (f a)),
        swap_swap, ←perm.one_def, one_mul] }
end

lemma mem_of_mem_perms_of_list :
  ∀ {l : list α} {f : perm α}, f ∈ perms_of_list l → ∀ {x}, f x ≠ x → x ∈ l
| []       f h := have f = 1 := by simpa [perms_of_list] using h, by rw this; simp
| (a :: l) f h :=
(mem_append.1 h).elim
  (λ h x hx, mem_cons_of_mem _ (mem_of_mem_perms_of_list h hx))
  (λ h x hx,
    let ⟨y, hy, hy'⟩ := list.mem_bind.1 h in
    let ⟨g, hg₁, hg₂⟩ := list.mem_map.1 hy' in
    if hxa : x = a then by simp [hxa]
    else if hxy : x = y then mem_cons_of_mem _ $ by rwa hxy
    else mem_cons_of_mem _ $
    mem_of_mem_perms_of_list hg₁ $
      by rw [eq_inv_mul_iff_mul_eq.2 hg₂, mul_apply, swap_inv, swap_apply_def];
        split_ifs; [exact ne.symm hxy, exact ne.symm hxa, exact hx])

lemma mem_perms_of_list_iff {l : list α} {f : perm α} :
  f ∈ perms_of_list l ↔ ∀ {x}, f x ≠ x → x ∈ l :=
⟨mem_of_mem_perms_of_list, mem_perms_of_list_of_mem⟩

lemma nodup_perms_of_list : ∀ {l : list α} (hl : l.nodup), (perms_of_list l).nodup
| []       hl := by simp [perms_of_list]
| (a :: l) hl :=
have hl' : l.nodup, from hl.of_cons,
have hln' : (perms_of_list l).nodup, from nodup_perms_of_list hl',
have hmeml : ∀ {f : perm α}, f ∈ perms_of_list l → f a = a,
  from λ f hf, not_not.1 (mt (mem_of_mem_perms_of_list hf) (nodup_cons.1 hl).1),
by rw [perms_of_list, list.nodup_append, list.nodup_bind, pairwise_iff_nth_le]; exact
⟨hln', ⟨λ _ _, hln'.map $ λ _ _, mul_left_cancel,
  λ i j hj hij x hx₁ hx₂,
    let ⟨f, hf⟩ := list.mem_map.1 hx₁ in
    let ⟨g, hg⟩ := list.mem_map.1 hx₂ in
    have hix : x a = nth_le l i (lt_trans hij hj),
      by rw [←hf.2, mul_apply, hmeml hf.1, swap_apply_left],
    have hiy : x a = nth_le l j hj,
      by rw [← hg.2, mul_apply, hmeml hg.1, swap_apply_left],
    absurd (hf.2.trans (hg.2.symm)) $
      λ h, ne_of_lt hij $ nodup_iff_nth_le_inj.1 hl' i j (lt_trans hij hj) hj $
        by rw [← hix, hiy]⟩,
  λ f hf₁ hf₂,
    let ⟨x, hx, hx'⟩ := list.mem_bind.1 hf₂ in
    let ⟨g, hg⟩ := list.mem_map.1 hx' in
    have hgxa : g⁻¹ x = a, from f.injective $
      by rw [hmeml hf₁, ← hg.2]; simp,
    have hxa : x ≠ a, from λ h, (list.nodup_cons.1 hl).1 (h ▸ hx),
    (list.nodup_cons.1 hl).1 $
      hgxa ▸ mem_of_mem_perms_of_list hg.1 (by rwa [apply_inv_self, hgxa])⟩

/-- Given a finset, produce the finset of all permutations of its elements. -/
def perms_of_finset (s : finset α) : finset (perm α) :=
quotient.hrec_on s.1 (λ l hl, ⟨perms_of_list l, nodup_perms_of_list hl⟩)
  (λ a b hab, hfunext (congr_arg _ (quotient.sound hab))
    (λ ha hb _, heq_of_eq $ finset.ext $
      by simp [mem_perms_of_list_iff, hab.mem_iff]))
  s.2

lemma mem_perms_of_finset_iff : ∀ {s : finset α} {f : perm α},
  f ∈ perms_of_finset s ↔ ∀ {x}, f x ≠ x → x ∈ s :=
by rintros ⟨⟨l⟩, hs⟩ f; exact mem_perms_of_list_iff

lemma card_perms_of_finset : ∀ (s : finset α),
  (perms_of_finset s).card = s.card! :=
by rintros ⟨⟨l⟩, hs⟩; exact length_perms_of_list l

/-- The collection of permutations of a fintype is a fintype. -/
def fintype_perm [fintype α] : fintype (perm α) :=
⟨perms_of_finset (@finset.univ α _), by simp [mem_perms_of_finset_iff]⟩

instance [fintype α] [fintype β] : fintype (α ≃ β) :=
if h : fintype.card β = fintype.card α
then trunc.rec_on_subsingleton (fintype.trunc_equiv_fin α)
  (λ eα, trunc.rec_on_subsingleton (fintype.trunc_equiv_fin β)
    (λ eβ, @fintype.of_equiv _ (perm α) fintype_perm
      (equiv_congr (equiv.refl α) (eα.trans (eq.rec_on h eβ.symm)) : (α ≃ α) ≃ (α ≃ β))))
else ⟨∅, λ x, false.elim (h (fintype.card_eq.2 ⟨x.symm⟩))⟩

lemma fintype.card_perm [fintype α] : fintype.card (perm α) = (fintype.card α)! :=
subsingleton.elim (@fintype_perm α _ _) (@equiv.fintype α α _ _ _ _) ▸
card_perms_of_finset _

lemma fintype.card_equiv [fintype α] [fintype β] (e : α ≃ β) :
  fintype.card (α ≃ β) = (fintype.card α)! :=
fintype.card_congr (equiv_congr (equiv.refl α) e) ▸ fintype.card_perm
