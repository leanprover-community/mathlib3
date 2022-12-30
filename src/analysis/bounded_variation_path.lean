/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.measure.lebesgue
import analysis.calculus.monotone
import data.set.function
import topology.instances.ennreal
import .for_mathlib

/-!
# Functions of bounded variation

We study functions of bounded variation. In particular, we show that a bounded variation function
is a difference of monotone functions, and differentiable almost everywhere. This implies that
Lipschitz functions from the real line into finite-dimensional vector space are also differentiable
almost everywhere.

## Main definitions and results

* `evariation_on f s` is the total variation of the function `f` on the set `s`, in `ℝ≥0∞`.
* `has_bounded_variation_on f s` registers that the variation of `f` on `s` is finite.
* `has_locally_bounded_variation f s` registers that `f` has finite variation on any compact
  subinterval of `s`.

* `evariation_on.Icc_add_Icc` states that the variation of `f` on `[a, c]` is the sum of its
  variations on `[a, b]` and `[b, c]`.
* `has_locally_bounded_variation_on.exists_monotone_on_sub_monotone_on` proves that a function
  with locally bounded variation is the difference of two monotone functions.
* `lipschitz_with.has_locally_bounded_variation_on` shows that a Lipschitz function has locally
  bounded variation.
* `has_locally_bounded_variation_on.ae_differentiable_within_at` shows that a bounded variation
  function into a finite dimensional real vector space is differentiable almost everywhere.
* `lipschitz_on_with.ae_differentiable_within_at` is the same result for Lipschitz functions.

We also give several variations around these results.

## Implementation

We define the variation as an extended nonnegative real, to allow for infinite variation. This makes
it possible to use the complete linear order structure of `ℝ≥0∞`. The proofs would be much
more tedious with an `ℝ`-valued or `ℝ≥0`-valued variation, since one would always need to check
that the sets one uses are nonempty and bounded above as these are only conditionally complete.
-/

variables {α β : Type*} {E F : Type*} [pseudo_emetric_space E] [pseudo_emetric_space F]
variables (f : α → E)

section length_on
namespace function

/-- The length of `f` on `l` is the sum of successive distances (zero for empty and singleton). -/
noncomputable def length_on : list α → ennreal :=
list.rec 0
  (λ (a : α) (l : list α) (ih : ennreal),
      list.rec 0 (λ (b : α) (l : list α) (ih' : ennreal), edist (f a) (f b) + ih) l)

lemma length_on_nil : f.length_on list.nil = 0 := rfl
lemma length_on_singleton (a : α) : f.length_on [a] = 0 := rfl
lemma length_on_cons_cons (a b : α) (l : list α) :
  f.length_on (a::b::l) = edist (f a) (f b) + f.length_on (b::l) := rfl

lemma length_on_pair (a b : α) : f.length_on [a, b] = edist (f a) (f b) :=
by simp only [length_on_cons_cons, length_on_singleton, add_zero]

lemma length_on_eq_zip_sum :
  ∀ (l : list α), f.length_on l = (list.zip_with (λ x y, edist (f x) (f y)) l l.tail).sum
| [] := by simp [length_on_nil]
| [a] := by simp [length_on_singleton]
| (a::b::l) := by simp [length_on_cons_cons, length_on_eq_zip_sum (b::l)]

lemma length_on_append_cons_cons :
   ∀ (l : list α) (a b : α), f.length_on (l ++ [a, b]) = f.length_on (l ++ [a]) + edist (f a) (f b)
| [] a b := by
  { simp only [length_on, list.nil_append, add_zero, zero_add], }
| [x] a b := by
  { simp only [length_on, list.singleton_append, add_zero], }
| (x :: y :: l) a b := by
  { simp only [length_on_cons_cons, list.cons_append, add_assoc],
    congr,
    simp only [←list.cons_append],
    apply length_on_append_cons_cons, }

lemma length_on_le_length_on_cons (c : α) : ∀ (l : list α), f.length_on l ≤ (f.length_on $ c :: l)
| [] := by { rw [length_on, le_zero_iff], }
| (a::l) := self_le_add_left _ _

lemma length_on_drop_second_cons_le :
  ∀ (a b : α) (l : list α), f.length_on (a :: l) ≤ f.length_on (a :: b :: l)
| _ _ []  := by
  { apply length_on_le_length_on_cons, }
| a b (c::l) := by
  { simp only [length_on, ←add_assoc],
    apply add_le_add_right (edist_triangle _ _ _) (f.length_on (c :: l)), }

lemma length_on_append : ∀ l l', f.length_on l + f.length_on l' ≤ f.length_on (l ++ l')
| [] l' := by
  { rw [list.nil_append, length_on, zero_add], exact le_refl (f.length_on l'), }
| [a] l' := by
  { rw [list.singleton_append, length_on, zero_add],
    apply length_on_le_length_on_cons, }
| (a :: b :: l) l' := by
  { rw [list.cons_append, length_on, add_assoc],
    refine add_le_add_left (length_on_append (b::l) l') _, }

lemma length_on_reverse : ∀ (l : list α), f.length_on l.reverse = f.length_on l
| [] := rfl
| [a] := rfl
| (a :: b :: l) := by
  { simp only [length_on_append_cons_cons, ←length_on_reverse (b :: l), list.reverse_cons,
               list.append_assoc, list.singleton_append, length_on_cons_cons],
    rw [add_comm, edist_comm], }

lemma length_on_map {γ : Type*} (φ : γ → α) :
  ∀ (l : list γ), f.length_on (l.map φ) = (f ∘ φ).length_on l
| [] := by { simp only [length_on_nil, list.map_nil], }
| [a] := by { simp only [length_on_singleton, list.map], }
| (a :: b :: l)  := by
  { simp only [length_on_cons_cons, list.map, comp_app, ←length_on_map (b::l)], }

lemma length_on_le_append_singleton_append :
  ∀ (l : list α) (x : α) (l' : list α), f.length_on (l ++ l') ≤ f.length_on (l ++ x :: l')
| [] x l' := f.length_on_le_length_on_cons _ _
| [a] x l' := f.length_on_drop_second_cons_le _ _ _
| (a :: b :: l) x l' := by
  { rw [length_on],
    apply add_le_add_left _ (edist (f a) (f b)),
    exact length_on_le_append_singleton_append (b :: l) x l', }

lemma length_on_append_singleton_append :
  ∀ (l : list α) (x : α) (l' : list α),
    f.length_on (l ++ x :: l') = f.length_on (l ++ [x]) + f.length_on (x :: l')
| [] x l' := by { simp only [list.nil_append, length_on_singleton, zero_add], }
| [a] x l' := by
  { simp only [length_on, list.singleton_append, list.cons_append, add_zero, eq_self_iff_true,
               list.nil_append], }
| (a :: b :: l) x l' := by
  { simp only [length_on_cons_cons, list.cons_append, list.append_assoc, list.singleton_append,
               add_assoc],
    congr, exact length_on_append_singleton_append (b::l) x l', }

lemma length_on_mono' :
  ∀ {l l' : list α}, l <+ l' → ∀ x, f.length_on (x::l) ≤ f.length_on (x::l')
| _ _ list.sublist.slnil             x := by { rw [length_on, le_zero_iff], }
| _ _ (list.sublist.cons  l₁ l₂ a s) x :=
  (f.length_on_drop_second_cons_le x a l₁).trans $ add_le_add_left (length_on_mono' s a) _
| _ _ (list.sublist.cons2 l₁ l₂ a s) x := add_le_add_left (length_on_mono' s a) _

lemma length_on_mono : ∀ {l l' : list α}, l <+ l' → f.length_on l ≤ f.length_on l'
| _ _ list.sublist.slnil             := by { rw [length_on, le_zero_iff], }
| _ _ (list.sublist.cons  l₁ l₂ a s) :=
  (f.length_on_le_length_on_cons a l₁).trans $ f.length_on_mono' s a
| _ _ (list.sublist.cons2 l₁ l₂ a s) := f.length_on_mono' s a

lemma edist_le_length_on_of_mem {a b : α} {l : list α} (al : a ∈ l) (bl : b ∈ l) :
  edist (f a) (f b) ≤ f.length_on l :=
begin
  rcases l.pair_mem_list al bl with rfl|ab|ba,
  { rw [edist_self (f a)], exact zero_le', },
  { rw [←length_on_pair], exact f.length_on_mono ab, },
  { rw [edist_comm, ←length_on_pair], exact f.length_on_mono ba, }
end

lemma length_on_congr {f g : α → E} :
  ∀ {l : list α} (h : ∀ x ∈ l, f x = g x), f.length_on l = g.length_on l
| [] h := by simp only [length_on_nil]
| [a] h := by simp only [length_on_singleton]
| (a::b::l) h := by
  { have al : a ∈ a::b::l, by simp only [list.mem_cons_iff, eq_self_iff_true, true_or],
    have bl : b ∈ a::b::l, by simp only [list.mem_cons_iff, eq_self_iff_true, true_or, or_true],
    simp only [length_on_cons_cons, h _ al, h _ bl,
               @length_on_congr (b::l) (λ x xl', h _ (or.inr xl'))], }

lemma length_on_const : ∀ {l : list α} (hc : ∀ x y ∈ l, f x = f y), f.length_on l = 0
| [] h := by simp only [length_on_nil]
| [a] h := by simp only [length_on_singleton]
| (a::b::l) h := by
  { have al : a ∈ a::b::l, by simp only [list.mem_cons_iff, eq_self_iff_true, true_or],
    have bl : b ∈ a::b::l, by simp only [list.mem_cons_iff, eq_self_iff_true, true_or, or_true],
    simp only [length_on_cons_cons, h _ al _ bl, edist_self, add_zero,
               @length_on_const (b::l) (λ x xl' y yl', h _ (or.inr xl') _ (or.inr yl'))], }

end function

end length_on

open emetric nnreal set ennreal measure_theory
open_locale big_operators nnreal ennreal

variables [linear_order α] [linear_order β]
variables (s : set α)


noncomputable def evariation_on : ennreal :=
  ⨆ l ∈ {l : list α | l.pairwise (≤) ∧ ∀ x ∈ l, x ∈ s}, f.length_on l

lemma length_on_le_evariation_on {l : list α} (hl :  l.pairwise (≤) ∧ ∀ x ∈ l, x ∈ s) :
  f.length_on l ≤ evariation_on f s := le_supr₂ l hl

def has_bounded_variation_on := evariation_on f s ≠ ∞

def has_locally_bounded_variation_on :=
∀ a b, a ∈ s → b ∈ s → has_bounded_variation_on f (s ∩ Icc a b)

namespace evariation_on

open function

def sorted_list_nonempty : set.nonempty {l : list α | l.pairwise (≤) ∧ ∀ x∈l, x∈s} :=
  ⟨[], list.pairwise.nil, λ x h, (list.not_mem_nil _ h).elim⟩

variables {f} {s} {t : set α}

lemma eps_approx (h : evariation_on f s ≠ ⊤) (ε : ennreal) (hε : ε ≠ 0) :
  ∃ ll : {l : list α | l.pairwise (≤) ∧ ∀ x ∈ l, x ∈ s},
    evariation_on f s < f.length_on ll.val + ε  :=
begin
  by_contra' hn,
  apply (ennreal.lt_add_right h hε).not_le,
  dsimp only [evariation_on],
  rw [bsupr_add (sorted_list_nonempty s), supr₂_le_iff],
  rw [set_coe.forall] at hn, exact hn,
end

lemma eq_of_eq_on {f f' : α → E} {s : set α} (h : set.eq_on f f' s) :
  evariation_on f s = evariation_on f' s :=
begin
  dsimp only [evariation_on],
  congr' 1 with l : 1,
  congr' 1 with hl : 1,
  exact length_on_congr (λ x xl, h (hl.right x xl)),
end

lemma mono (hst : t ⊆ s) : evariation_on f t ≤ evariation_on f s :=
supr₂_le $ λ l lp, length_on_le_evariation_on f s ⟨lp.left, λ x xl, hst (lp.right x xl)⟩

lemma _root_.has_bounded_variation_on.mono
  (h : has_bounded_variation_on f s) (hst : t ⊆ s) : has_bounded_variation_on f t :=
(lt_of_le_of_lt (evariation_on.mono hst) (lt_top_iff_ne_top.2 h)).ne

lemma _root_.has_bounded_variation_on.has_locally_bounded_variation_on
  (h : has_bounded_variation_on f s) : has_locally_bounded_variation_on f s :=
λ x y hx hy, h.mono (inter_subset_left _ _)

lemma constant_on {f : α → E} {s : set α}
  (hf : (f '' s).subsingleton) : evariation_on f s = 0 :=
begin
  refine le_antisymm (supr₂_le _) zero_le',
  rintros l ⟨lm,ls⟩,
  refine le_of_eq (f.length_on_const _),
  rintro x hx y hy, apply hf; apply set.mem_image_of_mem; apply ls; assumption,
end

@[simp] protected lemma subsingleton (f : α → E) {s : set α} (hs : s.subsingleton) :
  evariation_on f s = 0 := constant_on (hs.image f)

lemma edist_le {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
  edist (f x) (f y) ≤ evariation_on f s :=
begin
  rw ←f.length_on_pair,
  wlog hxy : x ≤ y := le_total x y using [x y, y x] tactic.skip, swap,
  { assume hx hy,
    rw [f.length_on_pair, edist_comm,←f.length_on_pair],
    exact this hy hx },
  apply length_on_le_evariation_on f,
  simp only [hxy, hx, hy, list.pairwise_cons, list.not_mem_nil, is_empty.forall_iff,
             implies_true_iff, list.pairwise.nil, and_self, list.mem_cons_iff, forall_eq_or_imp],
end

lemma _root_.has_bounded_variation_on.dist_le {E : Type*} [pseudo_metric_space E]
  {f : α → E} {s : set α} (h : has_bounded_variation_on f s) {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
  dist (f x) (f y) ≤ (evariation_on f s).to_real :=
begin
  rw [← ennreal.of_real_le_of_real_iff ennreal.to_real_nonneg, ennreal.of_real_to_real h,
      ← edist_dist],
  exact edist_le hx hy
end

lemma _root_.has_bounded_variation_on.sub_le
  {f : α → ℝ} {s : set α} (h : has_bounded_variation_on f s) {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
  f x - f y ≤ (evariation_on f s).to_real :=
begin
  apply (le_abs_self _).trans,
  rw ← real.dist_eq,
  exact h.dist_le hx hy
end

lemma add_le_union (h : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) :
  evariation_on f s + evariation_on f t ≤ evariation_on f (s ∪ t) :=
begin
  dsimp only [evariation_on],
  apply ennreal.bsupr_add_bsupr_le (sorted_list_nonempty s) (sorted_list_nonempty t),
  rintro ll ⟨llm,lls⟩ lr ⟨lrm,lrt⟩,
  apply (f.length_on_append _ _).trans,
  apply length_on_le_evariation_on f,
  simp only [list.pairwise_append, list.mem_append, mem_union],
  split,
  { exact ⟨llm, lrm, λ x xl y yr, h x (lls x xl) y (lrt y yr)⟩,  },
  { rintro x (xl|xr), exact or.inl (lls x xl), exact or.inr (lrt x xr), },
end

lemma union {x : α} (hs : is_greatest s x) (ht : is_least t x) :
  evariation_on f (s ∪ t) = evariation_on f s + evariation_on f t :=
begin
  apply le_antisymm _ (add_le_union (λ u us v vt, (hs.2 us).trans (ht.2 vt))),
  apply supr₂_le _,
  rintro l ⟨lm,lst⟩,
  rw ←list.take_while_append_drop (≤x) l,
  apply (length_on_le_append_singleton_append f _ x _).trans,
  rw length_on_append_singleton_append,
  refine add_le_add _ _,
  { apply length_on_le_evariation_on f,
    split,
    { simp only [list.pairwise_append, list.pairwise_cons, list.not_mem_nil, is_empty.forall_iff,
                 implies_true_iff, list.pairwise.nil, list.mem_singleton, forall_eq, true_and],
      refine ⟨ list.pairwise.sublist (list.take_while_prefix (≤x)).sublist lm, _⟩,
      apply list.mem_take_while_imp, },
    { simp only [list.mem_append, list.mem_singleton],
      rintro u (ul|rfl),
      { let := list.mem_take_while_imp ul,
        specialize lst u ((list.take_while_prefix (≤x)).subset ul),
        change u ∈ s ∨ u ∈ t at lst, cases lst,
        { assumption, },
        { cases le_antisymm this (ht.right lst), exact hs.left, }, },
      { exact hs.left, }, } },
  { apply length_on_le_evariation_on f,
    split,
    { simp only [list.singleton_append, list.pairwise_cons],
      exact ⟨ λ u ul, (lt_of_not_le (list.pairwise_le_drop_while_le_not_le x l lm u ul)).le,
              list.pairwise.sublist (list.drop_while_suffix (≤x)).sublist lm⟩, },
    { simp only [list.singleton_append, list.mem_cons_iff, forall_eq_or_imp],
      refine ⟨ht.left, λ u ul, _⟩,
      specialize lst u ((list.drop_while_suffix (≤x)).subset ul),
      change u ∈ s ∨ u ∈ t at lst, cases lst,
      { exact ((list.pairwise_le_drop_while_le_not_le x l lm u ul) (hs.right lst)).elim, },
      { assumption, }, }, },
end

lemma Icc_add_Icc {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) (hb : b ∈ s) :
  evariation_on f (s ∩ Icc a b) + evariation_on f (s ∩ Icc b c) = evariation_on f (s ∩ Icc a c) :=
begin
  have A : is_greatest (s ∩ Icc a b) b :=
    ⟨⟨hb, hab, le_rfl⟩, (inter_subset_right _ _).trans (Icc_subset_Iic_self)⟩,
  have B : is_least (s ∩ Icc b c) b :=
    ⟨⟨hb, le_rfl, hbc⟩, (inter_subset_right _ _).trans (Icc_subset_Ici_self)⟩,
  rw [← union A B, ← inter_union_distrib_left, Icc_union_Icc_eq_Icc hab hbc],
end

lemma comp_le_of_monotone_on {φ : β → α} {t :set β}
  (mφ : monotone_on φ t) (φst : t.maps_to φ s) : evariation_on (f ∘ φ) t ≤ evariation_on f s :=
begin
  simp only [evariation_on, supr₂_le_iff, ←f.length_on_map φ],
  rintro l ls,
  apply length_on_le_evariation_on f,
  exact ⟨list.pairwise.map_of_maps_to_of_forall φ mφ ls.2 ls.1, list.forall_mem.map φ φst ls.2⟩,
end

lemma comp_le_of_antitone_on {φ : β → α} {t :set β}
  (mφ : antitone_on φ t) (φst : t.maps_to φ s) :
  evariation_on (f ∘ φ) t ≤ evariation_on f s :=
begin
  simp only [evariation_on, supr₂_le_iff, ←f.length_on_map φ],
  rintro l ⟨lm,ls⟩,
  rw [←f.length_on_reverse, ←list.map_reverse],
  apply length_on_le_evariation_on f,
  split,
  { apply list.pairwise.map_of_maps_to_of_forall' φ mφ,
    simp only [list.mem_reverse], exact ls,
    simp only [list.pairwise_reverse, ge_iff_le], exact lm, },
  { simp only [list.mem_reverse, list.mem_map, forall_exists_index, and_imp,
               forall_apply_eq_imp_iff₂],
    rintro a al, apply φst (ls a al), },
end

lemma comp_eq_of_monotone_on {t : set β} [nonempty β] {φ : β → α}
  (hφ : monotone_on φ t) (φst : set.maps_to φ t s) (φsur : set.surj_on φ t s) :
  evariation_on (f ∘ φ) t = evariation_on f s :=
begin
  apply le_antisymm (comp_le_of_monotone_on hφ φst) _,
  let ψ := φ.inv_fun_on t,
  have ψφs : set.eq_on (φ ∘ ψ) id s := φsur.right_inv_on_inv_fun_on,
  have ψts : set.maps_to ψ s t := φsur.maps_to_inv_fun_on,
  have hψ : monotone_on ψ s :=
    function.monotone_on_of_right_inv_on_of_maps_to hφ ψφs ψts,
  change evariation_on (f ∘ id) s ≤ evariation_on (f ∘ φ) t,
  rw ←eq_of_eq_on (ψφs.comp_left : set.eq_on (f ∘ (φ ∘ ψ)) (f ∘ id) s),
  exact comp_le_of_monotone_on hψ ψts,
end

lemma comp_eq_of_antitone_on {t : set β} [nonempty β] {φ : β → α}
  (hφ : antitone_on φ t) (φst : set.maps_to φ t s) (φsur : set.surj_on φ t s) :
  evariation_on (f ∘ φ) t = evariation_on f s :=
begin
  apply le_antisymm (comp_le_of_antitone_on hφ φst),
  let ψ := φ.inv_fun_on t,
  have ψφs : set.eq_on (φ ∘ ψ) id s := φsur.right_inv_on_inv_fun_on,
  have ψts : set.maps_to ψ s t := φsur.maps_to_inv_fun_on,
  have hψ : antitone_on ψ s :=
    function.antitone_on_of_right_inv_on_of_maps_to hφ ψφs ψts,
  change evariation_on (f ∘ id) s ≤ evariation_on (f ∘ φ) t,
  rw ←eq_of_eq_on (ψφs.comp_left : set.eq_on (f ∘ (φ ∘ ψ)) (f ∘ id) s),
  exact comp_le_of_antitone_on hψ ψts,
end

end evariation_on

/-! ## Monotone functions and bounded variation -/

lemma monotone_on.evariation_on_le {f : α → ℝ} {s : set α} (hf : monotone_on f s) {a b : α}
  (as : a ∈ s) (bs : b ∈ s) :
  evariation_on f (s ∩ Icc a b) ≤ ennreal.of_real (f b - f a) :=
begin
  sorry -- stuck on this one…
end

lemma monotone_on.has_locally_bounded_variation_on {f : α → ℝ} {s : set α} (hf : monotone_on f s) :
  has_locally_bounded_variation_on f s :=
λ a b as bs, ((hf.evariation_on_le as bs).trans_lt ennreal.of_real_lt_top).ne

-- TODO : define `p` outside of this: it's the arc-length of `f`.
/-- If a real valued function has bounded variation on a set, then it is a difference of monotone
functions there. -/
lemma has_locally_bounded_variation_on.exists_monotone_on_sub_monotone_on {f : α → ℝ} {s : set α}
  (h : has_locally_bounded_variation_on f s) :
  ∃ (p q : α → ℝ), monotone_on p s ∧ monotone_on q s ∧ f = p - q :=
begin
  rcases eq_empty_or_nonempty s with rfl|hs,
  { exact ⟨f, 0, subsingleton_empty.monotone_on _, subsingleton_empty.monotone_on _,
            by simp only [tsub_zero]⟩ },
  rcases hs with ⟨c, cs⟩,
  let p := λ x, if c ≤ x then (evariation_on f (s ∩ Icc c x)).to_real
    else -(evariation_on f (s ∩ Icc x c)).to_real,
  have hp : monotone_on p s,
  { assume x xs y ys hxy,
    dsimp only [p],
    split_ifs with hcx hcy hcy,
    { have : evariation_on f (s ∩ Icc c x) + evariation_on f (s ∩ Icc x y)
        = evariation_on f (s ∩ Icc c y), from evariation_on.Icc_add_Icc hcx hxy xs,
      rw [← this, ennreal.to_real_add (h c x cs xs) (h x y xs ys)],
      exact le_add_of_le_of_nonneg le_rfl ennreal.to_real_nonneg },
    { exact (lt_irrefl _ ((not_le.1 hcy).trans_le (hcx.trans hxy))).elim },
    { exact (neg_nonpos.2 ennreal.to_real_nonneg).trans ennreal.to_real_nonneg },
    { simp only [neg_le_neg_iff],
      have : evariation_on f (s ∩ Icc x y) + evariation_on f (s ∩ Icc y c)
        = evariation_on f (s ∩ Icc x c), from evariation_on.Icc_add_Icc hxy (not_le.1 hcy).le ys,
      rw [← this, ennreal.to_real_add (h x y xs ys) (h y c ys cs), add_comm],
      exact le_add_of_le_of_nonneg le_rfl ennreal.to_real_nonneg } },
  have hq : monotone_on (λ x, p x - f x) s,
  { assume x xs y ys hxy,
    dsimp only [p],
    split_ifs with hcx hcy hcy,
    { have : evariation_on f (s ∩ Icc c x) + evariation_on f (s ∩ Icc x y)
        = evariation_on f (s ∩ Icc c y), from evariation_on.Icc_add_Icc hcx hxy xs,
      rw [← this, ennreal.to_real_add (h c x cs xs) (h x y xs ys)],
      suffices : f y - f x ≤ (evariation_on f (s ∩ Icc x y)).to_real, by linarith,
      exact (h x y xs ys).sub_le ⟨ys, hxy, le_rfl⟩ ⟨xs, le_rfl, hxy⟩ },
    { exact (lt_irrefl _ ((not_le.1 hcy).trans_le (hcx.trans hxy))).elim },
    { suffices : f y - f x ≤ (evariation_on f (s ∩ Icc x c)).to_real
        + (evariation_on f (s ∩ Icc c y)).to_real, by linarith,
      rw [← ennreal.to_real_add (h x c xs cs) (h c y cs ys),
          evariation_on.Icc_add_Icc (not_le.1 hcx).le hcy cs],
      exact (h x y xs ys).sub_le ⟨ys, hxy, le_rfl⟩ ⟨xs, le_rfl, hxy⟩ },
    { have : evariation_on f (s ∩ Icc x y) + evariation_on f (s ∩ Icc y c)
        = evariation_on f (s ∩ Icc x c), from evariation_on.Icc_add_Icc hxy (not_le.1 hcy).le ys,
      rw [← this, ennreal.to_real_add (h x y xs ys) (h y c ys cs)],
      suffices : f y - f x ≤ (evariation_on f (s ∩ Icc x y)).to_real, by linarith,
      exact (h x y xs ys).sub_le ⟨ys, hxy, le_rfl⟩ ⟨xs, le_rfl, hxy⟩ } },
  refine ⟨p, λ x, p x - f x, hp, hq, _⟩,
  ext x,
  dsimp,
  abel,
end

/-! ## Lipschitz functions and bounded variation -/

lemma function.length_on_postcomp_of_lipschitz_on {f : E → F} {C : ℝ≥0} {t : set E}
  (h : lipschitz_on_with C f t) {g : α → E} {s : set α} (hg : maps_to g s t) :
  ∀ l : list α, (∀ x ∈ l, x ∈ s) → (f ∘ g).length_on l ≤ C * (g.length_on l)
| [] hl := by simp only [function.length_on_nil, mul_zero, le_zero_iff]
| [a] hl := by simp only [function.length_on_singleton, mul_zero, le_zero_iff]
| (a::b::l) hl := by
  { simp only [function.length_on_cons_cons, mul_add, function.comp_app],
    refine add_le_add _ _,
    { apply h; apply hg; apply hl; simp, },
    { exact function.length_on_postcomp_of_lipschitz_on (b::l) (λ x xl', hl x (or.inr xl')), }, }

lemma lipschitz_on_with.comp_evariation_on_le {f : E → F} {C : ℝ≥0} {t : set E}
  (h : lipschitz_on_with C f t) {g : α → E} {s : set α} (hg : maps_to g s t) :
  evariation_on (f ∘ g) s ≤ C * (evariation_on g s) :=
supr₂_le (λ l hl, (function.length_on_postcomp_of_lipschitz_on h hg l hl.2).trans
         (mul_le_mul_left' (length_on_le_evariation_on _ _ hl) ↑C))

lemma lipschitz_on_with.comp_has_bounded_variation_on {f : E → F} {C : ℝ≥0} {t : set E}
  (hf : lipschitz_on_with C f t) {g : α → E} {s : set α} (hg : maps_to g s t)
  (h : has_bounded_variation_on g s) :
  has_bounded_variation_on (f ∘ g) s :=
begin
  dsimp only [has_bounded_variation_on] at h,
  apply ne_of_lt,
  apply (hf.comp_evariation_on_le hg).trans_lt,
  simp [lt_top_iff_ne_top, h],
end

lemma lipschitz_on_with.comp_has_locally_bounded_variation_on {f : E → F} {C : ℝ≥0} {t : set E}
  (hf : lipschitz_on_with C f t) {g : α → E} {s : set α} (hg : maps_to g s t)
  (h : has_locally_bounded_variation_on g s) :
  has_locally_bounded_variation_on (f ∘ g) s :=
λ x y xs ys, hf.comp_has_bounded_variation_on (hg.mono_left (inter_subset_left _ _)) (h x y xs ys)

lemma lipschitz_with.comp_has_bounded_variation_on {f : E → F} {C : ℝ≥0}
  (hf : lipschitz_with C f) {g : α → E} {s : set α} (h : has_bounded_variation_on g s) :
  has_bounded_variation_on (f ∘ g) s :=
(hf.lipschitz_on_with univ).comp_has_bounded_variation_on (maps_to_univ _ _) h

lemma lipschitz_with.comp_has_locally_bounded_variation_on {f : E → F} {C : ℝ≥0}
  (hf : lipschitz_with C f) {g : α → E} {s : set α} (h : has_locally_bounded_variation_on g s) :
  has_locally_bounded_variation_on (f ∘ g) s :=
(hf.lipschitz_on_with univ).comp_has_locally_bounded_variation_on (maps_to_univ _ _) h

lemma lipschitz_on_with.has_locally_bounded_variation_on {f : ℝ → E} {C : ℝ≥0} {s : set ℝ}
  (hf : lipschitz_on_with C f s) : has_locally_bounded_variation_on f s :=
hf.comp_has_locally_bounded_variation_on (maps_to_id _)
  (@monotone_on_id ℝ _ s).has_locally_bounded_variation_on

lemma lipschitz_with.has_locally_bounded_variation_on {f : ℝ → E} {C : ℝ≥0}
  (hf : lipschitz_with C f) (s : set ℝ) : has_locally_bounded_variation_on f s :=
(hf.lipschitz_on_with s).has_locally_bounded_variation_on

/-! ## Almost everywhere differentiability of functions with locally bounded variation -/

variables {V : Type*} [normed_add_comm_group V] [normed_space ℝ V] [finite_dimensional ℝ V]

namespace has_locally_bounded_variation_on

/-- A bounded variation function into `ℝ` is differentiable almost everywhere. Superseded by
`ae_differentiable_within_at_of_mem`. -/
theorem ae_differentiable_within_at_of_mem_real
  {f : ℝ → ℝ} {s : set ℝ} (h : has_locally_bounded_variation_on f s) :
  ∀ᵐ x, x ∈ s → differentiable_within_at ℝ f s x :=
begin
  obtain ⟨p, q, hp, hq, fpq⟩ : ∃ p q, monotone_on p s ∧ monotone_on q s ∧ f = p - q,
    from h.exists_monotone_on_sub_monotone_on,
  filter_upwards [hp.ae_differentiable_within_at_of_mem, hq.ae_differentiable_within_at_of_mem]
    with x hxp hxq xs,
  have fpq : ∀ x, f x = p x - q x, by simp [fpq],
  refine ((hxp xs).sub (hxq xs)).congr (λ y hy, fpq y) (fpq x),
end

/-- A bounded variation function into a finite dimensional product vector space is differentiable
almost everywhere. Superseded by `ae_differentiable_within_at_of_mem`. -/
theorem ae_differentiable_within_at_of_mem_pi {ι : Type*} [fintype ι]
  {f : ℝ → (ι → ℝ)} {s : set ℝ} (h : has_locally_bounded_variation_on f s) :
  ∀ᵐ x, x ∈ s → differentiable_within_at ℝ f s x :=
begin
  have A : ∀ (i : ι), lipschitz_with 1 (λ (x : ι → ℝ), x i) := λ i, lipschitz_with.eval i,
  have : ∀ (i : ι), ∀ᵐ x, x ∈ s → differentiable_within_at ℝ (λ (x : ℝ), f x i) s x,
  { assume i,
    apply ae_differentiable_within_at_of_mem_real,
    exact lipschitz_with.comp_has_locally_bounded_variation_on (A i) h },
  filter_upwards [ae_all_iff.2 this] with x hx xs,
  exact differentiable_within_at_pi.2 (λ i, hx i xs),
end

/-- A real function into a finite dimensional real vector space with bounded variation on a set
is differentiable almost everywhere in this set. -/
theorem ae_differentiable_within_at_of_mem
  {f : ℝ → V} {s : set ℝ} (h : has_locally_bounded_variation_on f s) :
  ∀ᵐ x, x ∈ s → differentiable_within_at ℝ f s x :=
begin
  let A := (basis.of_vector_space ℝ V).equiv_fun.to_continuous_linear_equiv,
  suffices H : ∀ᵐ x, x ∈ s → differentiable_within_at ℝ (A ∘ f) s x,
  { filter_upwards [H] with x hx xs,
    have : f = (A.symm ∘ A) ∘ f,
      by simp only [continuous_linear_equiv.symm_comp_self, function.comp.left_id],
    rw this,
    exact A.symm.differentiable_at.comp_differentiable_within_at x (hx xs) },
  apply ae_differentiable_within_at_of_mem_pi,
  exact A.lipschitz.comp_has_locally_bounded_variation_on h,
end

/-- A real function into a finite dimensional real vector space with bounded variation on a set
is differentiable almost everywhere in this set. -/
theorem ae_differentiable_within_at
  {f : ℝ → V} {s : set ℝ} (h : has_locally_bounded_variation_on f s) (hs : measurable_set s) :
  ∀ᵐ x ∂(volume.restrict s), differentiable_within_at ℝ f s x :=
begin
  rw ae_restrict_iff' hs,
  exact h.ae_differentiable_within_at_of_mem
end

/-- A real function into a finite dimensional real vector space with bounded variation
is differentiable almost everywhere. -/
theorem ae_differentiable_at {f : ℝ → V} (h : has_locally_bounded_variation_on f univ) :
  ∀ᵐ x, differentiable_at ℝ f x :=
begin
  filter_upwards [h.ae_differentiable_within_at_of_mem] with x hx,
  rw differentiable_within_at_univ at hx,
  exact hx (mem_univ _),
end

end has_locally_bounded_variation_on

/-- A real function into a finite dimensional real vector space which is Lipschitz on a set
is differentiable almost everywhere in this set . -/
lemma lipschitz_on_with.ae_differentiable_within_at_of_mem
  {C : ℝ≥0} {f : ℝ → V} {s : set ℝ} (h : lipschitz_on_with C f s) :
  ∀ᵐ x, x ∈ s → differentiable_within_at ℝ f s x :=
h.has_locally_bounded_variation_on.ae_differentiable_within_at_of_mem

/-- A real function into a finite dimensional real vector space which is Lipschitz on a set
is differentiable almost everywhere in this set. -/
lemma lipschitz_on_with.ae_differentiable_within_at
  {C : ℝ≥0} {f : ℝ → V} {s : set ℝ} (h : lipschitz_on_with C f s) (hs : measurable_set s) :
  ∀ᵐ x ∂(volume.restrict s), differentiable_within_at ℝ f s x :=
h.has_locally_bounded_variation_on.ae_differentiable_within_at hs

/-- A real Lipschitz function into a finite dimensional real vector space is differentiable
almost everywhere. -/
lemma lipschitz_with.ae_differentiable_at
  {C : ℝ≥0} {f : ℝ → V} (h : lipschitz_with C f) :
  ∀ᵐ x, differentiable_at ℝ f x :=
(h.has_locally_bounded_variation_on univ).ae_differentiable_at
