/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import data.fintype.card
import data.fin.tuple
import data.fin.vec_notation

/-!
# Stars and Bars

Note there are typically two interpretation of stars and bars; a version that only allows a bar
to be between two stars, and a version that allows bars to be adjacent to each other and to the
end of the list. This file implements the latter.

## Main definitions

* `stars_and_bars s b`: The type of orderings of `s` stars and `b` bars

## Main statements

* `stars_and_bars.card s b`: The cardinality of `stars_and_bars s b` is `(s + b).choose b`
* `stars_and_bars.equiv_list`: `stars_and_bars s b` is isomorphic to a list of booleans

## References

* https://en.wikipedia.org/wiki/Stars_and_bars_(combinatorics)
-/

open_locale big_operators

@[simp]
lemma finset.card_disj_union {α} (s t : finset α) (h) : (s.disj_union t h).card = s.card + t.card :=
multiset.card_add _ _

/-- The type of `s` stars and `b` bars.

This is the version that allows bars to be adjacent to each other. -/
inductive stars_and_bars : Π s b : ℕ, Type
| nil : stars_and_bars 0 0
| star {s b} (x : stars_and_bars s b) : stars_and_bars (nat.succ s) b
| bar {s b} (x : stars_and_bars s b) : stars_and_bars s (nat.succ b)

namespace stars_and_bars

/-- `stars_and_bars.star` as an embedding. -/
@[simps] def star_embedding {s b : ℕ} : stars_and_bars s b ↪ stars_and_bars s.succ b :=
⟨star, λ _ _, star.inj⟩

/-- `stars_and_bars.bar` as an embedding. -/
@[simps] def bar_embedding {s b : ℕ} : stars_and_bars s b ↪ stars_and_bars s b.succ :=
⟨bar, λ _ _, bar.inj⟩

/-- An iterated version of `stars_and_bars.star` -/
@[simp]
def stars : Π {s b : ℕ}, stars_and_bars s b → Π s', stars_and_bars (s + s') b
| s b x 0 := x
| s b x (s' + 1) := (x.stars s').star

/-- An iterated version of `stars_and_bars.bar` -/
@[simp]
def bars : Π {s b : ℕ}, stars_and_bars s b → Π b', stars_and_bars s (b + b')
| s b x 0 := x
| s b x (b' + 1) := (x.bars b').bar

protected def repr_aux : Π {s b : ℕ}, stars_and_bars s b → string
| _ _ (nil)      := ""
| _ _ (star x) := "⋆" ++ repr_aux x
| _ _ (bar x) := "|" ++ repr_aux x

/-- Produces a string like `(⋆⋆|⋆||⋆)` for an element of `stars_and_bars 4 3` -/
instance {s b : ℕ}  : has_repr (stars_and_bars s b) :=
⟨λ s, "(" ++ s.repr_aux ++ ")"⟩

@[simp]
def append : Π {s₁ b₁ s₂ b₂ : ℕ} (x₁ : stars_and_bars s₁ b₁) (x₂ : stars_and_bars s₂ b₂),
  stars_and_bars (s₂ + s₁) (b₂ + b₁)
| _ _ _ _ nil x₂ := x₂
| _ _ _ _ (star x₁) x₂ := (append x₁ x₂).star
| _ _ _ _ (bar x₁) x₂ := (append x₁ x₂).bar

#print list.append

/-! ### Cardinality and finiteness -/
section card

lemma mem_map_embedding_elim {s b : ℕ}
  {s₁ : finset (stars_and_bars s b.succ)} {s₂ : finset (stars_and_bars s.succ b)}
  (x : stars_and_bars s.succ b.succ)
  (hs : x ∈ s₁.map star_embedding) (hb : x ∈ s₂.map bar_embedding) : false :=
begin
  rw finset.mem_map at hs hb,
  obtain ⟨xs, -, rfl⟩ := hs,
  obtain ⟨xb, -, hsb⟩ := hb,
  injection hsb
end

instance : Π {s b : ℕ}, fintype (stars_and_bars s b)
| 0 0 := { elems := {nil}, complete := λ x, by {cases x, simp} }
| (nat.succ s) 0 := begin
  let : s < s.succ := nat.lt_succ_self _,
  haveI : _root_.fintype (stars_and_bars s 0) := fintype,
  refine ⟨finset.univ.map star_embedding, λ x, _⟩,
  cases x,
  simp
end
| 0 (nat.succ b) := begin
  let : b < b.succ := nat.lt_succ_self _,
  haveI : _root_.fintype (stars_and_bars 0 b) := fintype,
  refine ⟨finset.univ.map bar_embedding, λ x, _⟩,
  cases x,
  simp
end
| (nat.succ s) (nat.succ b) := begin
  let : s < s.succ := nat.lt_succ_self _,
  let : b < b.succ := nat.lt_succ_self _,
  haveI : _root_.fintype (stars_and_bars (nat.succ s) b) := fintype,
  haveI : _root_.fintype (stars_and_bars s (nat.succ b)) := fintype,
  refine ⟨(finset.univ.map star_embedding).disj_union
          (finset.univ.map bar_embedding) mem_map_embedding_elim, λ x, _⟩,
  cases x; simp
end
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ f, f.1 + f.2)⟩] }

@[simp] lemma univ_zero_zero : (finset.univ : finset (stars_and_bars 0 0)) = {nil} :=
by rw [finset.univ, stars_and_bars.fintype]

lemma univ_zero_succ (b : ℕ) :
  (finset.univ : finset (stars_and_bars 0 b.succ)) = finset.univ.map bar_embedding :=
by rw [finset.univ, stars_and_bars.fintype]

lemma univ_succ_zero (s : ℕ) :
  (finset.univ : finset (stars_and_bars s.succ 0)) = finset.univ.map star_embedding :=
by rw [finset.univ, stars_and_bars.fintype]

lemma univ_succ_succ (s b : ℕ) :
  (finset.univ : finset (stars_and_bars s.succ b.succ)) =
    (finset.univ.map star_embedding).disj_union (finset.univ.map bar_embedding)
      mem_map_embedding_elim :=
by rw [finset.univ, stars_and_bars.fintype]

lemma card : Π (s b : ℕ),
  fintype.card (stars_and_bars s b) = nat.choose (s + b) b
| 0 0 := by simp [fintype.card, univ_zero_zero]
| 0 (nat.succ b) := have b < b.succ, from nat.lt_succ_self _,
  by simpa [fintype.card, univ_zero_succ] using card 0 b
| (nat.succ s) 0 := have s < s.succ, from nat.lt_succ_self _,
  by simpa [fintype.card, univ_succ_zero] using card s 0
| (nat.succ s) (nat.succ b) :=
  have s < s.succ, from nat.lt_succ_self _,
  have b < b.succ, from nat.lt_succ_self _,
  by simpa [fintype.card, univ_succ_succ, nat.add_succ, nat.succ_add_eq_succ_add,
    (s + b).succ.choose_succ_succ] using
    (add_comm _ _).trans (congr_arg2 (+) (card s.succ b) (card s b.succ))
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ f, f.1 + f.2)⟩] }

end card

/-! ### Other representations -/

section list
open list

/--
The equation compiler does not generate nice lemmas for these definitions, in that it splits `n`
into `0` and `n.succ` even when both statements are teh same. As such, we state all the internal
proofs as standalone lemmas, so that we can use them again in our own equation-like lemmas
-/

lemma to_list.nil_proof : [].count ff = 0 ∧ [].count tt = 0 :=
⟨count_nil _, count_nil _⟩

lemma to_list.star_proof {s b : ℕ} (x : stars_and_bars s b) {l : list bool}
  (hl : l.count ff = s ∧ l.count tt = b) :
  (ff :: l).count ff = s.succ ∧ (ff :: l).count tt = b :=
⟨(count_cons_self _ _).trans (congr_arg nat.succ hl.1),
  (count_cons_of_ne tt_eq_ff_eq_false _).trans hl.2⟩

lemma to_list.bar_proof {s b : ℕ} (x : stars_and_bars s b) {l : list bool}
  (hl : l.count ff = s ∧ l.count tt = b) :
  (tt :: l).count ff = s ∧ (tt :: l).count tt = b.succ :=
⟨(count_cons_of_ne ff_eq_tt_eq_false _).trans hl.1,
  (count_cons_self _ _).trans (congr_arg nat.succ hl.2)⟩

/-- Convert `stars_and_bars s b` to a list with `s` `ff`s and `b` `tt`s. -/
def to_list : Π {s b : ℕ},
  stars_and_bars s b → {l : list bool // l.count ff = s ∧ l.count tt = b}
| 0 0 nil := ⟨[], stars_and_bars.to_list.nil_proof⟩
| (nat.succ s) b (star x) := ⟨ff :: to_list x, stars_and_bars.to_list.star_proof x (to_list x).prop⟩
| s (nat.succ b) (bar x) := ⟨tt :: to_list x, stars_and_bars.to_list.bar_proof x (to_list x).prop⟩

@[simp] lemma to_list_nil : to_list nil = ⟨[], to_list.nil_proof⟩ := rfl
@[simp] lemma to_list_star {s b : ℕ} (x : stars_and_bars s b) :
  to_list (star x) = ⟨ff :: to_list x, to_list.star_proof x (to_list x).prop⟩ :=
by {cases b; refl}
@[simp] lemma to_list_bar {s b : ℕ} (x : stars_and_bars s b) :
  to_list (bar x) = ⟨tt :: to_list x, to_list.bar_proof x (to_list x).prop⟩ :=
by {cases s; refl}

lemma of_list.tt_proof {s b : ℕ} {l : list bool}
  (hl : (tt :: l).count ff = s ∧ (tt :: l).count tt = b.succ) :
  l.count ff = s ∧ l.count tt = b :=
⟨(count_cons_of_ne ff_eq_tt_eq_false _).symm.trans hl.1,
  nat.succ.inj $ (count_cons_self _ _).symm.trans hl.2⟩

lemma of_list.ff_proof {s b : ℕ} {l : list bool}
  (hl : (ff :: l).count ff = s.succ ∧ (ff :: l).count tt = b) :
  l.count ff = s ∧ l.count tt = b :=
⟨nat.succ.inj $ (count_cons_self _ _).symm.trans hl.1,
  (count_cons_of_ne tt_eq_ff_eq_false _).symm.trans hl.2⟩

/-- Convert a list with `s` `ff`s and `b` `tt`s to `stars_and_bars s b` -/
def of_list : Π {s b : ℕ},
  {l : list bool // l.count ff = s ∧ l.count tt = b} → stars_and_bars s b
| 0 0 ⟨[], _⟩ := nil
| s (nat.succ b) ⟨tt :: l, h⟩ := have b < b.succ := nat.lt_succ_self _,
    (of_list ⟨l, stars_and_bars.of_list.tt_proof h⟩).bar
| (nat.succ s) b ⟨ff :: l, h⟩ := have s < s.succ := nat.lt_succ_self _,
    (of_list ⟨l, stars_and_bars.of_list.ff_proof h⟩).star

@[simp] lemma of_list_nil (hl) : of_list ⟨[], hl⟩ = stars_and_bars.nil := by rw of_list
@[simp] lemma of_list_tt_cons {s b : ℕ} (l : list bool)
  (hl : (tt :: l).count ff = s ∧ (tt :: l).count tt = b.succ) :
  of_list ⟨tt :: l, hl⟩ = (of_list ⟨l, of_list.tt_proof hl⟩).bar :=
by { cases s; rw of_list }
@[simp] lemma of_list_ff_cons {s b : ℕ} (l : list bool)
  (hl : (ff :: l).count ff = s.succ ∧ (ff :: l).count tt = b) :
  of_list ⟨ff :: l, hl⟩ = (of_list ⟨l, of_list.ff_proof hl⟩).star :=
by { cases b; rw of_list }

lemma of_list_to_list : Π {s b : ℕ} (x : stars_and_bars s b),
  of_list (to_list x) = x
| 0 0 nil := by simp
| (nat.succ s) b (star x) := by simp [of_list_to_list]
| s (nat.succ b) (bar x) := by simp [of_list_to_list]

lemma to_list_of_list : Π {s b : ℕ} (l : {l : list bool // l.count ff = s ∧ l.count tt = b}),
  to_list (of_list l) = l
| 0 0 ⟨[], _⟩ := by simp
| s (nat.succ b) ⟨tt :: l, h⟩  := have b < b.succ := nat.lt_succ_self _,
    by simp [@to_list_of_list s b]
| (nat.succ s) b ⟨ff :: l, h⟩  := have s < s.succ := nat.lt_succ_self _,
    by simp [@to_list_of_list s b]

/-- `stars_and_bars.to_list` and `stars_and_bars.of_list` form an equiv. -/
@[simps] def equiv_list {s b : ℕ} :
  stars_and_bars s b ≃ {l : list bool // l.count ff = s ∧ l.count tt = b} :=
{ to_fun := to_list,
  inv_fun := of_list,
  left_inv := of_list_to_list,
  right_inv := to_list_of_list }

end list

section tuple

@[elab_as_eliminator]
lemma _root_.fin.cons_induction {n : ℕ} {α : fin n.succ → Type*} {P : (Π i : fin n.succ, α i) → Prop}
  (h : ∀ x₀ x, P (fin.cons x₀ x)) (x : (Π i : fin n.succ, α i)) : P x :=
fin.cons_self_tail x ▸ h (x 0) (fin.tail x)

/-- The tuple corresponding to the number of consecutive stars between the bars. -/
@[simp]
def to_tuple : Π {s b : ℕ}, stars_and_bars s b → {f : fin b.succ → ℕ // ∑ i, f i = s}
| _ _ nil := ⟨![0], by simp⟩
| (nat.succ s) b (star x) :=
  ⟨fin.cons ((to_tuple x : fin b.succ → ℕ) 0).succ (fin.tail (to_tuple x : fin b.succ → ℕ)), begin
    generalize : to_tuple x = f,
    cases f with f hf,
    refine fin.cons_induction (λ x₀ x, _) f hf,
    rintro rfl,
    simp [nat.succ_add_eq_succ_add, nat.add_succ, fin.sum_univ_succ],
  end⟩
| s (nat.succ b) (bar x) := ⟨fin.cons 0 (to_tuple x), begin
    generalize : to_tuple x = f,
    cases f with f hf,
    refine fin.cons_induction (λ x₀ x, _) f hf,
    rintro rfl,
    simp [fin.sum_univ_succ],
  end⟩

attribute [pattern] matrix.vec_cons

/-- The stars and bars produced by joining `f i` stars with bars inbetween. -/
@[simp]
def of_tuple : Π {s b : ℕ}, {f : fin b.succ → ℕ // ∑ i, f i = s} → stars_and_bars s b
| s 0 ⟨f, _⟩ := begin
  convert (nil.stars s),
  rw zero_add
end
| s (nat.succ b) ⟨f, hf⟩ := begin
  rw [fin.sum_univ_succ, add_comm] at hf,
  subst hf,
  exact (of_tuple ⟨fin.tail f, rfl⟩).bar.stars (f 0),
end

set_option trace.check true

lemma to_tuple_of_tuple : Π {s b : ℕ} (f : {f : fin b.succ → ℕ // ∑ i, f i = s}),
  to_tuple (of_tuple f) = f
| s 0 ⟨f, hf⟩ := begin
  ext x,
  dsimp,
  rw subsingleton.elim x 0,
  sorry
  -- dsimp,
  -- rw [fin.sum_univ_succ, fin.sum_univ_zero, add_zero] at hf,
  -- rw hf,
  -- clear hf,
  -- generalize : cast _ (nil.stars s) = q,
  -- cases hq : q,
  -- { simp, },
  -- { rw to_tuple,
  --   simp, },
  -- dsimp,
  -- simp,
end
| s (nat.succ b) ⟨f, hf⟩ := begin
  refine fin.cons_induction _ f hf,
  intros x₀ x hx,
  rw fin.sum_univ_succ at hx,
  simp_rw [of_tuple,fin.tail_cons],
  generalize_proofs h1 h2,
  revert hx,
  simp_rw fin.cons_zero,
  simp_rw fin.cons_zero,  -- why?
end

lemma of_tuple_to_tuple : Π {s b : ℕ} (x : stars_and_bars s b),
  of_tuple (to_tuple x) = x
| _ _ nil := rfl
| (nat.succ s) b (star x) := begin
  simp,
end
| s (nat.succ b) (bar x) := begin
  simp,
  have := (of_tuple.equations._eqn_2 s b (fin.cons 0 ↑(x.to_tuple)) _),
  swap,
  { rw fin.sum_univ_succ,
    simp_rw [fin.cons_zero, zero_add, fin.cons_succ],
    exact (x.to_tuple).prop,},
  refine this.trans _,
  simp only [fin.tail_cons, subtype.coe_eta],
  simp_rw fin.cons_zero,
  -- simp_rw [fin.tail_cons] at this,
  -- simp_rw fin.cons_zero (0 : (λ i : fin b.succ.succ, ℕ) 0) at this,
  -- convert this using 1,
end

#print prefix stars_and_bars.of_tuple.equations

/-- `stars_and_bars.to_tuple` and `stars_and_bars.of_tuple` form an equiv. -/
def equiv_tuple {s b : ℕ} : stars_and_bars s b ≃ {f : fin b.succ → ℕ // ∑ i, f i = s} :=
{ to_fun := _,
  inv_fun := _,
  left_inv := of_tuple_to_tuple,
  right_inv := to_tuple_of_tuple }

#print prefix stars_and_bars.of_tuple.equations

end tuple

end stars_and_bars
