/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import algebra.order.archimedean
import data.set.pointwise
import order.upper_lower

/-!
# Dedeking cuts

A basic theory of Dedekind cuts, used in a construction of the reals.

## Important definitions

- `dedekind_cut Q` is an `add_comm_group` when `Q` is `linear_ordered_field` and `archimedean`
- TODO: finish constructing the full field

## Tags

dedekind, real, cut

## References

[Rudin, *Principles of Mathematical Analysis* (Chapter 1, Appendix)][rudin1976]

-/

section

variables (Q : Type*) [has_lt Q]

/-- *Dedekind cut*, defined for an arbitrary type with a less-than relation -/
@[ext] structure dedekind_cut :=
(carrier : set Q)
(nonempty' : carrier.nonempty) -- Step 1, (I), first half
(ne_top' : carrier ≠ ⊤) -- Step 1, (I), second half
(is_lt_lower' : ∀ ⦃p q : Q⦄, q < p → p ∈ carrier → q ∈ carrier) -- Step 1, (II)
(exists_gt' : ∀ ⦃p : Q⦄, p ∈ carrier → ∃ (r : Q) (hr : r ∈ carrier), p < r) -- Step 1, (III)

variables {Q}

namespace dedekind_cut

instance : set_like (dedekind_cut Q) Q :=
⟨dedekind_cut.carrier, λ p q h, by cases p; cases q; congr'⟩

variables {α β γ : dedekind_cut Q} {p q r : Q}

@[simp]
lemma mem_carrier : p ∈ α.carrier ↔ p ∈ α := iff.rfl

@[simp]
lemma mem_coe : p ∈ (α : set Q) ↔ p ∈ α := iff.rfl

@[simp]
lemma mem_mk {s : set Q} (hn hne hl hg) : p ∈ mk s hn hne hl hg ↔ p ∈ s := iff.rfl

variables (α)

lemma nonempty : (α : set Q).nonempty := α.nonempty'
lemma lt_top : (α : set Q) < ⊤ :=
begin
  split,
  { simp },
  have := α.ne_top',
  contrapose! this,
  ext,
  simp only [mem_carrier, set.top_eq_univ, set.mem_univ, iff_true],
  exact this (by simp)
end
lemma is_lt_lower ⦃p q : Q⦄ (h : q < p) (hp : p ∈ α) : q ∈ α := α.is_lt_lower' h hp
lemma exists_gt ⦃p : Q⦄ (hp : p ∈ α) : ∃ (r : Q) (hr : r ∈ α), p < r := α.exists_gt' hp
lemma exists_not_mem : ∃ (r : Q), r ∉ α :=
begin
  have := α.ne_top',
  contrapose! this,
  ext,
  simpa using this _
end

lemma is_lower_set {Q : Type*} [partial_order Q] (α : dedekind_cut Q) : is_lower_set (α : set Q) :=
begin
  intros p q h hp,
  rcases h.eq_or_lt with rfl|h,
  { exact hp },
  { exact α.is_lt_lower h hp }
end

lemma lt_of_mem_of_not_mem {Q : Type*} [linear_order Q] {α : dedekind_cut Q} {p q : Q}
  (hp : p ∈ α) (hq : q ∉ α) : p < q :=
begin
  contrapose! hq,
  exact α.is_lower_set hq hp
end

lemma not_mem_of_lt_of_not_mem {r s : Q} (h : r < s) (hr : r ∉ α) : s ∉ α :=
mt (α.is_lt_lower h) hr

noncomputable instance {Q : Type*} [linear_order Q] : linear_order (dedekind_cut Q) := -- Step 2
{ le_total := λ α β, begin
    by_cases h : α ≤ β,
    { exact or.inl h },
    { obtain ⟨p, hp, hnp⟩ : ∃ (p : Q) (hp : p ∈ α), p ∉ β,
      { contrapose! h, exact h },
      exact or.inr (λ q hq, α.is_lt_lower (lt_of_mem_of_not_mem hq hnp) hp) }
  end,
  decidable_le := classical.dec_rel (≤),
  ..set_like.partial_order }

-- Step 3
/-- Dedekind cuts have the least-upper-bound property, where a Sup of a non-empty, bounded above
set of cuts can be constructed. See `le_cSup` and `is_lub_cSup` for the resulting bound
properties. -/
def cSup (A : set (dedekind_cut Q)) (hA : A.nonempty) (hA' : bdd_above A) : dedekind_cut Q :=
{ carrier := Sup (coe '' A),
  nonempty' := begin
    obtain ⟨α₀, hα₀⟩ := hA,
    refine Exists.imp _ α₀.nonempty,
    simp only [mem_coe, set.Sup_eq_sUnion, set.sUnion_image, set.mem_Union, exists_prop],
    exact λ p hp, ⟨α₀, hα₀, hp⟩
  end,
  ne_top' := begin
    refine ne_of_lt _,
    obtain ⟨β, hβ⟩ := hA',
    refine lt_of_le_of_lt (λ p hp, _) β.lt_top,
    simp only at hp,
    simp only [set.Sup_eq_sUnion, set.sUnion_image, set.mem_Union, mem_coe, exists_prop] at hp,
    obtain ⟨α, hα, hp⟩ := hp,
    exact hβ hα hp,
  end,
  is_lt_lower' := λ p q h, begin
    simp only [set.Sup_eq_sUnion, set.sUnion_image, set.mem_Union, mem_coe],
    exact Exists₂.imp (λ _ _, is_lt_lower _ h)
  end,
  exists_gt' := λ p, begin
    simp only [set.Sup_eq_sUnion, set.sUnion_image, set.mem_Union, mem_coe, exists_prop,
               forall_exists_index, and_imp],
    intros α hα hp,
    refine (α.exists_gt hp).imp _,
    rintro q ⟨hq, h⟩,
    exact ⟨⟨α, hα, hq⟩, h⟩
  end }

@[simp]
lemma mem_cSup {A : set (dedekind_cut Q)} {hA : A.nonempty} {hA' : bdd_above A} :
  p ∈ cSup A hA hA' ↔ ∃ α ∈ A, α ∈ A ∧ p ∈ α :=
by simp [cSup]

lemma le_cSup (A : set (dedekind_cut Q)) (hA : A.nonempty) (hA' : bdd_above A) (hα : α ∈ A) :
  α ≤ cSup A hA hA' :=
λ p hp, by { simp only [mem_cSup, exists_prop, and_self_left], exact ⟨α, hα, hp⟩ }

lemma is_lub_cSup (A : set (dedekind_cut Q)) (hA : A.nonempty) (hA' : bdd_above A) :
  is_lub A (cSup A hA hA') :=
begin
  refine ⟨λ _, le_cSup _ _ _ _, λ δ hδ s hs, _⟩,
  simp only [mem_cSup, exists_prop, and_self_left] at hs,
  obtain ⟨α, hα, hs⟩ := hs,
  exact hδ hα hs
end

open_locale pointwise

-- Step 4 (A1)
instance {Q : Type*} [linear_order Q] [add_group Q]
  [covariant_class Q Q (+) (<)] [covariant_class Q Q (function.swap (+)) (<)] :
  has_add (dedekind_cut Q) :=
⟨λ α β, { carrier := α + β,
  nonempty' := by { obtain ⟨p, hp⟩ := α.nonempty, obtain ⟨q, hq⟩ := β.nonempty,
    exact ⟨p + q, p, q, hp, hq, rfl⟩ },
  ne_top' := begin
    suffices : ∃ (rs : Q), rs ∉ (α : set Q) + β,
    { contrapose! this, simp [this] },
    obtain ⟨r', hr'⟩ := α.exists_not_mem,
    obtain ⟨s', hs'⟩ := β.exists_not_mem,
    refine ⟨r' + s', _⟩,
    rintro ⟨r, s, hr, hs, h⟩,
    have : r + s < r' + s' :=
      add_lt_add (lt_of_mem_of_not_mem hr hr') (lt_of_mem_of_not_mem hs hs'),
    exact absurd h this.ne
  end,
  is_lt_lower' := begin
    rintro p q h ⟨r, s, hr, hs, rfl⟩,
    refine ⟨q - s, s, is_lt_lower _ _ hr, hs, sub_add_cancel _ _⟩,
    rwa sub_lt_iff_lt_add
  end,
  exists_gt' := begin
    rintros p ⟨r, s, hr, hs, rfl⟩,
    obtain ⟨t, ht, hrt⟩ := α.exists_gt hr,
    exact ⟨t + s, ⟨t, s, ht, hs, rfl⟩, add_lt_add_right hrt _⟩
  end }⟩

lemma mem_add_iff {Q : Type*} [linear_order Q] [add_group Q] [covariant_class Q Q (+) (<)]
  [covariant_class Q Q (function.swap (+)) (<)] {α β : dedekind_cut Q} {p : Q} :
  p ∈ α + β ↔ ∃ (r s : Q), r ∈ α ∧ s ∈ β ∧ r + s = p := iff.rfl

-- Step 4 (A2)
protected lemma add_comm {Q : Type*} [linear_order Q] [add_comm_group Q]
  [covariant_class Q Q (+) (<)] (α β : dedekind_cut Q) : α + β = β + α :=
begin
  ext,
  simp only [mem_add_iff, and.comm, and.left_comm, mem_carrier],
  split;
  { rintro ⟨r, s, rfl, hr, hs⟩,
    exact ⟨s, r, add_comm _ _, hs, hr⟩ }
end

-- Step 4 (A3)
protected lemma add_assoc {Q : Type*} [linear_order Q] [add_group Q] [covariant_class Q Q (+) (<)]
  [covariant_class Q Q (function.swap (+)) (<)] (α β γ : dedekind_cut Q) :
  α + β + γ = α + (β + γ) :=
begin
  ext,
  simp only [mem_carrier, mem_add_iff, and.comm, and.assoc, and.left_comm],
  split,
  { rintro ⟨_, r, rfl, hr, s, t, rfl, hs, ht⟩,
    refine ⟨_, _, _, hs, _, _, rfl, ht, hr⟩,
    rw add_assoc },
  { rintro ⟨_, r, rfl, hr, s, t, rfl, hs, ht⟩,
    refine ⟨_, _, _, ht, _, _, rfl, hr, hs⟩,
    rw add_assoc }
end

end dedekind_cut

end

namespace dedekind_cut

variables {Q : Type*} [linear_ordered_field Q]

section

variables {α β : dedekind_cut Q} {p q : Q}

instance : covariant_class (dedekind_cut Q) (dedekind_cut Q) (+) (≤) :=
⟨λ α β γ h, begin
  intro p,
  simp_rw mem_add_iff,
  rintro ⟨r, s, hr, hs, rfl⟩,
  exact ⟨r, s, hr, h hs, rfl⟩
end⟩

-- Step 4, construction
instance : has_coe_t Q (dedekind_cut Q) :=
⟨λ p, { carrier := set_of (< p),
   nonempty' := ⟨p - 1, by simp⟩,
   ne_top' := begin
     have : (p : Q) ∉ set_of (< (p : Q)) := by simp,
     contrapose! this,
     simp [this]
   end,
   is_lt_lower' := λ _ _, lt_trans,
   exists_gt' := λ q hq, begin
    simp only [set.mem_set_of_eq] at hq ⊢,
    refine ⟨(p + q) / 2, _, _⟩,
    { rwa [div_lt_iff, mul_two, add_lt_add_iff_left],
      exact zero_lt_two },
    { rwa [lt_div_iff, mul_two, add_lt_add_iff_right],
      exact zero_lt_two }
   end }⟩

@[simp] lemma mem_coe_iff : p ∈ (q : dedekind_cut Q) ↔ p < q := iff.rfl

instance : has_zero (dedekind_cut Q) := ⟨(0 : Q)⟩

instance : inhabited (dedekind_cut Q) := ⟨0⟩

@[simp] lemma mem_zero_iff : p ∈ (0 : dedekind_cut Q) ↔ p < 0 := iff.rfl

-- Step 4 (A4)
protected lemma add_zero (α : dedekind_cut Q) : α + 0 = α :=
begin
  refine le_antisymm (λ p hp, _) (λ p hp, _),
  { simp only [mem_add_iff, mem_zero_iff, exists_and_distrib_left] at hp,
    obtain ⟨r, hr, s, hs, rfl⟩ := hp,
    exact α.is_lt_lower (add_lt_iff_neg_left.mpr hs) hr },
  { obtain ⟨r, hr, hpr⟩ := α.exists_gt hp,
    simp only [mem_add_iff, mem_zero_iff, exists_and_distrib_left],
    exact ⟨r, hr, p - r, sub_neg.mpr hpr, add_sub_cancel'_right _ _⟩ }
end

-- Step 4 (A5) construction
instance : has_neg (dedekind_cut Q) :=
⟨λ α, { carrier := {p | ∃ (r : Q) (hr : 0 < r), - p - r ∉ α},
  nonempty' := begin
    obtain ⟨s, hs⟩ := α.exists_not_mem,
    refine ⟨- s - 1, _⟩,
    simp only [exists_prop, set.mem_set_of_eq, neg_sub, sub_neg_eq_add],
    exact ⟨1, by simpa using hs⟩
  end,
  ne_top' := begin
    obtain ⟨q, hq⟩ := α.nonempty,
    suffices : - q ∉ {p : Q | ∃ (r : Q) (hr : 0 < r), -p - r ∉ α},
    { contrapose! this,
      simp only [this, set.top_eq_univ] },
    rintro ⟨r, hr, hr'⟩,
    refine hr' (α.is_lt_lower _ hq),
    simpa using hr
  end,
  is_lt_lower' := begin
    rintro p q h ⟨r, hr, hp⟩,
    refine ⟨r, hr, λ H, hp (α.is_lt_lower _ H)⟩,
    simpa using h
  end,
  exists_gt' := begin
    rintro p ⟨r, hr, hr'⟩,
    refine ⟨p + r / 2, ⟨r / 2, _, _⟩, _⟩,
    { simp [div_pos_iff, hr] },
    { rwa [neg_add, add_sub_assoc, ←sub_eq_neg_add, ←neg_add', ←mul_two, div_mul_cancel, ←neg_add',
           add_comm, neg_add'],
      exact zero_lt_two.ne' },
    { simp [div_pos_iff, hr] }
  end }⟩

@[simp] lemma mem_neg_iff : p ∈ - α ↔ ∃ (r : Q) (hr : 0 < r), - p - r ∉ α := iff.rfl

lemma mem_neg_imp_neg_not_mem (hp : p ∈ - α) : - p ∉ α :=
begin
  obtain ⟨r, rpos, hr⟩ := hp,
  contrapose! hr,
  refine α.is_lt_lower _ hr,
  simpa using rpos
end

end

variables [archimedean Q]

-- Step 4 (A5)
protected lemma add_left_neg (α : dedekind_cut Q) : - α + α = 0 :=
begin
  refine le_antisymm (λ p hp, _) (λ v hv, _),
  { rw mem_add_iff at hp,
    obtain ⟨s, r, hs, hr, rfl⟩ := hp,
    rw [mem_zero_iff, add_comm, ←neg_neg s, ←sub_eq_add_neg, sub_lt_zero],
    exact lt_of_mem_of_not_mem hr (mem_neg_imp_neg_not_mem hs) },
  { set w : Q := - v / 2 with hw,
    have wpos : 0 < w,
    { rw [mem_zero_iff] at hv,
      simp [hw, div_pos_iff, hv] },
    obtain ⟨n, hn, hn'⟩ : ∃ (n : ℤ), n • w ∈ α ∧ (n + 1) • w ∉ α,
    { obtain ⟨q, hq⟩ := α.exists_not_mem,
      have := archimedean.arch q wpos,
      contrapose! this,
      obtain ⟨z, hz⟩ : ∃ (z : ℤ), z • w ∈ α,
      { obtain ⟨r, hr⟩ := α.nonempty,
        obtain ⟨z, hz, hz'⟩ := exists_unique_zsmul_near_of_pos wpos r,
        exact ⟨z, α.is_lower_set hz.left hr⟩ },
      replace this : ∀ (n : ℤ), n • w ∈ α,
      { intros n,
        induction hn : n - z using int.induction_on with k IH k IH generalizing n,
        { rw sub_eq_zero at hn,
          subst hn,
          exact hz },
        { specialize this _ (IH (n - 1) _),
          { rw [sub_sub, add_comm, ←sub_sub, hn, add_sub_cancel] },
          { rwa sub_add_cancel at this } },
        { rw [sub_eq_iff_eq_add, add_comm] at hn,
          subst hn,
          refine α.is_lower_set _ hz,
          simp only [mul_le_mul_right wpos, zsmul_eq_mul, int.cast_add, int.cast_sub, int.cast_neg,
                     int.cast_coe_nat, int.cast_one, add_le_iff_nonpos_right, sub_nonpos, neg_le],
          suffices : (-1 : ℤ) ≤ k,
          { exact_mod_cast this },
          refine le_trans _ (int.coe_nat_nonneg k),
          simp } },
      obtain ⟨k, hk⟩ : ∃ (n : ℤ), (q / w) < n := exists_int_gt _,
      rw [div_lt_iff wpos, ←zsmul_eq_mul] at hk,
      exact absurd (α.is_lt_lower hk (this _)) hq },
    rw mem_add_iff,
    refine ⟨- (n + 2) • w, n • w, _, hn, _⟩,
    { rw mem_neg_iff,
      refine ⟨w, wpos, _⟩,
      convert hn',
      simp [add_mul, add_sub_assoc, two_mul, -add_halves'] },
    { rw ←add_zsmul,
      simp [two_mul] } }
end

instance : add_comm_group (dedekind_cut Q) :=
{ add := (+),
  add_assoc := dedekind_cut.add_assoc,
  zero := 0,
  zero_add := by simpa [dedekind_cut.add_comm] using dedekind_cut.add_zero,
  add_zero := dedekind_cut.add_zero,
  neg := has_neg.neg,
  add_left_neg := begin
    intros α,
    convert dedekind_cut.add_left_neg α,
  end,
  add_comm := dedekind_cut.add_comm }

-- Step 5
instance : covariant_class (dedekind_cut Q) (dedekind_cut Q) (+) (<) :=
⟨λ α β γ h, begin
  refine lt_of_le_of_ne (add_le_add_left h.le _) (λ H, h.ne _),
  rwa add_right_inj at H
end⟩

end dedekind_cut
