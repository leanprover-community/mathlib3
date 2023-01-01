/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.measure.lebesgue
import analysis.calculus.monotone
import data.set.function
import topology.instances.ennreal
import topology.metric_space.list_edist

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


open emetric nnreal set ennreal measure_theory
open_locale big_operators nnreal ennreal

variables {α β : Type*} {E F : Type*} [pseudo_emetric_space E] [pseudo_emetric_space F]
variables (f : α → E)
variables [linear_order α] [linear_order β]
variables (s t : set α)


noncomputable def evariation_on :=
⨆ l ∈ {l : list α | l.pairwise (≤) ∧ ∀ ⦃x⦄, x ∈ l → x ∈ s}, (l.map f).edist

lemma map_edist_le_evariation_on {l : list α} (hl :  l.pairwise (≤) ∧ ∀ ⦃x⦄, x ∈ l → x ∈ s) :
  (l.map f).edist ≤ evariation_on f s := le_supr₂ l hl

def has_bounded_variation_on := evariation_on f s ≠ ∞

def has_locally_bounded_variation_on :=
∀ a b, a ∈ s → b ∈ s → has_bounded_variation_on f (s ∩ Icc a b)

namespace evariation_on

open function

variables {f} {s} {t}

def sorted_list_nonempty : set.nonempty {l : list α | l.pairwise (≤) ∧ ∀⦃x⦄, x∈l → x∈s} :=
  ⟨[], list.pairwise.nil, λ x h, (list.not_mem_nil _ h).elim⟩

lemma eps_approx (h : evariation_on f s ≠ ⊤) (ε : ennreal) (hε : ε ≠ 0) :
  ∃ ll : {l : list α | l.pairwise (≤) ∧ ∀ ⦃x⦄, x ∈ l → x ∈ s},
    evariation_on f s < (ll.val.map f).edist + ε  :=
begin
  by_contra' hn,
  apply (ennreal.lt_add_right h hε).not_le,
  dsimp only [evariation_on],
  rw [bsupr_add (sorted_list_nonempty), supr₂_le_iff],
  rw [set_coe.forall] at hn, exact hn,
end

lemma eq_of_eq_on {f f' : α → E} {s : set α} (h : set.eq_on f f' s) :
  evariation_on f s = evariation_on f' s :=
begin
  dsimp only [evariation_on],
  congr' 1 with l : 1,
  congr' 1 with hl : 1,
  simp only [list.map_congr (λ x xl, h (hl.2 xl))],
end

lemma mono (hst : t ⊆ s) : evariation_on f t ≤ evariation_on f s :=
supr₂_le $ λ l lp, map_edist_le_evariation_on f s ⟨lp.left, λ x xl, hst (lp.right xl)⟩

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
  refine le_of_eq (list.edist_const (λ x hx y hy, _)),
  simp only [list.mem_map] at hx hy,
  exact hf ⟨_, ls hx.some_spec.1, hx.some_spec.2⟩ ⟨_, ls hy.some_spec.1, hy.some_spec.2⟩,
end

@[simp] protected lemma subsingleton (f : α → E) {s : set α} (hs : s.subsingleton) :
  evariation_on f s = 0 := constant_on (hs.image f)

lemma edist_le {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
  edist (f x) (f y) ≤ evariation_on f s :=
begin
  wlog hxy : x ≤ y := le_total x y using [x y, y x] tactic.skip, swap,
  { rw edist_comm,
    exact λ hy hx, this hx hy, },
  rw [←list.edist_pair],
  have : [f x, f y] = [x, y].map f, by simp, rw this,
  apply map_edist_le_evariation_on f,
  simp only [hxy, hx, hy, list.pairwise_cons, list.not_mem_nil, is_empty.forall_iff,
             implies_true_iff, list.pairwise.nil, and_self, list.mem_cons_iff, forall_eq_or_imp],
end

lemma _root_.has_bounded_variation_on.dist_le {E : Type*} [pseudo_metric_space E]
  {f : α → E} {s : set α} (h : has_bounded_variation_on f s) {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
  dist (f x) (f y) ≤ (evariation_on f s).to_real :=
begin
  rw [←ennreal.of_real_le_of_real_iff ennreal.to_real_nonneg, ennreal.of_real_to_real h,
      ←edist_dist],
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
  apply ennreal.bsupr_add_bsupr_le sorted_list_nonempty sorted_list_nonempty,
  rintro ll ⟨llm,lls⟩ lr ⟨lrm,lrt⟩,
  apply (list.edist_append _ _).trans,
  rw ←list.map_append,
  apply map_edist_le_evariation_on f,
  simp only [list.pairwise_append, list.mem_append, mem_union],
  split,
  { exact ⟨llm, lrm, λ x xl y yr, h x (lls xl) y (lrt yr)⟩,  },
  { rintro x (xl|xr), exact or.inl (lls xl), exact or.inr (lrt xr), },
end

--mathlib
lemma list.not_le_of_mem_drop_while_le_of_pairwise_le {α : Type*} {x:α}
  [preorder α] [decidable_pred (≤x)] :
  ∀ {l : list α} (h : l.pairwise (≤)) ⦃y : α⦄, y ∈ l.drop_while (≤x) → ¬y ≤ x
| [] h y hy := by { simpa only [list.drop_while, list.not_mem_nil] using hy, }
| (a::l) h y hy := by
  { dsimp only [list.drop_while] at hy,
    simp only [list.pairwise_cons] at h,
    split_ifs at hy with ax nax,
    { exact list.not_le_of_mem_drop_while_le_of_pairwise_le h.right hy, },
    { cases hy,
      { cases hy, exact ax },
      { exact λ yx, ax ((h.left y hy).trans yx), }, }, }

lemma union {x : α} (hs : is_greatest s x) (ht : is_least t x) :
  evariation_on f (s ∪ t) = evariation_on f s + evariation_on f t :=
begin
  apply le_antisymm _ (add_le_union (λ u us v vt, (hs.2 us).trans (ht.2 vt))),
  apply supr₂_le _,
  rintro l ⟨lm,lst⟩,
  rw [←list.take_while_append_drop (≤x) l, list.map_append],
  apply (list.edist_le_append_singleton_append _ (f x) _).trans,
  rw list.edist_append_singleton_append,
  refine add_le_add _ _;
  rw [(by simp : [f x] = [x].map f), ←list.map_append];
  apply map_edist_le_evariation_on,
  { split,
    { simp only [list.pairwise_append, list.pairwise_cons, list.not_mem_nil, is_empty.forall_iff,
                 implies_true_iff, list.pairwise.nil, list.mem_singleton, forall_eq, true_and],
      refine ⟨ list.pairwise.sublist (list.take_while_prefix (≤x)).sublist lm, _⟩,
      apply list.mem_take_while_imp, },
    { simp only [list.mem_append, list.mem_singleton],
      rintro u (ul|rfl),
      { let := list.mem_take_while_imp ul,
        specialize lst ((list.take_while_prefix (≤x)).subset ul),
        change u ∈ s ∨ u ∈ t at lst, cases lst,
        { assumption, },
        { cases le_antisymm this (ht.right lst), exact hs.left, }, },
      { exact hs.left, }, } },
  { split,
    { simp only [list.singleton_append, list.pairwise_cons],
      exact ⟨ λ u ul, (lt_of_not_le (list.not_le_of_mem_drop_while_le_of_pairwise_le lm ul)).le,
              list.pairwise.sublist (list.drop_while_suffix (≤x)).sublist lm⟩, },
    { simp only [list.singleton_append, list.mem_cons_iff, forall_eq_or_imp],
      refine ⟨ht.left, λ u ul, _⟩,
      specialize lst ((list.drop_while_suffix (≤x)).subset ul),
      change u ∈ s ∨ u ∈ t at lst, cases lst,
      { exact ((list.not_le_of_mem_drop_while_le_of_pairwise_le lm ul) (hs.right lst)).elim, },
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

--mathlib?
lemma list.forall_mem.map {α β : Type*}
  {l : list α} (φ : α → β) {s : set α} {t : set β} (φst : s.maps_to φ t)
  (ls : ∀ ⦃x⦄, x ∈ l → x ∈ s) : ∀ ⦃x⦄, x ∈ l.map φ → x ∈ t :=
begin
  simp only [list.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂],
  exact λ x xφl, φst (ls xφl),
end

--mathlib?
lemma list.pairwise.map_of_maps_to_of_forall {α β : Type*} [preorder α] [preorder β]
  {l : list α} (φ : α → β) {s : set α} (φm : monotone_on φ s)
  (ls : ∀ ⦃x⦄, x ∈ l → x ∈ s) (lm : l.pairwise (≤)) : (l.map φ).pairwise (≤) :=
begin
  induction l,
  { simp only [list.map_nil, list.pairwise.nil], },
  { simp only [list.pairwise_cons] at lm,
    constructor,
    { rintro a aφl, simp only [list.mem_map] at aφl, obtain ⟨x,xl,rfl⟩ := aφl,
      exact φm (ls (or.inl rfl)) (ls (or.inr xl)) (lm.1 _ xl), },
    { apply l_ih (λ x xh, ls (or.inr xh)) lm.2  }, },
end

--mathlib?
lemma list.pairwise.map_of_maps_to_of_forall' {α β : Type*} [preorder α] [preorder β]
  {l : list α} (φ : α → β) {s : set α} (φm : antitone_on φ s)
  (ls : ∀ ⦃x⦄, x ∈ l → x ∈ s) (lm : l.pairwise (≥)) : (l.map φ).pairwise (≤) :=
begin
  induction l,
  { simp only [list.map_nil, list.pairwise.nil], },
  { simp only [list.pairwise_cons] at lm,
    constructor,
    { rintro a aφl, simp only [list.mem_map] at aφl, obtain ⟨x,xl,rfl⟩ := aφl,
      exact φm (ls (or.inr xl)) (ls (or.inl rfl)) (lm.1 _ xl), },
    { apply l_ih (λ x xh, ls (or.inr xh)) lm.2  }, },
end

lemma comp_le_of_monotone_on {φ : β → α} {t :set β}
  (mφ : monotone_on φ t) (φst : t.maps_to φ s) : evariation_on (f ∘ φ) t ≤ evariation_on f s :=
begin
  simp only [evariation_on, supr₂_le_iff, ←list.map_comp_map f φ],
  exact λ l ls, map_edist_le_evariation_on _ _
    ⟨list.pairwise.map_of_maps_to_of_forall φ mφ ls.2 ls.1, list.forall_mem.map φ φst ls.2⟩,
end

lemma comp_le_of_antitone_on {φ : β → α} {t :set β}
  (mφ : antitone_on φ t) (φst : t.maps_to φ s) :
  evariation_on (f ∘ φ) t ≤ evariation_on f s :=
begin
  simp only [evariation_on, supr₂_le_iff, ←list.map_comp_map f φ],
  rintro l ⟨lm,ls⟩,
  rw [←list.edist_reverse, ←list.map_reverse],
  apply map_edist_le_evariation_on f,
  split,
  { rw ←list.map_reverse,
    apply list.pairwise.map_of_maps_to_of_forall' φ mφ,
    simp only [list.mem_reverse], exact ls,
    simp only [list.pairwise_reverse, ge_iff_le], exact lm, },
  { simp only [list.mem_reverse, list.mem_map, forall_exists_index, and_imp,
               forall_apply_eq_imp_iff₂],
    rintro a al, apply φst (ls al), },
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

theorem list.pairwise.map_on {γ δ : Type*} {R : γ → γ → Prop} {l : list γ} {S : δ → δ → Prop}
  (f : γ → δ) (H : ∀ ⦃a b : γ⦄, a ∈ l → b ∈ l → R a b → S (f a) (f b))
  (p : list.pairwise R l) : (l.map f).pairwise S := sorry

lemma monotone_on.evariation_on_le {f : α → ℝ} {s : set α} (hf : monotone_on f s) {a b : α}
  (as : a ∈ s) (bs : b ∈ s) :
  evariation_on f (s ∩ Icc a b) ≤ ennreal.of_real (f b - f a) :=
begin
  apply supr₂_le _,
  rintro l ⟨lm,ls⟩,
  by_cases ab : a ≤ b,
  { have : edist (f a) (f b) = ennreal.of_real (f b - f a), by sorry, rw ←this,
    apply list.edist_of_monotone_le_real,
    exact list.pairwise.map_on f (λ a b al bl ab, hf (ls al).1 (ls bl).1 ab) lm,
    simp only [list.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂],
    exact λ x xl, ⟨hf as (ls xl).1 (ls xl).2.1, hf (ls xl).1 bs (ls xl).2.2⟩, },
  { sorry, /- ¬ a ≤ b means the interval is empty and everything is zero, -/ },
end

lemma monotone_on.has_locally_bounded_variation_on {f : α → ℝ} {s : set α} (hf : monotone_on f s) :
  has_locally_bounded_variation_on f s :=
λ a b as bs, ((hf.evariation_on_le as bs).trans_lt ennreal.of_real_lt_top).ne

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

lemma lipschitz_on_with.comp_evariation_on_le {f : E → F} {C : ℝ≥0} {t : set E}
  (h : lipschitz_on_with C f t) {g : α → E} {s : set α} (hg : maps_to g s t) :
  evariation_on (f ∘ g) s ≤ C * (evariation_on g s) :=
begin
  apply supr₂_le _,
  rintro l hl,
  rw ←list.map_comp_map,
  transitivity' ↑C * (l.map g).edist,
  { apply list.edist_map_of_lipschitz_on h,
    rintro x xl, simp only [list.mem_map] at xl, obtain ⟨y,yl,rfl⟩ := xl, exact hg (hl.right yl), },
  { exact mul_le_mul_left' (map_edist_le_evariation_on g s hl) (↑C), },
end

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
