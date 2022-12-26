/-
Copyright (c) 2022 Pedro Sánchez Terraf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pedro Sánchez Terraf
-/
import set_theory.cardinal.continuum
import measure_theory.measurable_space_def
import set_theory.cardinal.cofinality
import tactic.induction

/-!
# The Borel hierarchy

In this file we define recursively define the classical Borel hierarchy of sets.
It is developed as a purely set-theoretic definition here.

## Mathematical overview

For a second countable topological space $X$, the Borel hierarchy is defined
recursively as follows (viz., Sect. 11.B in [kechris1995]):
$$
\begin{align}
  \mathbf{\Sigma}^0_1(X)     &= \{U \subseteq X: U \text { is open }\} \\
  \mathbf{\Pi}^0_{\xi}(X)    &= \{ X \setminus Q : Q \in \mathbf{\Sigma}^0_{\xi}(X)\} \\
  \mathbf{\Sigma}^0_{\xi}(X) &= \left\{\textstyle\bigcup_n A_n: A_n \in
    \mathbf{\Pi}^0_{\xi_n}(X), \xi_n<\xi, n \in \mathbb{N}\right\}, \text { if } \xi>1,
\end{align}
$$
where $\xi$ and $\xi_n$ are ordinals between $1$ and $\omega_1$.

This is a streamlined version of the notation for classes of *definable* subsets
of the space $X$ (aka, **pointclasses**): $\mathbf{\Pi}^0_1(X)$ are the closed sets; $\mathbf{\Sigma}^0_2(X)$
are the $F_\sigma$ sets; $\mathbf{\Pi}^0_2(X)$, the $G_\delta$; and so forth.
This is specially useful for infinite indices $\xi$.

In this file, we provide an inductive definition of the above hierarchy of subsets
of an arbitrary type, without assuming a topology but using an extra paramater `s`
which is intended to be a countable base of a topology.

## Main definitions

- `sigma0_pi0_rec`: Recursive definition of the hierarchy, not intended for direct use.
- `sigma0`, `pi0` : The classical pointclasses, obtained from `sigma0_pi0_rec`
using its `bool` argument.

## Implementation notes

Traditionally, pointclasses $\Sigma^0_\alpha$ and $\Pi^0_\alpha$ are defined for positive
values of the ordinal $\alpha$. Here the definition is extended in such a way that
$\Sigma^0_0 = \emptyset$ (which results in more generality for some lemmas) and
$\Pi^0_0$ coincides with the set of generators.

The `inductive` definition of `sigma0_pi0_rec` was suggested by Junyan Xu.

## References

The definition of the hierarchy was extracted from [kechris1995].
-/

universe u

namespace pointclasses

section sigma0_pi0

/-!
### Σ and Π pointclasses

This section includes basic definitions and API.
-/
open set

variables {α : Type u} (s : set (set α)) (i k : ordinal.{u})

/--
Simultaneous recursive definition of Σ⁰ᵢ and Π⁰ᵢ pointclasses by recursion
on ordinals (a variant of 11.B in Kechris, [Classical Descriptive Set Theory][kechris1995]).

The definition is encoded as a single inductive predicate, where the `bool` argument
determines if we are defining Σ⁰ᵢ (for `ff`) or Π⁰ᵢ (for `tt`). The parameter
`s : set (set α)` is the generating family.

The main difference is that the hierarchy starts at level 0: Π⁰₀ coincides with `s`
augmented with `∅` and `univ` (intended to be a countable basis of a topology) and
Σ⁰₀ is the empty family.
-/
inductive sigma0_pi0_rec {α : Type u} (s : set (set α)) :
  ordinal.{u} → bool → set α → Prop
| basic (x ∈ s) : sigma0_pi0_rec 0 tt x
| empty         : sigma0_pi0_rec 0 tt ∅
| univ          : sigma0_pi0_rec 0 tt univ
| compl {i x}   : sigma0_pi0_rec i ff x → sigma0_pi0_rec i tt xᶜ
| union {i} (f : ℕ → set α) (g : ℕ → ordinal.{u}) :
    (∀ n, g n < i) → (∀ n, sigma0_pi0_rec (g n) tt (f n)) → sigma0_pi0_rec i ff (⋃ n, f n)

/--
The family of (boldface) Σ⁰ᵢ pointsets, which are countable unions of Π⁰ⱼ sets
(given by the function `pointclasses.pi0` below) of smaller index. The parameter
`s : set (set α)` is the family of sets from which the generation begins.
-/
def sigma0 : set (set α) := sigma0_pi0_rec s i ff

/--
The family of (boldface) Π⁰ᵢ pointsets, which are the complements of Π⁰ᵢ sets
(given by the function `pointclasses.sigma0` above). The parameter
`s : set (set α)` is the family of sets from which the generation begins.

When the ordinal argument is `0`, `pi0` returns the generating family `s`.
-/
def pi0 : set (set α) := sigma0_pi0_rec s i tt

lemma sigma0_pi0_rec_def' {b : bool} :
  sigma0_pi0_rec s i b = if b then pi0 s i else sigma0 s i :=
by { unfold pi0 sigma0, cases b; refl }

@[simp] lemma sigma0_zero : sigma0 s 0 = ∅ :=
begin
  unfold sigma0,
  ext x, rw [mem_empty_iff_false, iff_false],
  intro hx,
  induction' hx with _ _ _ _ _ _ _ f g glt hf IH,
  exact ordinal.not_lt_zero (g 0) (glt 0)
 end

lemma sigma0_eq_Union_pi0:
  sigma0 s i = set.range (λ (f : ℕ → ⋃ j (hij : j < i), pi0 s j), ⋃ n, (f n).1) :=
begin
  rcases classical.em (i=0) with rfl | hi; unfold sigma0, rw sigma0_pi0_rec_def',
  { apply eq.symm, simp [range_eq_empty, ordinal.not_lt_zero] },
  { ext x, split; intro hx,
    { induction' hx with _ _ _ _ _ _ i f g glt hf,
      existsi λn, (⟨f n, _⟩ : ↥⋃ j < i, pi0 s j),
      { simp only [eq_self_iff_true] },
      { rw mem_Union,
      use g n,
      rw mem_Union,
      exact ⟨glt n, hf n⟩ } },
    { cases hx with f hf,
      rw ← hf,
      dsimp only at hf,
      choose g hg using λn, (mem_Union.mp (f n).property),
      simp only [mem_Union,exists_prop] at hg,
      apply sigma0_pi0_rec.union _ g,
      exact λ n, (hg n).1,
      unfold pi0 at hg,
      exact λ n, (hg n).2 } }
end

lemma pi0_subset_sigma0 (hik : i < k) :
  pi0 s i ⊆ sigma0 s k :=
begin
  simp only [sigma0_eq_Union_pi0,hik],
  intros x hx,
  apply mem_range.mpr,
  have hxU : x ∈ ⋃ j < k, pi0 s j,
  { simp only [mem_Union,exists_prop],
    use i,
    exact ⟨hik,hx⟩ },
  existsi (λn : ℕ, (⟨x,hxU⟩ : ⋃ (j < k), pi0 s j)),
  exact Union_const x
end

lemma pi0_eq_compl_sigma0 (hi : ¬i = 0):
  pi0 s i = compl '' sigma0 s i :=
begin
  unfold sigma0 pi0,
  ext x, split; intro hx; induction' hx with hcomp IH c d IH,
  any_goals { contradiction },
  { simp only [mem_image], use d, tauto },
  { have := sigma0_pi0_rec.compl IH.1, rwa ← IH.2 }
end

lemma pi0_zero :
  pi0 s 0 = s ∪ {∅,univ} :=
begin
  unfold pi0, ext,
  simp only [mem_insert_iff,union_insert,union_singleton],
  split; intro hx,
  { induction' hx with _ hx _ v hv,
    any_goals { tauto },
    simp only [sigma0_pi0_rec_def'] at hv,
    have : sigma0 s 0 v,
    { exact hv },
    exfalso,
    rw sigma0_zero at this,
    exact this },
  { rcases hx with rfl | rfl | x_in_s,
    exacts [sigma0_pi0_rec.empty, sigma0_pi0_rec.univ, sigma0_pi0_rec.basic x x_in_s] }
end

lemma sigma0_one :
  sigma0 s 1 = set.range (λ (f : ℕ → s ∪ {∅,univ}), ⋃ n, (f n).1) :=
begin
  unfold sigma0,
  change sigma0_pi0_rec s 1 ff = range (λ (f : ℕ → ↥(s ∪ {∅, univ})), ⋃ (n : ℕ), ↑(f n)),
  ext z,
  change sigma0_pi0_rec s 1 ff z ↔ ∃ (y : ℕ → ↥(s ∪ {∅, univ})), (⋃ (n : ℕ), ↑(y n)) = z,
  refine ⟨λ h, _, λ h, _⟩,
  { -- Subgoal solved by Junyan Xu.
    induction' h with _ _ _ _ _ _ _ f g glt1 IH f_Union,
    simp_rw ordinal.lt_one_iff_zero at glt1,
    simp_rw glt1 at IH,
    change ∀ n, f n ∈ pi0 s 0 at IH,
    simp_rw pi0_zero at IH,
    use λ n, ⟨f n, IH n⟩,
    exact rfl },
  { rcases h with ⟨f,rfl⟩,
    apply sigma0_pi0_rec.union (λ n, (f n).val) (λ n, 0),
    { simp },
    { change ∀ (n : ℕ), sigma0_pi0_rec s 0 tt ↑(f n),
      intro n,
      have hfn := (f n).property,
      simp only [subtype.val_eq_coe,mem_insert_iff,union_insert,union_singleton] at hfn,
      rcases hfn with nul | uni | bas,
      { rw nul, exact sigma0_pi0_rec.empty },
      { rw uni, exact sigma0_pi0_rec.univ },
      { exact sigma0_pi0_rec.basic (f n) bas } } }
end

lemma sigma0_subset_sigma0 (hik : i ≤ k) :
  sigma0 s i ⊆ sigma0 s k :=
begin
  rw le_iff_lt_or_eq at hik,
  cases hik,
  -- Take care of the trivial case `i = k` first,
  swap,
  { simp only [hik, subset_rfl] },
  -- Now the interesting `i < k`:
  repeat { rw sigma0_eq_Union_pi0 },
  intros x hx,
  cases hx with f hf,
  simp only at hf,
  have hfUn : ∀ (n : ℕ), ↑(f n) ∈ (⋃ j < k, pi0 s j),
  { intro n,
    apply mem_Union.mpr,
    -- Awful proof ahead :(
    have : ∃ j (hjk : j < k), (f n).val ∈ pi0 s j :=
      (let (Exists.intro j q) := (mem_Union.mp (f n).property) in
        let (Exists.intro l r) := mem_Union.mp q in
        Exists.intro j (Exists.intro (trans l hik) r)),
    cases this with j hj,
    use j,
    exact mem_Union.mpr hj },
  apply mem_range.mpr,
  existsi (λn : ℕ, (⟨f n, hfUn n⟩ : ⋃ j < k, (pi0 s j))),
  tauto,
end

/--
The sequence of `pi0` families is nondecreasing.

The hypothesis `¬i = 0` is required in case elements of the generating set are
not closed. If the underlying space is zero-dimensional, one can take a basis
of clopen sets and the inclusion will hold unconditionally.
-/
lemma pi0_subset_pi0 (hi : ¬i = 0) (hik : i ≤ k) :
  pi0 s i ⊆ pi0 s k :=
begin
  rw [pi0_eq_compl_sigma0,pi0_eq_compl_sigma0],
  exacts [image_subset _ (sigma0_subset_sigma0 s i k hik),
    ordinal.one_le_iff_ne_zero.mp (trans (ordinal.one_le_iff_ne_zero.mpr hi) hik),
    hi]
end

lemma Union_of_sigma0_sequence {g : ℕ → sigma0 s i} :
  (⋃ n, (g n).val) ∈ sigma0 s i :=
begin
  have hg : ∀ n : ℕ, (g n).val ∈ sigma0 s i := λ n, (g n).property,
  simp only [subtype.val_eq_coe,sigma0_eq_Union_pi0] at *,
  choose o ho using hg,
  have : ℕ × ℕ ≃ ℕ,
  { exact denumerable.eqv (ℕ × ℕ) },
  cases this with tup untup htup huntup,
  use λ n, let p := (untup n) in o p.1 p.2,
  ext x, split; intro hx; simp only [mem_Union] at hx ⊢;
  cases hx with j hxin,
  { let n := (untup j).fst,
    use n,
    specialize ho n,
    rw [← ho, mem_Union],
    use (untup j).snd,
    assumption },
  { simp only [mem_Union,← ho j] at hxin,
    cases hxin with k hk,
    existsi tup ⟨j,k⟩,
    have fstj : (untup (tup ⟨j,k⟩)).fst = j,
    { exact (congr_arg prod.fst (htup (j, k))).trans rfl },
    have sndk : (untup (tup ⟨j,k⟩)).snd = k,
    { exact (congr_arg prod.snd (htup (j, k))).trans rfl },
    rw [fstj,sndk],
    exact hk }
end

lemma Union_of_mem_sigma0 {f : ℕ → set α} (hf : ∀ n, f n ∈ sigma0 s i):
  (⋃ n, f n) ∈ sigma0 s i :=
by exact @Union_of_sigma0_sequence _ s i (λn, {val := f n, property := hf n} : ℕ → sigma0 s i)

lemma self_subset_sigma0 (hi : ¬i = 0) :
  s ⊆ sigma0 s i :=
begin
  calc
  s   ⊆ s ∪ {∅,univ} : subset_union_left _ _
  ... = pi0 s 0      : eq.symm (pi0_zero s)
  ... ⊆ sigma0 s i   : pi0_subset_sigma0 s 0 i (ordinal.pos_iff_ne_zero.mpr hi),
end

theorem empty_mem_sigma0 (hi : ¬i = 0) :
  ∅ ∈ sigma0 s i :=
begin
  have : ∅ ∈ s ∪ {∅,univ} := by { apply mem_union_right, simp },
  have that : s ∪ {∅,univ} = pi0 s 0 := eq.symm (pi0_zero s),
  rw that at this,
  calc
  ∅   ∈ pi0 s 0      : this
  ... ⊆ sigma0 s i   : pi0_subset_sigma0 s 0 i (ordinal.pos_iff_ne_zero.mpr hi)
end

end sigma0_pi0

section gen_measurable
/-!
### Generated σ-algebra by recursion
-/
variables {α : Type u} (s : set (set α)) (i k : ordinal.{u})

open set ordinal cardinal
open_locale ordinal

/--
The σ-algebra recursively generated by the family `s`. It is obtained at the
`ω₁`th level of the `sigma0` hierarchy.
-/
def gen_measurable := sigma0 s ω₁

lemma gen_measurable_eq_Union_sigma0 :
  gen_measurable s = ⋃ (j < ω₁), sigma0 s j :=
begin
  unfold gen_measurable,
  apply subset_antisymm,
  { rw sigma0_eq_Union_pi0,
    intros x hx,
    simp only [mem_Union,exists_prop] at *,
    cases hx with f hf,
    let g := λ n, (f n).property,
    simp only [mem_Union,exists_prop] at g,
    choose o ho using g,
    use order.succ(sup o),
    split,
    { exact is_limit.succ_lt is_limit_omega_1 (sup_sequence_lt_omega_1 o (λ n, (ho n).left)) },
    rw sigma0_eq_Union_pi0,
    rw mem_range,
    have typf : ∀ n, ↑(f n) ∈ ⋃ (j < order.succ (sup o)), pi0 s j,
    { intro n, apply mem_Union.2,
      specialize ho n,
      use o n,
      exact mem_Union.2 ⟨lt_of_le_of_lt (le_sup o n) (order.lt_succ (sup o)), ho.2⟩ },
    use λ n, (⟨f n, typf n⟩ : ⋃ (j < order.succ (sup o)), pi0 s j),
    tauto },
  { simp only [Union_subset_iff],
    exact λ _ hi, sigma0_subset_sigma0 s _ _ (le_of_lt hi) }
end

theorem compl_mem_gen_measurable (t : set α) (ht : t ∈ gen_measurable s) :
  tᶜ ∈ gen_measurable s :=
begin
  rw gen_measurable_eq_Union_sigma0 at ht,
  simp only [mem_Union,exists_prop] at ht,
  cases ht with o ho,
  rcases classical.em (o=0) with rfl | onon,
  { finish },
  calc
  tᶜ  ∈ pi0 s o          : by { rw pi0_eq_compl_sigma0,
    simp only [mem_image,compl_inj_iff,exists_eq_right], exacts [ho.2,onon] }
  ... ⊆ gen_measurable s : pi0_subset_sigma0 s o ω₁ ho.1,
end

theorem Union_mem_gen_measurable {f : ℕ → set α} (hf : ∀ n, f n ∈ gen_measurable s) :
  (⋃ n, f n) ∈ gen_measurable s:=
by { unfold gen_measurable at *, exact Union_of_mem_sigma0 s ω₁ hf }

open measurable_space

lemma generate_measurable_of_mem_sigma0 (t) (ht : t ∈ sigma0 s i) :
  generate_measurable s t :=
begin
  induction i using ordinal.induction with i IH generalizing t,
  rw [sigma0_eq_Union_pi0,mem_range] at ht,
  rcases ht with ⟨f,hf⟩,
  have typf : ∀ n : ℕ, generate_measurable s (f n),
  { intro n,
    have fn_in : (f n).val ∈ ⋃ (j : ordinal) (hij : j < i), pi0 s j := (f n).property,
    simp only [subtype.val_eq_coe,mem_Union,exists_prop] at fn_in,
    rcases fn_in with ⟨o,⟨o_lt_i,fn_in⟩⟩,
    -- Case `(f n).val ∈ pi0 s 0`.
    rcases classical.em (o=0) with rfl | honz,
    { rw pi0_zero at fn_in,
      rcases fn_in with  fn_in | fn_emp | fn_in,
      { exact generate_measurable.basic _ fn_in },
      { rw fn_emp, exact generate_measurable.empty },
      { rw mem_singleton_iff at fn_in, rw [fn_in,←compl_empty],
        exact generate_measurable.compl _ generate_measurable.empty } },
    -- Case `(f n).val ∈ pi0 s o` with `o ≠ 0`.
    simp only at IH,
    rw pi0_eq_compl_sigma0 s o honz at fn_in,
    rw ← compl_compl ↑(f n),
    apply generate_measurable.compl,
    cases fn_in with x hx,
    rw [←hx.2, compl_compl],
    exact IH o o_lt_i x hx.1 },
  rw ← hf,
  exact generate_measurable.union (λn, (f n).val) typf
end

theorem generate_measurable_eq_gen_measurable :
  {t | generate_measurable s t} = gen_measurable s :=
begin
  ext t, refine ⟨λ ht, _, λ ht, _⟩,
  { have om1_nonz : ω₁ ≠ 0,
    { unfold omega_1, exact ne_zero_of_out_nonempty _,},
    induction ht with u hu u hu IH f hf IH,
    exacts
    [ self_subset_sigma0 s ω₁ om1_nonz hu,
      empty_mem_sigma0 s ω₁ om1_nonz,
      compl_mem_gen_measurable s u IH,
      Union_mem_gen_measurable s IH ] },
  { exact generate_measurable_of_mem_sigma0 s ω₁ t ht }
end

end gen_measurable

section card_gen_measurable

/-!
### Cardinality of sigma-algebras
-/

variables {α : Type u} (s : set (set α)) (i k : ordinal.{u})

open set measurable_space cardinal ordinal
open_locale cardinal ordinal

/- The result holds for arbitrary `i`, but it is easier to prove
this way -/
lemma cardinal_sigma0_le (hi : i ≤ ω₁):
  #(sigma0 s i) ≤ (max (#s) 2) ^ aleph_0.{u} :=
begin
  induction i using ordinal.induction with i IH,
  have Upi0sub : (⋃ j < i, pi0 s j) ⊆ s ∪ {∅, univ} ∪ ⋃ j < i, compl '' sigma0 s j,
  { simp only [mem_singleton_iff,union_insert,union_singleton,mem_insert_iff,Union_subset_iff],
    intros j hj x hx,
    rcases classical.em (j=0) with rfl | hjnz,
    { simp only [mem_singleton_iff,union_insert,union_singleton,mem_insert_iff,pi0_zero] at hx,
      exact mem_union_left _ hx },
    rw pi0_eq_compl_sigma0 s j hjnz at hx,
    apply mem_union_right _ (mem_Union.mpr _),
    use j,
    apply mem_Union.mpr,
    use hj,
    exact hx },
  have cardcompl : ∀ j, #(sigma0 s j) = #(compl '' sigma0 s j) :=
    λ j, cardinal.eq.mpr (⟨equiv.set.image _ _  compl_injective⟩),
  have A := aleph_0_le_aleph 1,
  have B : aleph 1 ≤ (max (#s) 2) ^ aleph_0.{u} :=
    aleph_one_le_continuum.trans (power_le_power_right (le_max_right _ _)),
  have C : ℵ₀ ≤ (max (#s) 2) ^ aleph_0.{u} := A.trans B,
  have L : #(↥(s ∪ {∅, univ})) ≤ (max (#s) 2) ^ aleph_0.{u},
  { apply_rules [(mk_union_le _ _).trans, add_le_of_le C, mk_image_le.trans],
    { exact (le_max_left _ _).trans (self_le_power _ one_lt_aleph_0.le) },
    repeat { simp only [mk_fintype,fintype.card_unique,nat.cast_one,mk_singleton],
      exact one_lt_aleph_0.le.trans C } },
  have K : #(↥⋃ j < i, compl '' sigma0 s j) ≤ (max (#s) 2) ^ aleph_0.{u},
  { apply mk_Union_ordinal_le_of_le,
    exact (hi.trans $ ord_le_ord.mpr B),
    exact C,
    intros j hj,
    rw ← cardcompl,
    apply IH j hj,
    exact (le_of_lt $ lt_of_lt_of_le hj hi) },
  have J : #(↥(s ∪ {∅, univ} ∪ ⋃ j < i, compl '' sigma0 s j)) ≤ (max (#s) 2) ^ aleph_0.{u},
    { calc
      #(↥(s ∪ {∅, univ} ∪ ⋃ j < i, compl '' sigma0 s j)) ≤
        #(↥(s ∪ {∅, univ})) + #(↥⋃ j < i, compl '' sigma0 s j) : mk_union_le _ _
      ... ≤ (max (#s) 2) ^ aleph_0.{u} + (max (#s) 2) ^ aleph_0.{u} :
        (add_le_add (le_refl _) K).trans (add_le_add L (le_refl _))
      ... = (max (#s) 2) ^ aleph_0.{u} :
        (add_eq_max C).trans (max_eq_right (le_refl _)) },
  -- The main calculation:
  calc
  #↥(sigma0 s i) =
    #↥(range (λ (f : ℕ → (↥⋃ j < i, pi0 s j)), ⋃ n, ↑(f n))) :
    by { rw sigma0_eq_Union_pi0, simp }
  ... ≤ #(ℕ → (↥⋃ j < i, pi0 s j))                  : mk_range_le
  ... = prod (λ n : ℕ, #(↥⋃ j < i, pi0 s j))        : mk_pi _
  ... = #(↥⋃ j < i, pi0 s j) ^ aleph_0.{u}          : by { simp [prod_const] }
  ... ≤ #(↥(s ∪ {∅, univ} ∪ ⋃ j < i, compl '' sigma0 s j)) ^ aleph_0.{u} :
    power_le_power_right (mk_le_mk_of_subset Upi0sub)
  ... ≤ (max (# ↥s) 2 ^ aleph_0.{u}) ^ aleph_0.{u}  : power_le_power_right J
  ... ≤ (max (# ↥s) 2 ^ aleph_0.{u})                :
    by { rwa [← power_mul, aleph_0_mul_aleph_0] }
end

theorem cardinal_gen_measurable_le :
  #(gen_measurable s) ≤ (max (#s) 2) ^ aleph_0.{u} := cardinal_sigma0_le _ _ (le_refl _)

theorem cardinal_generate_measurable_le :
  #{t | generate_measurable s t} ≤ (max (#s) 2) ^ aleph_0.{u} :=
begin
  rw generate_measurable_eq_gen_measurable,
  exact cardinal_gen_measurable_le s,
end

theorem cardinal_measurable_set_le' :
  #{t | @measurable_set α (generate_from s) t} ≤ (max (#s) 2) ^ aleph_0.{u} :=
cardinal_generate_measurable_le _

theorem cardinal_generate_measurable_le_continuum (hs : #s ≤ 𝔠) :
  #{t | generate_measurable s t} ≤ 𝔠 :=
(cardinal_generate_measurable_le _).trans begin
  rw ←continuum_power_aleph_0,
  exact_mod_cast power_le_power_right (max_le hs (nat_lt_continuum 2).le)
end

theorem cardinal_measurable_set_le_continuum :
  #s ≤ 𝔠 → #{t | @measurable_set α (generate_from s) t} ≤ 𝔠 :=
cardinal_generate_measurable_le_continuum _

end card_gen_measurable

end pointclasses
