/-
Copyright (c) 2018 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow
-/
import topology.basic topology.continuity topology.metric_space.basic
import data.real.cau_seq_filter

open filter

/- Sequences in topological spaces.
 - 
 - In this file we define sequences in topological spaces and show how they are related to
 - filters and the topology. In particular, we
 -
 - (*) associate a filter with a sequence and prove equivalence of convergence of the two,
 - (*) define the sequential closure of a set and prove that it's contained in the closure, 
 - (*) define a type class "sequential_space" in which closure and sequential closure agree, 
 - (*) define sequential continuity and show that it coincides with continuity in sequential spaces,
 - (*) provide an instance that shows that every metric space is a sequential space.
 -
 - TODO: There should be an instance that associates a sequential space with a first countable
 -       space. 
 - TODO: Sequential compactness should be handled here.
 -/
namespace sequence

universes u v
variables {X : Type u} {Y : Type v}

local notation x `⟶` limit := tendsto x at_top (nhds limit)

/- Statements about sequences in general topological spaces. -/
section topological_space
variables [topological_space X] [topological_space Y]


/-- A sequence converges in the sence of topological spaces iff the associated statement for filter holds. -/
@[simp] lemma topological_space.seq_tendsto_iff [topological_space X] {x : ℕ → X} {limit : X} :
  tendsto x at_top (nhds limit) ↔ ∀ U : set X, limit ∈ U → is_open U → ∃ n0 : ℕ, ∀ n ≥ n0, (x n) ∈ U := 
iff.intro
  (assume ttol : tendsto x at_top (nhds limit),
    show ∀ U : set X, limit ∈ U → is_open U → ∃ n0 : ℕ, ∀ n ≥ n0, (x n) ∈ U, from
      assume U limitInU isOpenU,
        have {n | (x n) ∈ U} ∈ at_top.sets, from mem_map.mp $ le_def.mp ttol U 
                                             (mem_nhds_sets isOpenU limitInU),
        show ∃ n0 : ℕ, ∀ n ≥ n0, (x n) ∈ U, from mem_at_top_sets.mp this)
  (assume xtol : ∀ U : set X, limit ∈ U → is_open U → ∃ n0 : ℕ, ∀ n ≥ n0, (x n) ∈ U,
    suffices ∀ U, limit ∈ U → is_open U → x ⁻¹' U ∈ at_top.sets, from tendsto_nhds this,
      assume U limitInU isOpenU,
        suffices ∃ n0 : ℕ, ∀ n ≥ n0, (x n) ∈ U, by simp[this],
        xtol U limitInU isOpenU)

lemma const_seq_conv [topological_space X] (p : X) : (λ n : ℕ, p) ⟶ p :=
suffices ∀ U : set X, p ∈ U → is_open U → ∃ n0 : ℕ, ∀ n ≥ n0, p ∈ U, by simp; exact this,
assume U (_ : p ∈ U) (_ : is_open U), exists.intro 0 (assume n (_ : n ≥ 0), ‹p ∈ U›)


/-- The sequential closure of a subset M ⊆ X of a topological space X is 
    the set of all p ∈ X which arise as limit of sequences in M. -/
def sequential_closure (M : set X) : set X :=
{p | ∃ x : ℕ → X, (∀ n : ℕ, ((x n) ∈ M)) ∧ (x ⟶ p)}


lemma subset_seq_closure (M : set X) : M ⊆ sequential_closure M := 
assume p (_ : p ∈ M), show p ∈ sequential_closure M, from
  exists.intro (λ n, p) ⟨assume n, ‹p ∈ M›, const_seq_conv p⟩

def is_seq_closed (A : set X) : Prop := A = sequential_closure A

/-- A convenience lemma for showing that a set is sequentially closed. -/
lemma is_seq_closed_of_def {A : set X} (h : ∀ (x : ℕ → X), (∀ n : ℕ, ((x n) ∈ A)) → ∀ p : X,
  (x ⟶ p) → p ∈ A) : is_seq_closed A :=
show A = sequential_closure A, from set.subset.antisymm
  (subset_seq_closure A)
  (show ∀ p, (p ∈ sequential_closure A) → p ∈ A, from 
    (assume p _,
      have ∃ x : ℕ → X, (∀ n : ℕ, ((x n) ∈ A)) ∧ (x ⟶ p), by assumption,
      let ⟨x, ⟨_, _⟩⟩ := this in
      show p ∈ A, from h x ‹∀ n : ℕ, ((x n) ∈ A)› p ‹(x ⟶ p)›))

/-- The sequential closure of a set is contained in the closure of that set. The converse is not true. -/ 
lemma sequential_closure_subset_closure (M : set X) : sequential_closure M ⊆ closure M :=
show ∀ p, p ∈ sequential_closure M → p ∈ closure M, from
assume p,
assume : ∃ x : ℕ → X, (∀ n : ℕ, ((x n) ∈ M)) ∧ (x ⟶ p),
let ⟨x, ⟨_, _⟩⟩ := this in
show p ∈ closure M, from
-- we have to show that p is in the closure of M
-- using mem_closure_iff, this is equivalent to proving that every open neighbourhood
-- has nonempty intersection with M, but this is witnessed by our sequence x
suffices ∀ O, is_open O → p ∈ O → O ∩ M ≠ ∅, from mem_closure_iff.mpr this,
have ∀ (U : set X), p ∈ U → is_open U → (∃ n0, ∀ n, n ≥ n0 → x n ∈ U), by rwa[←topological_space.seq_tendsto_iff],
assume O is_open_O p_in_O,
let ⟨n0, _⟩ := this O ‹p ∈ O› ‹is_open O› in
have (x n0) ∈ O, from ‹∀ n ≥ n0, x n ∈ O› n0 (show n0 ≥ n0, from le_refl n0),
have (x n0) ∈ O ∩ M, from ⟨this, ‹∀n, x n ∈ M› n0⟩,
set.ne_empty_of_mem this

/-- A set is sequentially closed if it is closed. -/
lemma is_seq_closed_of_is_closed (M : set X) (_ : is_closed M) : is_seq_closed M :=
suffices sequential_closure M ⊆ M,
  from set.eq_of_subset_of_subset (subset_seq_closure M) this,
calc sequential_closure M ⊆ closure M : sequential_closure_subset_closure M
                      ... = M : closure_eq_of_is_closed ‹is_closed M›

/-- The limit of a convergent sequence in a sequentially closed set is in that set.-/
lemma is_mem_of_conv_to_of_is_seq_closed {A : set X} (_ : is_seq_closed A) {x : ℕ → X}
  (_ : ∀ n, x n ∈ A) {limit : X} (_ : (x ⟶ limit)) : limit ∈ A :=
have limit ∈ sequential_closure A, from 
  show ∃ x : ℕ → X, (∀ n : ℕ, ((x n) ∈ A)) ∧ (x ⟶ limit), from
    exists.intro x ⟨‹∀ n, x n ∈ A›, ‹(x ⟶ limit)›⟩,
eq.subst (eq.symm ‹is_seq_closed A›) ‹limit ∈ sequential_closure A›

/-- The limit of a convergent sequence in a closed set is in that set.-/
lemma is_mem_of_is_closed_of_conv_to {A : set X} (_ : is_closed A) {x : ℕ → X}
  (_ : ∀ n, x n ∈ A) {limit : X} (_ : x ⟶ limit) : limit ∈ A :=
is_mem_of_conv_to_of_is_seq_closed (is_seq_closed_of_is_closed A ‹is_closed A›)
  ‹∀ n, x n ∈ A› ‹(x ⟶ limit)›

/-- A sequential space is a space in which 'sequences are enough to probe the topology'. This can be
 formalised by demanding that the sequential closure and the closure coincide. The following
 statements show that other topological properties can be deduced from sequences in sequential
 spaces. -/
class sequential_space (X : Type u) [topological_space X] : Prop :=
(sequential_closure_eq_closure : ∀ M : set X, sequential_closure M = closure M)


/-- In a sequential space, a set is closed iff it's sequentially closed. -/
lemma is_seq_closed_iff_is_closed [sequential_space X] : ∀ {M : set X},
  (is_seq_closed M ↔ is_closed M) :=  
assume M, iff.intro
(assume _, closure_eq_iff_is_closed.mp (eq.symm
  (calc M = sequential_closure M : by assumption
      ... = closure M            : sequential_space.sequential_closure_eq_closure M)))
(is_seq_closed_of_is_closed M)

/-- A function between topological spaces is sequentially continuous if it commutes with limit of
 convergent sequences. -/
def sequentially_continuous (f : X → Y) : Prop :=
∀ (x : ℕ → X), ∀ {limit : X}, (x ⟶ limit) → (f∘x ⟶ f limit)

/- A continuous function is sequentially continuous. -/
lemma cont_to_seq_cont {f : X → Y} (_ : continuous f) : sequentially_continuous f :=
assume x limit (_ : x ⟶ limit),
have tendsto f (nhds limit) (nhds (f limit)), from continuous.tendsto ‹continuous f› limit,
show (f ∘ x) ⟶ (f limit), from tendsto.comp ‹(x ⟶ limit)› this

/-- In a sequential space, continuity and sequential continuity coincide. -/
lemma cont_iff_seq_cont {f : X → Y} [sequential_space X] :
  continuous f ↔ sequentially_continuous f :=
iff.intro
  (assume _, cont_to_seq_cont ‹continuous f›) 
  (assume : sequentially_continuous f, show continuous f, from
    suffices h : ∀ {A : set Y}, is_closed A → is_seq_closed (f ⁻¹' A), from 
      continuous_iff_is_closed.mpr (assume A _, 
        is_seq_closed_iff_is_closed.mp $ h ‹is_closed A›),
    assume A (_ : is_closed A),
      is_seq_closed_of_def $
        assume (x : ℕ → X),
        assume : ∀ n, (x n) ∈ (f ⁻¹' A),
        have ∀ n, f (x n) ∈ A, by assumption,
        assume p (_ : x ⟶ p),
        have (f ∘ x) ⟶ (f p), from ‹sequentially_continuous f› x ‹(x ⟶ p)›, 
        show f p ∈ A, from is_mem_of_is_closed_of_conv_to ‹is_closed A› ‹∀ n, f (x n) ∈ A›
          ‹((f∘x) ⟶ (f p))›)
  

end topological_space

/- Statements about sequences in metric spaces -/
section metric_space
variable [metric_space X]
variables {ε : ℝ}

open metric

/-- A sequence converges in the sence of metric spaces iff the associated statement about filters holds. -/
@[simp] lemma metric_space.seq_tendsto_iff {x : ℕ → X} {limit : X} :
  (x ⟶ limit) ↔ ∀ ε > 0, ∃ n0 : ℕ, ∀ n ≥ n0, dist (x n) limit < ε :=
iff.intro
  (assume tendsto,
    have convTo : ∀ (U : set X), limit ∈ U → is_open U → (∃ n0, ∀ n, n ≥ n0 → x n ∈ U),
      by rwa[←topological_space.seq_tendsto_iff],
    show ∀ ε > 0, ∃ n0, ∀ n ≥ n0, dist (x n) limit < ε, from
      assume ε _,
      have ∃ n0 : ℕ, ∀ n ≥ n0, (x n) ∈ (ball limit ε), from 
        convTo (ball limit ε) (mem_ball_self ‹ε > 0›) is_open_ball,
      let ⟨n0, _⟩ := this in
      exists.intro n0 
        (show ∀ n ≥ n0, dist (x n) limit < ε, from
          assume n _,
            ‹∀ n ≥ n0, (x n) ∈ ball limit ε› n ‹n ≥ n0›))
  (assume metrConvTo,
    suffices ∀ U : set X, limit ∈ U → is_open U → ∃ n0 : ℕ, ∀ n ≥ n0, (x n) ∈ U, by simpa,
    assume U limitInU isOpenU,
      have ∃ ε > 0, ball limit ε ⊆ U, from is_open_iff.mp isOpenU limit limitInU,
      let ⟨ε, _, _⟩ := this in
      have ∃ n0, ∀ n ≥ n0, dist (x n) limit < ε, from metrConvTo ε ‹ε > 0›, 
      let ⟨n0, _⟩ := this in
      show ∃ n0, ∀ n ≥ n0, (x n) ∈ U, from  
        exists.intro n0 (assume n _, 
          have (x n) ∈ ball limit ε, from ‹∀ n ≥ n0, dist (x n) limit < ε› _ ‹n ≥ n0›,
          show (x n) ∈ U, from set.mem_of_subset_of_mem ‹ball limit ε ⊆ U› ‹(x n) ∈ ball limit ε›))

-- necessary for the next instance
set_option eqn_compiler.zeta true
/-- Show that every metric space is sequential. -/
instance metric_space.to_sequential_space : sequential_space X :=
⟨show ∀ M, sequential_closure M = closure M, from assume M,
  suffices closure M ⊆ sequential_closure M,
    from set.subset.antisymm (sequential_closure_subset_closure M) this,
  assume (p : X) (_ : p ∈ closure M),
  -- we construct a sequence in X, with values in M, that converges to p
  -- the first step is to use (p ∈ closure M) ↔ "all nhds of p contain elements of M" on metric
  -- balls 
  have ∀ n : ℕ, ball p ((1:ℝ)/((n+1):ℝ)) ∩ M ≠ ∅, from
    assume n : ℕ, mem_closure_iff.mp ‹p ∈ (closure M)› (ball p ((1:ℝ)/((n+1):ℝ))) (is_open_ball) 
                  (mem_ball_self (show (1:ℝ)/(n+1) > 0, from one_div_succ_pos n)),

  -- from this, construct a "sequence of hypothesis" h, (h n) := _ ∈ {x // x ∈ ball (1/n+1) p ∩ M}
  let h := λ n : ℕ, (classical.indefinite_description _ (set.exists_mem_of_ne_empty (this n))),
  -- and the actual sequence
      x := λ n : ℕ, (h n).val in

  -- now we construct the promised sequence and show the claim
  show ∃ x : ℕ → X, (∀ n : ℕ, ((x n) ∈ M)) ∧ (x ⟶ p), from
    exists.intro x
      (and.intro 
        (assume n, have (x n) ∈ ball p ((1:ℝ)/((n+1):ℝ)) ∩ M, from (h n).property, this.2)
        (suffices ∀ ε > 0, ∃ n0 : ℕ, ∀ n ≥ n0, dist (x n) p < ε, begin simpa only [metric_space.seq_tendsto_iff] end,
         assume ε _,
           -- we apply that 1/n converges to zero to the fact that (x n) ∈ ball p ε
           have ∀ ε > 0, ∃ n0 : ℕ, ∀ n ≥ n0, dist (1 / (↑n + 1)) (0:ℝ) < ε,
             from metric_space.seq_tendsto_iff.mp sequentially_complete.tendsto_div,
           let ⟨n0, hn0⟩ := this ε ‹ε > 0› in
           show ∃ n0 : ℕ, ∀ n ≥ n0, dist (x n) p < ε, from
           (exists.intro n0 (assume n ngtn0,
           show dist (x n) p < ε, from
           calc dist (x n) p < (1:ℝ)/↑(n+1) : (h n).property.1
                         ... = abs ((1:ℝ)/↑(n+1)) : eq.symm 
                                   (abs_of_pos (one_div_succ_pos n)) 
                         ... = abs ((1:ℝ)/↑(n+1) - 0) : by simp
                         ... = dist ((1:ℝ)/↑(n+1)) 0 : eq.symm $ real.dist_eq ((1:ℝ)/↑(n+1)) 0
                         ... < ε : hn0 n ‹n ≥ n0›))))⟩

set_option eqn_compiler.zeta false

end metric_space

end sequence
