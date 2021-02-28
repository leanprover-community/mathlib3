/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Reid Barton
-/
import topology.separation

/-!
# The shrinking lemma

In this file we prove a few versions of the shrinking lemma. The lemma says that in a normal
topological space a point finite open covering can be “shrunk”: for a point finite open covering
`u : ι → set X` there exists a refinement `v : ι → set X` such that `closure (v i) ⊆ u i`.

For finite or countable coverings this lemma can be proved without the axiom of choice, see
[ncatlab](https://ncatlab.org/nlab/show/shrinking+lemma) for details. We only formalize the most
general result that works for any covering but needs the axiom of choice.

We prove two versions of the lemma:

* `exists_subset_Union_closure_subset` deals with a covering of a closed set in a normal space;
* `exists_Union_eq_closure_subset` deals with a covering of the whole space.

## Implementation details

The shrinking lemma is true not only for general open coverings of a normal space but also, e.g.,
for coverings of a proper metric space by open balls. In order to make the result reusable in other
settings, we introduce an auxiliary structure `shrinking_lemma_data`, prove the shrinking lemma for
any `B : shrinking_lemma_data ι _ X`, and provide an instance of `shrinking_lemma_data` for a normal
topological space.

## Tags

normal space, shrinking lemma
-/

open set zorn function
open_locale classical
noncomputable theory

variables {ι α X : Type*} [topological_space X]

/-- We prove the shrinking lemma for any family of sets `B : ι → α → set X`
satisfying the properties listed in this structure.

* In a normal space one can take `α = {s | is_open s}`, `rel s t = closure s ⊆ t`,
  and `B i ⟨s, hs⟩ = s`.
* In a proper metric space one can take `α = ℝ` or `α = (0, +∞)`, `rel = (<)`,
  and `B i r = ball (c i) r`, where `c : ι → α` is some fixed family of centers. -/
structure shrinking_lemma_data (ι α X : Type*) [topological_space X] :=
(to_fun : ι → α → set X)
(rel : α → α → Prop)
(subset' : ∀ i {a b}, rel a b → to_fun i a ⊆ to_fun i b)
(is_open' : ∀ i a, is_open (to_fun i a))
(exists_shrink' : ∀ i a (s ⊆ to_fun i a), is_closed s → ∃ a', rel a' a ∧ s ⊆ to_fun i a')

namespace shrinking_lemma_data

/-- Application of `shrinking_lemma_data.exists_Union_eq_closure_subset`
to `shrinking_lemma_data.of_noraml ι X` gives the standard shrinking lemma for normal spaces. -/
def of_normal (ι X : Type*) [topological_space X] [normal_space X] :
  shrinking_lemma_data ι {s : set X | is_open s} X :=
{ to_fun := λ _, coe,
  rel := λ s t, closure (s : set X) ⊆ t,
  subset' := λ _ s t h, subset.trans subset_closure h,
  is_open' := λ _ s, s.2,
  exists_shrink' := λ _ s t hts ht,
    let ⟨s', s'o, s's, s't⟩ := normal_shrink_left s.coe_prop ht
      (by rwa [← compl_subset_iff_union, compl_subset_compl])
    in ⟨⟨s', s'o⟩, s's, by rwa [← compl_subset_iff_union, compl_subset_compl] at s't⟩ }

instance [normal_space X] : inhabited (shrinking_lemma_data ι {s : set X | is_open s} X) :=
⟨of_normal ι X⟩

variables (B : shrinking_lemma_data ι α X)

instance : has_coe_to_fun (shrinking_lemma_data ι α X) := ⟨_, to_fun⟩

protected lemma is_open (i : ι) (a : α) : is_open (B i a) := B.is_open' _ _

protected lemma subset (i : ι) {a b : α} (h : B.rel a b) : B i a ⊆ B i b := B.subset' i h

lemma exists_shrink (i : ι) (a : α) {s : set X} (h : s ⊆ B i a) (hs : is_closed s) :
  ∃ a', B.rel a' a ∧ s ⊆ B i a' :=
B.exists_shrink' _ _ _ h hs

/-- Auxiliary definition for the proof of `shrinking_lemma_data.shrinking_lemma`. A partial
refinement of a covering `⋃ i, B i (u i)` on a set `s` is a map `v : ι → α` and a set
`carrier : set ι` such that

* `s ⊆ ⋃ i, B i (v i)`;
* if `i ∈ carrier v`, then `v i` is related to `u i` by `B.rel`;
* if `i ∉ carrier`, then `v i = u i`.

This type is equipped with the folowing partial order: `v ≤ v'` if `v.carrier ⊆ v'.carrier`
and `v i = v' i` for `i ∈ v.carrier`. We will use the Zorn's lemma to prove that this type has
a maximal element, then show that the maximal element must have `carrier = univ`. -/
@[nolint has_inhabited_instance] -- the trivial refinement needs `u` to be a covering
structure partial_refinement (u : ι → α) (s : set X) :=
(to_fun : ι → α)
(carrier : set ι)
(subset_Union' : s ⊆ ⋃ i, B i (to_fun i))
(rel' : ∀ i ∈ carrier, B.rel (to_fun i) (u i))
(apply_eq' : ∀ i ∉ carrier, to_fun i = u i)

namespace partial_refinement

instance (u : ι → α) (s : set X) : has_coe_to_fun (B.partial_refinement u s) := ⟨_, to_fun⟩

variables {B} {u : ι → α} {s : set X}

lemma subset_Union (v : partial_refinement B u s) : s ⊆ ⋃ i, B i (v i) := v.subset_Union'

protected lemma rel (v : partial_refinement B u s) {i : ι} (hi : i ∈ v.carrier) :
  B.rel (v i) (u i) :=
v.rel' i hi

lemma apply_eq (v : partial_refinement B u s) {i : ι} (hi : i ∉ v.carrier) : v i = u i :=
v.apply_eq' i hi

protected lemma subset (v : partial_refinement B u s) (i : ι) : B i (v i) ⊆ B i (u i) :=
if h : i ∈ v.carrier then B.subset i $ v.rel h
else (congr_arg (B i) (v.apply_eq h)).le

attribute [ext] partial_refinement

instance : partial_order (partial_refinement B u s) :=
{ le := λ v₁ v₂, v₁.carrier ⊆ v₂.carrier ∧ ∀ i ∈ v₁.carrier, v₁ i = v₂ i,
  le_refl := λ v, ⟨subset.refl _, λ _ _, rfl⟩,
  le_trans := λ v₁ v₂ v₃ h₁₂ h₂₃,
    ⟨subset.trans h₁₂.1 h₂₃.1, λ i hi, (h₁₂.2 i hi).trans (h₂₃.2 i $ h₁₂.1 hi)⟩,
  le_antisymm := λ v₁ v₂ h₁₂ h₂₁,
    have hc : v₁.carrier = v₂.carrier, from subset.antisymm h₁₂.1 h₂₁.1,
    ext _ _ (funext $ λ x,
      if hx : x ∈ v₁.carrier then h₁₂.2 _ hx
      else (v₁.apply_eq hx).trans (eq.symm $ v₂.apply_eq $ hc ▸ hx)) hc }

/-- If two partial refinements `v₁`, `v₂` belong to a chain (hence, they are comparable)
and `i` belongs to the carriers of both partial refinements, then `v₁ i = v₂ i`. -/
lemma apply_eq_of_chain {c : set (partial_refinement B u s)} (hc : chain (≤) c) {v₁ v₂}
  (h₁ : v₁ ∈ c) (h₂ : v₂ ∈ c) {i} (hi₁ : i ∈ v₁.carrier) (hi₂ : i ∈ v₂.carrier) :
  v₁ i = v₂ i :=
begin
  wlog hle : v₁ ≤ v₂ := hc.total_of_refl h₁ h₂ using [v₁ v₂, v₂ v₁],
  exact hle.2 _ hi₁,
end

/-- The carrier of the least upper bound of a non-empty chain of partial refinements
is the union of their carriers. -/
def chain_Sup_carrier (c : set (partial_refinement B u s)) : set ι :=
⋃ v ∈ c, carrier v

/-- Choice of an element of a nonempty chain of partial refinements. If `i` belongs to one of
`carrier v`, `v ∈ c`, then `find c ne i` is one of these partial refinements. -/
def find (c : set (partial_refinement B u s)) (ne : c.nonempty) (i : ι) :
  partial_refinement B u s :=
if hi : ∃ v ∈ c, i ∈ carrier v then hi.some else ne.some

lemma find_mem {c : set (partial_refinement B u s)} (i : ι) (ne : c.nonempty) :
  find c ne i ∈ c :=
by { rw find, split_ifs, exacts [h.some_spec.fst, ne.some_spec] }

lemma mem_find_carrier_iff {c : set (partial_refinement B u s)} {i : ι} (ne : c.nonempty) :
  i ∈ (find c ne i).carrier ↔ i ∈ chain_Sup_carrier c :=
begin
  rw find,
  split_ifs,
  { have : i ∈ h.some.carrier ∧ i ∈ chain_Sup_carrier c,
      from ⟨h.some_spec.snd, mem_bUnion_iff.2 h⟩,
    simp only [this] },
  { have : i ∉ ne.some.carrier ∧ i ∉ chain_Sup_carrier c,
      from ⟨λ hi, h ⟨_, ne.some_spec, hi⟩, mt mem_bUnion_iff.1 h⟩,
    simp only [this] }
end

lemma find_apply_of_mem {c : set (partial_refinement B u s)} (hc : chain (≤) c) (ne : c.nonempty)
  {i v} (hv : v ∈ c) (hi : i ∈ carrier v) :
  find c ne i i = v i :=
apply_eq_of_chain hc (find_mem _ _) hv
  ((mem_find_carrier_iff _).2 $ mem_bUnion_iff.2 ⟨v, hv, hi⟩) hi

/-- Least upper bound of a nonempty chain of partial refinements. -/
def chain_Sup (c : set (partial_refinement B u s)) (hc : chain (≤) c)
  (ne : c.nonempty) (hfin : ∀ x ∈ s, finite {i | x ∈ B i (u i)}) (hU : s ⊆ ⋃ i, B i (u i)) :
  partial_refinement B u s :=
begin
  refine ⟨λ i, find c ne i i, chain_Sup_carrier c,
    λ x hxs, mem_Union.2 _,
    λ i hi, (find c ne i).rel ((mem_find_carrier_iff _).2 hi),
    λ i hi, (find c ne i).apply_eq (mt (mem_find_carrier_iff _).1 hi)⟩,
  rcases em (∃ i ∉ chain_Sup_carrier c, x ∈ B i (u i)) with ⟨i, hi, hxi⟩|hx,
  { use i,
    rwa (find c ne i).apply_eq (mt (mem_find_carrier_iff _).1 hi) },
  { simp_rw [not_exists, not_imp_not, chain_Sup_carrier, mem_bUnion_iff] at hx,
    haveI : nonempty (B.partial_refinement u s) := ⟨ne.some⟩,
    choose! v hvc hiv using hx,
    rcases (hfin x hxs).exists_maximal_wrt v _ (mem_Union.1 (hU hxs))
      with ⟨i, hxi : x ∈ B i (u i), hmax : ∀ j, x ∈ B j (u j) → v i ≤ v j → v i = v j⟩,
    rcases mem_Union.1 ((v i).subset_Union hxs) with ⟨j, hj⟩,
    use j,
    have hj' : x ∈ B j (u j) := (v i).subset _ hj,
    have : v j ≤ v i,
      from (hc.total_of_refl (hvc _ hxi) (hvc _ hj')).elim (λ h, (hmax j hj' h).ge) id,
    rwa find_apply_of_mem hc ne (hvc _ hxi) (this.1 $ hiv _ hj') }
end

/-- `chain_Sup hu c hc ne hfin hU` is an upper bound of the chain `c`. -/
lemma le_chain_Sup {c : set (partial_refinement B u s)} (hc : chain (≤) c)
  (ne : c.nonempty) (hfin : ∀ x ∈ s, finite {i | x ∈ B i (u i)}) (hU : s ⊆ ⋃ i, B i (u i))
  {v} (hv : v ∈ c) :
  v ≤ chain_Sup c hc ne hfin hU :=
⟨λ i hi, mem_bUnion hv hi, λ i hi, (find_apply_of_mem hc _ hv hi).symm⟩

/-- If `s` is a closed set, `v` is a partial refinement, and `i` is an index such that
`i ∉ v.carrier`, then there exists a partial refinement that is strictly greater than `v`. -/
lemma exists_gt (v : partial_refinement B u s) (hs : is_closed s) (i : ι) (hi : i ∉ v.carrier) :
  ∃ v' : partial_refinement B u s, v < v' :=
begin
  have I : s ∩ (⋂ j ≠ i, (B j (v j))ᶜ) ⊆ B i (v i),
  { simp only [subset_def, mem_inter_eq, mem_Inter, and_imp],
    intros x hxs H,
    rcases mem_Union.1 (v.subset_Union hxs) with ⟨j, hj⟩,
    exact (em (j = i)).elim (λ h, h ▸ hj) (λ h, (H j h hj).elim) },
  have C : is_closed (s ∩ (⋂ j ≠ i, (B j (v j))ᶜ)),
    from is_closed_inter hs (is_closed_bInter $ λ _ _, is_closed_compl_iff.2 $ B.is_open _ _),
  rcases B.exists_shrink i (v i) I C with ⟨vi, cvi, hvi⟩,
  refine ⟨⟨update v i vi, insert i v.carrier, _, _, _⟩, _, _⟩,
  { refine λ x hx, mem_Union.2 _,
    rcases em (∃ j ≠ i, x ∈ B j (v j)) with ⟨j, hji, hj⟩|h,
    { use j, rwa update_noteq hji },
    { push_neg at h, use i, rw update_same, exact hvi ⟨hx, mem_bInter h⟩ } },
  { rintro j (rfl|hj),
    { rwa [update_same, ← v.apply_eq hi] },
    { rw update_noteq (ne_of_mem_of_not_mem hj hi), exact v.rel hj } },
  { intros j hj,
    rw [mem_insert_iff, not_or_distrib] at hj,
    rw [update_noteq hj.1, v.apply_eq hj.2] },
  { refine ⟨subset_insert _ _, λ j hj, _⟩,
    exact (update_noteq (ne_of_mem_of_not_mem hj hi) _ _).symm },
  { exact λ hle, hi (hle.1 $ mem_insert _ _) }
end

end partial_refinement

/-- Shrinking lemma. Let `B : ι → α → set X` be a map and `B.rel : α → α → Prop` be a relation.
Suppose that

* each `B i a` is open,
* `B i a ⊆ B i a'` whenever `B.rel a a'`,
* for every `i : ι`, `a : α`, and a closed set `t ⊆ B i a` there exists `a'` such that `B.rel a' a`
  and `t ⊆ B i a'`.

E.g., for a normal space one can take `α = {s | is_open s}`, `B i = coe`,
and `B.rel s t = closure s ⊆ t`; for a proper metric space one can take `α = ℝ`,
`B i r = ball (c i) r`, where `c : ι → X` is some fixed map, and `B.rel = (<)`.

Then for any closed set `s` and a point finite covering `⋃ i, B i (u i)` of `s` there exists
a refinement covering `⋃ i, B i (v i)` of `s` such that for all `i` we have `B.rel (v i) (u i)`.

The proof is based on
https://ncatlab.org/nlab/show/shrinking+lemma#ShrinkingLemmaForLocallyFiniteCountableCovers
with minor modifications introducing the family `B` and a closed set `s`. -/
lemma exists_subset_Union_forall_rel (B : shrinking_lemma_data ι α X)
  {s : set X} (hs : is_closed s) (u : ι → α) (uf : ∀ x ∈ s, finite {i | x ∈ B i (u i)})
  (su : s ⊆ ⋃ i, B i (u i)) :
  ∃ v : ι → α, s ⊆ (⋃ i, B i (v i)) ∧ ∀ i, B.rel (v i) (u i) :=
begin
  classical,
  have : ∀ c : set (partial_refinement B u s), chain (≤) c → ∃ ub, ∀ v ∈ c, v ≤ ub,
  { intros c hc,
    rcases eq_empty_or_nonempty c with rfl|ne,
    { exact ⟨⟨u, ∅, su, λ _, false.elim, λ _ _, rfl⟩, λ _, false.elim⟩ },
    { exact ⟨partial_refinement.chain_Sup c hc ne uf su,
        λ v hv, partial_refinement.le_chain_Sup _ _ _ _ hv⟩ } },
  rcases zorn_partial_order this with ⟨v, hv⟩,
  suffices : ∀ i, i ∈ v.carrier, from ⟨v, v.subset_Union, λ i, v.rel (this i)⟩,
  contrapose! hv,
  rcases hv with ⟨i, hi⟩,
  rcases v.exists_gt hs i hi with ⟨v', hlt⟩,
  exact ⟨v', hlt.le, hlt.ne'⟩
end

/-- Shrinking lemma. Let `B : ι → α → set X` be a map and `B.rel : α → α → Prop` be a relation.
Suppose that

* each `B i a` is open,
* `B i a ⊆ B i a'` whenever `B.rel a a'`,
* for every `i : ι`, `a : α`, and a closed set `t ⊆ B i a` there exists `a'` such that `B.rel a' a`
  and `t ⊆ B i a'`.

E.g., for a normal space one can take `α = {s | is_open s}`, `B i = coe`,
and `B.rel s t = closure s ⊆ t`; for a proper metric space one can take `α = ℝ`,
`B i r = ball (c i) r`, where `c : ι → X` is some fixed map, and `B.rel = (<)`.

Then for a point finite covering `⋃ i, B i (u i)` of the whole space `X` there exists a refinement
covering `⋃ i, B i (v i)` of `X` such that for all `i` we have `B.rel (v i) (u i)`. -/
lemma exists_Union_eq_forall_rel (B : shrinking_lemma_data ι α X)
  (u : ι → α) (uf : ∀ x, finite {i | x ∈ B i (u i)}) (su : (⋃ i, B i (u i)) = univ) :
  ∃ v : ι → α, (⋃ i, B i (v i)) = univ ∧ ∀ i, B.rel (v i) (u i) :=
let ⟨v, vU, hv⟩ := B.exists_subset_Union_forall_rel is_closed_univ u (λ x _, uf x) su.ge
in ⟨v, univ_subset_iff.1 vU, hv⟩

end shrinking_lemma_data

variables [normal_space X] {u : ι → set X} {s : set X}

/-- A point-finite open cover of a closed subset of a normal space can be "shrunk" to a new open
cover so that the closure of each new open set is contained in the corresponding original open
set. -/
lemma exists_subset_Union_closure_subset (hs : is_closed s) (uo : ∀ i, is_open (u i))
  (uf : ∀ x ∈ s, finite {i | x ∈ u i}) (us : s ⊆ ⋃ i, u i) :
  ∃ v : ι → set X, s ⊆ Union v ∧ ∀ i, is_open (v i) ∧ closure (v i) ⊆ u i :=
let ⟨v, hsv, hv⟩ := (shrinking_lemma_data.of_normal ι X).exists_subset_Union_forall_rel
  hs (λ i, ⟨u i, uo i⟩) uf us
in ⟨λ i, v i, hsv, λ i, ⟨(v i).2, hv i⟩⟩

/-- A point-finite open cover of a closed subset of a normal space can be "shrunk" to a new open
cover so that the closure of each new open set is contained in the corresponding original open
set. -/
lemma exists_Union_eq_closure_subset (uo : ∀ i, is_open (u i)) (uf : ∀ x, finite {i | x ∈ u i})
  (uU : (⋃ i, u i) = univ) :
  ∃ v : ι → set X, Union v = univ ∧ ∀ i, is_open (v i) ∧ closure (v i) ⊆ u i :=
let ⟨v, Uv, hv⟩ :=
  (shrinking_lemma_data.of_normal ι X).exists_Union_eq_forall_rel (λ i, ⟨u i, uo i⟩) uf uU
in ⟨λ i, v i, Uv, λ i, ⟨(v i).2, hv i⟩⟩
