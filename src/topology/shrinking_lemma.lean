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

## Tags

normal space, shrinking lemma
-/

open set zorn function
open_locale classical
noncomputable theory

variables {ι X : Type*} [topological_space X] [normal_space X]

namespace shrinking_lemma

/-- Auxiliary definition for the proof of `shrinking_lemma`. A partial refinement of a covering
`⋃ i, u i` of a set `s` is a map `v : ι → set X` and a set `carrier : set ι` such that

* `s ⊆ ⋃ i, v i`;
* all `v i` are open;
* if `i ∈ carrier v`, then `closure (v i) ⊆ u i`;
* if `i ∉ carrier`, then `v i = u i`.

This type is equipped with the folowing partial order: `v ≤ v'` if `v.carrier ⊆ v'.carrier`
and `v i = v' i` for `i ∈ v.carrier`. We will use Zorn's lemma to prove that this type has
a maximal element, then show that the maximal element must have `carrier = univ`. -/
@[nolint has_inhabited_instance] -- the trivial refinement needs `u` to be a covering
structure partial_refinement (u : ι → set X) (s : set X) :=
(to_fun : ι → set X)
(carrier : set ι)
(is_open' : ∀ i, is_open (to_fun i))
(subset_Union' : s ⊆ ⋃ i, to_fun i)
(closure_subset' : ∀ i ∈ carrier, closure (to_fun i) ⊆ (u i))
(apply_eq' : ∀ i ∉ carrier, to_fun i = u i)

namespace partial_refinement

variables {u : ι → set X} {s : set X}

instance : has_coe_to_fun (partial_refinement u s) := ⟨_, to_fun⟩

lemma subset_Union (v : partial_refinement u s) : s ⊆ ⋃ i, v i := v.subset_Union'

lemma closure_subset (v : partial_refinement u s) {i : ι} (hi : i ∈ v.carrier) :
  closure (v i) ⊆ (u i) :=
v.closure_subset' i hi

lemma apply_eq (v : partial_refinement u s) {i : ι} (hi : i ∉ v.carrier) : v i = u i :=
v.apply_eq' i hi

protected lemma is_open (v : partial_refinement u s) (i : ι) : is_open (v i) := v.is_open' i

protected lemma subset (v : partial_refinement u s) (i : ι) : v i ⊆ u i :=
if h : i ∈ v.carrier then subset.trans subset_closure (v.closure_subset h)
else (v.apply_eq h).le

attribute [ext] partial_refinement

instance : partial_order (partial_refinement u s) :=
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
lemma apply_eq_of_chain {c : set (partial_refinement u s)} (hc : chain (≤) c) {v₁ v₂}
  (h₁ : v₁ ∈ c) (h₂ : v₂ ∈ c) {i} (hi₁ : i ∈ v₁.carrier) (hi₂ : i ∈ v₂.carrier) :
  v₁ i = v₂ i :=
begin
  wlog hle : v₁ ≤ v₂ := hc.total_of_refl h₁ h₂ using [v₁ v₂, v₂ v₁],
  exact hle.2 _ hi₁,
end

/-- The carrier of the least upper bound of a non-empty chain of partial refinements
is the union of their carriers. -/
def chain_Sup_carrier (c : set (partial_refinement u s)) : set ι :=
⋃ v ∈ c, carrier v

/-- Choice of an element of a nonempty chain of partial refinements. If `i` belongs to one of
`carrier v`, `v ∈ c`, then `find c ne i` is one of these partial refinements. -/
def find (c : set (partial_refinement u s)) (ne : c.nonempty) (i : ι) :
  partial_refinement u s :=
if hi : ∃ v ∈ c, i ∈ carrier v then hi.some else ne.some

lemma find_mem {c : set (partial_refinement u s)} (i : ι) (ne : c.nonempty) :
  find c ne i ∈ c :=
by { rw find, split_ifs, exacts [h.some_spec.fst, ne.some_spec] }

lemma mem_find_carrier_iff {c : set (partial_refinement u s)} {i : ι} (ne : c.nonempty) :
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

lemma find_apply_of_mem {c : set (partial_refinement u s)} (hc : chain (≤) c) (ne : c.nonempty)
  {i v} (hv : v ∈ c) (hi : i ∈ carrier v) :
  find c ne i i = v i :=
apply_eq_of_chain hc (find_mem _ _) hv
  ((mem_find_carrier_iff _).2 $ mem_bUnion_iff.2 ⟨v, hv, hi⟩) hi

/-- Least upper bound of a nonempty chain of partial refinements. -/
def chain_Sup (c : set (partial_refinement u s)) (hc : chain (≤) c)
  (ne : c.nonempty) (hfin : ∀ x ∈ s, finite {i | x ∈ u i}) (hU : s ⊆ ⋃ i, u i) :
  partial_refinement u s :=
begin
  refine ⟨λ i, find c ne i i, chain_Sup_carrier c,
    λ i, (find _ _ _).is_open i,
    λ x hxs, mem_Union.2 _,
    λ i hi, (find c ne i).closure_subset ((mem_find_carrier_iff _).2 hi),
    λ i hi, (find c ne i).apply_eq (mt (mem_find_carrier_iff _).1 hi)⟩,
  rcases em (∃ i ∉ chain_Sup_carrier c, x ∈ u i) with ⟨i, hi, hxi⟩|hx,
  { use i,
    rwa (find c ne i).apply_eq (mt (mem_find_carrier_iff _).1 hi) },
  { simp_rw [not_exists, not_imp_not, chain_Sup_carrier, mem_bUnion_iff] at hx,
    haveI : nonempty (partial_refinement u s) := ⟨ne.some⟩,
    choose! v hvc hiv using hx,
    rcases (hfin x hxs).exists_maximal_wrt v _ (mem_Union.1 (hU hxs))
      with ⟨i, hxi : x ∈ u i, hmax : ∀ j, x ∈ u j → v i ≤ v j → v i = v j⟩,
    rcases mem_Union.1 ((v i).subset_Union hxs) with ⟨j, hj⟩,
    use j,
    have hj' : x ∈ u j := (v i).subset _ hj,
    have : v j ≤ v i,
      from (hc.total_of_refl (hvc _ hxi) (hvc _ hj')).elim (λ h, (hmax j hj' h).ge) id,
    rwa find_apply_of_mem hc ne (hvc _ hxi) (this.1 $ hiv _ hj') }
end

/-- `chain_Sup hu c hc ne hfin hU` is an upper bound of the chain `c`. -/
lemma le_chain_Sup {c : set (partial_refinement u s)} (hc : chain (≤) c)
  (ne : c.nonempty) (hfin : ∀ x ∈ s, finite {i | x ∈ u i}) (hU : s ⊆ ⋃ i, u i)
  {v} (hv : v ∈ c) :
  v ≤ chain_Sup c hc ne hfin hU :=
⟨λ i hi, mem_bUnion hv hi, λ i hi, (find_apply_of_mem hc _ hv hi).symm⟩

/-- If `s` is a closed set, `v` is a partial refinement, and `i` is an index such that
`i ∉ v.carrier`, then there exists a partial refinement that is strictly greater than `v`. -/
lemma exists_gt (v : partial_refinement u s) (hs : is_closed s) (i : ι) (hi : i ∉ v.carrier) :
  ∃ v' : partial_refinement u s, v < v' :=
begin
  have I : s ∩ (⋂ j ≠ i, (v j)ᶜ) ⊆ v i,
  { simp only [subset_def, mem_inter_eq, mem_Inter, and_imp],
    intros x hxs H,
    rcases mem_Union.1 (v.subset_Union hxs) with ⟨j, hj⟩,
    exact (em (j = i)).elim (λ h, h ▸ hj) (λ h, (H j h hj).elim) },
  have C : is_closed (s ∩ (⋂ j ≠ i, (v j)ᶜ)),
    from is_closed.inter hs (is_closed_bInter $ λ _ _, is_closed_compl_iff.2 $ v.is_open _),
  rcases normal_exists_closure_subset C (v.is_open i) I with ⟨vi, ovi, hvi, cvi⟩,
  refine ⟨⟨update v i vi, insert i v.carrier, _, _, _, _⟩, _, _⟩,
  { intro j, by_cases h : j = i; simp [h, ovi, v.is_open] },
  { refine λ x hx, mem_Union.2 _,
    rcases em (∃ j ≠ i, x ∈ v j) with ⟨j, hji, hj⟩|h,
    { use j, rwa update_noteq hji },
    { push_neg at h, use i, rw update_same, exact hvi ⟨hx, mem_bInter h⟩ } },
  { rintro j (rfl|hj),
    { rwa [update_same, ← v.apply_eq hi] },
    { rw update_noteq (ne_of_mem_of_not_mem hj hi), exact v.closure_subset hj } },
  { intros j hj,
    rw [mem_insert_iff, not_or_distrib] at hj,
    rw [update_noteq hj.1, v.apply_eq hj.2] },
  { refine ⟨subset_insert _ _, λ j hj, _⟩,
    exact (update_noteq (ne_of_mem_of_not_mem hj hi) _ _).symm },
  { exact λ hle, hi (hle.1 $ mem_insert _ _) }
end

end partial_refinement

end shrinking_lemma

open shrinking_lemma

variables {u : ι → set X} {s : set X}

/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new open cover so that the closure of each new open set is contained in the corresponding
original open set. -/
lemma exists_subset_Union_closure_subset (hs : is_closed s) (uo : ∀ i, is_open (u i))
  (uf : ∀ x ∈ s, finite {i | x ∈ u i}) (us : s ⊆ ⋃ i, u i) :
  ∃ v : ι → set X, s ⊆ Union v ∧ (∀ i, is_open (v i)) ∧ ∀ i, closure (v i) ⊆ u i :=
begin
  classical,
  haveI : nonempty (partial_refinement u s) := ⟨⟨u, ∅, uo, us, λ _, false.elim, λ _ _, rfl⟩⟩,
  have : ∀ c : set (partial_refinement u s), chain (≤) c → c.nonempty → ∃ ub, ∀ v ∈ c, v ≤ ub,
    from λ c hc ne, ⟨partial_refinement.chain_Sup c hc ne uf us,
      λ v hv, partial_refinement.le_chain_Sup _ _ _ _ hv⟩,
  rcases zorn_nonempty_partial_order this with ⟨v, hv⟩,
  suffices : ∀ i, i ∈ v.carrier,
    from ⟨v, v.subset_Union, λ i, v.is_open _, λ i, v.closure_subset (this i)⟩,
  contrapose! hv,
  rcases hv with ⟨i, hi⟩,
  rcases v.exists_gt hs i hi with ⟨v', hlt⟩,
  exact ⟨v', hlt.le, hlt.ne'⟩
end

/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new closed cover so that each new closed set is contained in the corresponding original open
set. See also `exists_subset_Union_closure_subset` for a stronger statement. -/
lemma exists_subset_Union_closed_subset (hs : is_closed s) (uo : ∀ i, is_open (u i))
  (uf : ∀ x ∈ s, finite {i | x ∈ u i}) (us : s ⊆ ⋃ i, u i) :
  ∃ v : ι → set X, s ⊆ Union v ∧ (∀ i, is_closed (v i)) ∧ ∀ i, v i ⊆ u i :=
let ⟨v, hsv, hvo, hv⟩ := exists_subset_Union_closure_subset hs uo uf us
in ⟨λ i, closure (v i), subset.trans hsv (Union_subset_Union $ λ i, subset_closure),
  λ i, is_closed_closure, hv⟩

/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new open cover so that the closure of each new open set is contained in the corresponding
original open set. -/
lemma exists_Union_eq_closure_subset (uo : ∀ i, is_open (u i)) (uf : ∀ x, finite {i | x ∈ u i})
  (uU : (⋃ i, u i) = univ) :
  ∃ v : ι → set X, Union v = univ ∧ (∀ i, is_open (v i)) ∧ ∀ i, closure (v i) ⊆ u i :=
let ⟨v, vU, hv⟩ := exists_subset_Union_closure_subset is_closed_univ uo (λ x _, uf x) uU.ge
in ⟨v, univ_subset_iff.1 vU, hv⟩

/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new closed cover so that each of the new closed sets is contained in the corresponding
original open set. See also `exists_Union_eq_closure_subset` for a stronger statement. -/
lemma exists_Union_eq_closed_subset (uo : ∀ i, is_open (u i)) (uf : ∀ x, finite {i | x ∈ u i})
  (uU : (⋃ i, u i) = univ) :
  ∃ v : ι → set X, Union v = univ ∧ (∀ i, is_closed (v i)) ∧ ∀ i, v i ⊆ u i :=
let ⟨v, vU, hv⟩ := exists_subset_Union_closed_subset is_closed_univ uo (λ x _, uf x) uU.ge
in ⟨v, univ_subset_iff.1 vU, hv⟩
