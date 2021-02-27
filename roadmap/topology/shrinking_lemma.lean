/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/

import ..todo
import topology.separation

/-!
A formal roadmap for the shrinking lemma for local finite countable covers.

It contains the statement of the lemma, and an informal sketch of the proof,
along with references.

Any contributor should feel welcome to contribute a formal proof. When this happens,
we should also consider preserving the current file as an exemplar of a formal roadmap.
-/

open set zorn function
open_locale classical
noncomputable theory

universes u v

structure shrinking_lemma_data (ι X : Type*) [topological_space X] :=
(to_fun : ι → set (set X))
(is_open' : ∀ i (s ∈ to_fun i), is_open s)
(exists_shrink' : ∀ i (s ∈ to_fun i) t, is_open t → s ∪ t = univ →
  ∃ s' ∈ to_fun i, closure s' ⊆ s ∧ s' ∪ t = univ)

namespace shrinking_lemma_data

def of_normal (ι X : Type*) [topological_space X] [normal_space X] :
  shrinking_lemma_data ι X :=
{ to_fun := λ _, {s | is_open s},
  is_open' := λ _ s, id,
  exists_shrink' := λ _ s hs t ht, by simpa only [exists_prop] using normal_shrink_left hs ht }

variables {ι X : Type*} [topological_space X] (B : shrinking_lemma_data ι X)

instance : has_coe_to_fun (shrinking_lemma_data ι X) := ⟨_, to_fun⟩

protected lemma is_open {i : ι} {s : set X} (h : s ∈ B i) : is_open s :=
B.is_open' _ _ h

lemma exists_shrink {i : ι} {s t : set X} (hs : s ∈ B i) (ht : is_open t) (h : s ∪ t = univ) :
  ∃ s' ∈ B i, closure s' ⊆ s ∧ s' ∪ t = univ :=
B.exists_shrink' _ _ hs _ ht h

structure partial_refinement (u : ι → set X) (s : set X) :=
(to_fun : ι → set X)
(mem_base' : ∀ i, to_fun i ∈ B i)
(carrier : set ι)
(subset_Union' : s ⊆ ⋃ i, to_fun i)
(closure_subset' : ∀ i ∈ carrier, closure (to_fun i) ⊆ u i)
(apply_eq' : ∀ i ∉ carrier, to_fun i = u i)

namespace partial_refinement

instance (u : ι → set X) (s : set X) : has_coe_to_fun (B.partial_refinement u s) :=
⟨_, to_fun⟩

variables {B} {u : ι → set X} {s : set X}

lemma mem_base (v : partial_refinement B u s) (i : ι) : v i ∈ B i := v.mem_base' i

lemma subset_Union (v : partial_refinement B u s) : s ⊆ ⋃ i, v i := v.subset_Union'

lemma closure_subset (v : partial_refinement B u s) {i : ι} (hi : i ∈ v.carrier) :
  closure (v i) ⊆ u i :=
v.closure_subset' i hi

lemma apply_eq (v : partial_refinement B u s) {i : ι} (hi : i ∉ v.carrier) : v i = u i :=
v.apply_eq' i hi

lemma subset (v : partial_refinement B u s) (i : ι) : v i ⊆ u i :=
if h : i ∈ v.carrier then subset.trans subset_closure (v.closure_subset h)
else (v.apply_eq h).le

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

lemma apply_eq_of_chain {c : set (partial_refinement B u s)} (hc : chain (≤) c) {v₁ v₂}
  (h₁ : v₁ ∈ c) (h₂ : v₂ ∈ c) {i} (hi₁ : i ∈ v₁.carrier) (hi₂ : i ∈ v₂.carrier) :
  v₁ i = v₂ i :=
begin
  wlog hle : v₁ ≤ v₂ := hc.total_of_refl h₁ h₂ using [v₁ v₂, v₂ v₁],
  exact hle.2 _ hi₁,
end

def chain_Sup_carrier (c : set (partial_refinement B u s)) : set ι :=
⋃ v ∈ c, carrier v

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

def chain_Sup (hu : ∀ i, u i ∈ B i) (c : set (partial_refinement B u s)) (hc : chain (≤) c)
  (ne : c.nonempty) (hfin : ∀ x ∈ s, finite {i | x ∈ u i}) (hU : s ⊆ ⋃ i, u i) :
  partial_refinement B u s :=
begin
  refine ⟨λ i, find c ne i i, λ i, (find c ne i).mem_base i, chain_Sup_carrier c,
    λ x hxs, mem_Union.2 _,
    λ i hi, (find c ne i).closure_subset ((mem_find_carrier_iff _).2 hi),
    λ i hi, (find c ne i).apply_eq (mt (mem_find_carrier_iff _).1 hi)⟩,
  rcases em (∃ i ∉ chain_Sup_carrier c, x ∈ u i) with ⟨i, hi, hxi⟩|hx,
  { use i,
    rwa (find c ne i).apply_eq (mt (mem_find_carrier_iff _).1 hi) },
  { simp_rw [not_exists, not_imp_not, chain_Sup_carrier, mem_bUnion_iff] at hx,
    haveI : nonempty (B.partial_refinement u s) := ⟨ne.some⟩,
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

lemma le_chain_Sup (hu : ∀ i, u i ∈ B i) {c : set (partial_refinement B u s)} (hc : chain (≤) c)
  (ne : c.nonempty) (hfin : ∀ x ∈ s, finite {i | x ∈ u i}) (hU : s ⊆ ⋃ i, u i)
  {v} (hv : v ∈ c) :
  v ≤ chain_Sup hu c hc ne hfin hU :=
⟨λ i hi, mem_bUnion hv hi, λ i hi, (find_apply_of_mem hc _ hv hi).symm⟩

lemma exists_gt (v : partial_refinement B u s) (hs : is_closed s) (i : ι) (hi : i ∉ v.carrier) :
  ∃ v' : partial_refinement B u s, v < v' :=
begin
  have O : is_open (⋃ j ≠ i, v j), from is_open_bUnion (λ j (hj : j ≠ i), B.is_open (v.mem_base _)),
  have U : v i ∪ (sᶜ ∪ ⋃ j ≠ i, v j) = univ,
  { refine eq_univ_of_forall (λ x, _),
    refine (em (x ∈ s)).elim (λ hs, _) (λ h, or.inr (or.inl h)),
    rcases mem_Union.1 (v.subset_Union hs) with ⟨j, hj⟩,
    exact (em (j = i)).elim (λ h, or.inl $ h ▸ hj) (λ hji, or.inr (or.inr $ mem_bUnion hji hj)) },
  rcases B.exists_shrink (v.mem_base i) (is_open_union (is_open_compl_iff.2 hs) O) U
    with ⟨vi, Bvi, cvi, hvi⟩,
  refine ⟨⟨update v i vi, _, insert i v.carrier, _, _, _⟩, _, _⟩,
  { intro j, by_cases hj : j = i; simp [hj, Bvi, v.mem_base] },
  { intros x hx,
    have := eq_univ_iff_forall.1 hvi x,
    simp only [mem_union, mem_compl, mem_Union] at this ⊢,
    rcases this with hxi|hxs|⟨j, hji, hj⟩,
    { use i, rwa update_same },
    { exact absurd hx hxs },
    { use j, rwa update_noteq hji } },
  { rintro j (rfl|hj),
    { rw update_same, exact subset.trans cvi (v.subset j) },
    { rw update_noteq (ne_of_mem_of_not_mem hj hi),
      exact v.closure_subset hj } },
  { intros j hj,
    rw [mem_insert_iff, not_or_distrib] at hj,
    rw [update_noteq hj.1, v.apply_eq hj.2] },
  { refine ⟨subset_insert _ _, λ j hj, _⟩,
    exact (update_noteq (ne_of_mem_of_not_mem hj hi) _ _).symm },
  { exact λ hle, hi (hle.1 $ mem_insert _ _) }
end

end partial_refinement

/-- A point-finite open cover of a closed subset of a normal space can be "shrunk" to a new open
cover so that the closure of each new open set is contained in the corresponding original open
set.

The proof is based on
https://ncatlab.org/nlab/show/shrinking+lemma#ShrinkingLemmaForLocallyFiniteCountableCovers -/
lemma shrinking_lemma_set (B : shrinking_lemma_data ι X)
  {s : set X} (hs : is_closed s) (u : ι → set X) (Bu : ∀ i, u i ∈ B i)
  (uf : ∀ x ∈ s, finite {i | x ∈ u i}) (su : s ⊆ Union u) :
  ∃ v : ι → set X, s ⊆ Union v ∧ ∀ i, v i ∈ B i ∧ closure (v i) ⊆ u i :=
begin
  classical,
  have : ∀ c : set (partial_refinement B u s), chain (≤) c → ∃ ub, ∀ v ∈ c, v ≤ ub,
  { intros c hc,
    rcases eq_empty_or_nonempty c with rfl|ne,
    { exact ⟨⟨u, Bu, ∅, su, λ _, false.elim, λ _ _, rfl⟩, λ _, false.elim⟩ },
    { exact ⟨partial_refinement.chain_Sup Bu c hc ne uf su,
        λ v hv, partial_refinement.le_chain_Sup _ _ _ _ _ hv⟩ } },
  rcases zorn_partial_order this with ⟨v, hv⟩,
  suffices : ∀ i, i ∈ v.carrier,
    from ⟨v, v.subset_Union, λ i, ⟨v.mem_base i, v.closure_subset (this i)⟩⟩,
  contrapose! hv,
  rcases hv with ⟨i, hi⟩,
  rcases v.exists_gt hs i hi with ⟨v', hlt⟩,
  exact ⟨v', hlt.le, hlt.ne'⟩
end

lemma shrinking_lemma (B : shrinking_lemma_data ι X) (u : ι → set X) (Bu : ∀ i, u i ∈ B i)
  (uf : ∀ x, finite {i | x ∈ u i}) (su : Union u = univ) :
  ∃ v : ι → set X, Union v = univ ∧ ∀ i, v i ∈ B i ∧ closure (v i) ⊆ u i :=
let ⟨v, vU, hv⟩ := B.shrinking_lemma_set is_closed_univ u Bu (λ x _, uf x) su.ge
in ⟨v, univ_subset_iff.1 vU, hv⟩

end shrinking_lemma_data

variables {ι X : Type*} [topological_space X] [normal_space X] {u : ι → set X} {s : set X}

/-- A point-finite open cover of a closed subset of a normal space can be "shrunk" to a new open
cover so that the closure of each new open set is contained in the corresponding original open
set. -/
lemma shrinking_lemma_set (hs : is_closed s) (uo : ∀ i, is_open (u i))
  (uf : ∀ x ∈ s, finite {i | x ∈ u i}) (us : s ⊆ ⋃ i, u i) :
  ∃ v : ι → set X, s ⊆ Union v ∧ ∀ i, is_open (v i) ∧ closure (v i) ⊆ u i :=
(shrinking_lemma_data.of_normal ι X).shrinking_lemma_set hs u uo uf us

/-- A point-finite open cover of a closed subset of a normal space can be "shrunk" to a new open
cover so that the closure of each new open set is contained in the corresponding original open
set. -/
lemma shrinking_lemma (uo : ∀ i, is_open (u i)) (uf : ∀ x, finite {i | x ∈ u i})
  (uU : (⋃ i, u i) = univ) :
  ∃ v : ι → set X, Union v = univ ∧ ∀ i, is_open (v i) ∧ closure (v i) ⊆ u i :=
(shrinking_lemma_data.of_normal ι X).shrinking_lemma u uo uf uU
