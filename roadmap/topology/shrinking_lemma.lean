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

open set zorn
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

structure partial_refinement (u : ι → set X) :=
(to_fun : ι → set X)
(mem_base' : ∀ i, to_fun i ∈ B i)
(carrier : set ι)
(Union_eq' : (⋃ i, to_fun i) = univ)
(closure_subset' : ∀ i ∈ carrier, closure (to_fun i) ⊆ u i)
(apply_eq' : ∀ i ∉ carrier, to_fun i = u i)

namespace partial_refinement

instance (u : ι → set X) : has_coe_to_fun (B.partial_refinement u) :=
⟨_, to_fun⟩

variables {B} {u : ι → set X}

lemma mem_base (v : partial_refinement B u) (i : ι) : v i ∈ B i := v.mem_base' i

lemma Union_eq (v : partial_refinement B u) : (⋃ i, v i) = univ := v.Union_eq'

lemma closure_subset (v : partial_refinement B u) {i : ι} (hi : i ∈ v.carrier) :
  closure (v i) ⊆ u i :=
v.closure_subset' i hi

lemma apply_eq (v : partial_refinement B u) {i : ι} (hi : i ∉ v.carrier) : v i = u i :=
v.apply_eq' i hi

attribute [ext] partial_refinement

instance : partial_order (partial_refinement B u) :=
{ le := λ v₁ v₂, v₁.carrier ⊆ v₂.carrier ∧ ∀ i ∈ v₁.carrier, v₁ i = v₂ i,
  le_refl := λ v, ⟨subset.refl _, λ _ _, rfl⟩,
  le_trans := λ v₁ v₂ v₃ h₁₂ h₂₃,
    ⟨subset.trans h₁₂.1 h₂₃.1, λ i hi, (h₁₂.2 i hi).trans (h₂₃.2 i $ h₁₂.1 hi)⟩,
  le_antisymm := λ v₁ v₂ h₁₂ h₂₁,
    have hc : v₁.carrier = v₂.carrier, from subset.antisymm h₁₂.1 h₂₁.1,
    ext _ _ (funext $ λ x,
      if hx : x ∈ v₁.carrier then h₁₂.2 _ hx
      else (v₁.apply_eq hx).trans (eq.symm $ v₂.apply_eq $ hc ▸ hx)) hc }

lemma apply_eq_of_chain {c : set (partial_refinement B u)} (hc : chain (≤) c) {v₁ v₂}
  (h₁ : v₁ ∈ c) (h₂ : v₂ ∈ c) {i} (hi : i ∈ v₁.carrier ↔ i ∈ v₂.carrier) :
  v₁ i = v₂ i :=
begin
  wlog hle : v₁ ≤ v₂ := hc.total_of_refl h₁ h₂ using [v₁ v₂, v₂ v₁],
  by_cases hi₁ : i ∈ v₁.carrier,
  { exact hle.2 _ hi₁ },
  { rw [v₁.apply_eq hi₁, v₂.apply_eq (mt hi.mpr hi₁)] }
end

def chain_Sup_carrier (c : set (partial_refinement B u)) : set ι :=
⋃ v ∈ c, carrier v

lemma chain_Sup_cases (c : set (partial_refinement B u)) (i : ι) :
  (∃ v ∈ c, i ∈ carrier v) ∨ i ∉ chain_Sup_carrier c :=
by simpa only [chain_Sup_carrier, mem_Union] using em (i ∈ chain_Sup_carrier c)

def find (c : set (partial_refinement B u)) (i : ι) (hi : i ∈ chain_Sup_carrier c) :
  partial_refinement B u :=
(mem_bUnion_iff.1 hi).some

lemma find_mem {c : set (partial_refinement B u)} {i : ι} (hi : i ∈ chain_Sup_carrier c) :
  find c i hi ∈ c :=
(mem_bUnion_iff.1 hi).some_spec.fst

lemma mem_find_carrier {c : set (partial_refinement B u)} {i : ι} (hi : i ∈ chain_Sup_carrier c) :
  i ∈ (find c i hi).carrier :=
(mem_bUnion_iff.1 hi).some_spec.snd

def chain_Sup_fun (c : set (partial_refinement B u)) (i : ι) : set X :=
if hi : i ∈ chain_Sup_carrier c then find c i hi i else u i

/-
lemma chain_Sup_fun_of_mem {c : set (partial_refinement B u)} (hc : chain (≤) c)
  {i : ι} {v : partial_refinement B u} (hvc : v ∈ c) (hiv : i ∈ v.carrier) :
  chain_Sup_fun c i = v i :=
begin
  have : ∃ v ∈ c, i ∈ carrier v, from ⟨v, hvc, hiv⟩,
  rw [chain_Sup_fun, dif_pos this],
  refine apply_eq_of_chain hc this.some_spec.fst hvc _,
  have := this.some_spec.snd,
  simp only [hiv, this]
end-/

lemma chain_Sup_of_not_mem {c : set (partial_refinement B u)} {i : ι}
  (h : i ∉ chain_Sup_carrier c) : chain_Sup_fun c i = u i :=
dif_neg h

def chain_Sup (hu : ∀ i, u i ∈ B i) (c : set (partial_refinement B u)) (hc : chain (≤) c) :
  partial_refinement B u :=
begin
  refine ⟨chain_Sup_fun c, λ i, _, chain_Sup_carrier c, _, _, _⟩,
  { rcases chain_Sup_cases c i with ⟨v, hvc, hiv⟩|hi,
    { rw [chain_Sup_fun_of_mem hc hvc hiv], exact v.mem_base i },
    { rw [chain_Sup_of_not_mem hi], exact hu i } },
  { sorry },
  {  }
end

end partial_refinement

/-- A point-finite open cover of a closed subset of a normal space can be "shrunk" to a new open
cover so that the closure of each new open set is contained in the corresponding original open
set. -/
lemma shrinking_lemma {X : Type u} [topological_space X] [normal_space X]
  {s : set X} (hs : is_closed s) {α : Type v} (u : α → set X) (uo : ∀ a, is_open (u a))
  (uf : ∀ x, finite {a | x ∈ u a}) (su : s ⊆ Union u) :
  ∃ v : α → set X, s ⊆ Union v ∧ ∀ a, is_open (v a) ∧ closure (v a) ⊆ u a :=
begin
  classical,
  set T := Σ t : set α, {v : α → set X // s ⊆ Union v ∧ (∀ a, is_open (v a)) ∧
    (∀ a ∈ t, closure (v a) ⊆ u a) ∧ (∀ a ∉ t, v a = u a)},
  set r : T → T → Prop := λ tv tv', tv.1 ⊆ tv'.1 ∧ ∀ a ∈ tv.1, tv.2.1 a = tv'.2.1 a,
  haveI : is_refl T r := ⟨λ tv, ⟨subset.refl _, λ a ha, rfl⟩⟩,
  have eq_of_chain : ∀ {c} (hc : chain r c) {tv tv' : T} (h : tv ∈ c) (h' : tv' ∈ c)
    {a} (ha : a ∈ tv.1) (ha' : a ∈ tv'.1), tv.2.1 a = tv'.2.1 a,
  { intros c hc tv tv' h h' a ha ha',
    rcases hc.total_of_refl h h' with (h|h'),
    exacts [h.2 _ ha, (h'.2 _ ha').symm] },
  have r_chain : ∀ c, chain r c → ∃ ub, ∀ a ∈ c, r a ub,
  { intros c hc,
    set I : set α := ⋃ tv ∈ c, sigma.fst tv,
    set v : α → set X := λ a, if h : a ∈ I  then (mem_bUnion_iff.1 h).some.2.1 a else u a,
    have v_of_mem : ∀ (tv : T) (htv : tv ∈ c) (a ∈ tv.1), v a = tv.2.1 a,
    { intros tv htv a ha,
      have : a ∈ I, from mem_bUnion htv ha,
      simp only [v], rw [dif_pos this],
      exact eq_of_chain hc (mem_bUnion_iff.1 this).some_spec.fst htv
        (mem_bUnion_iff.1 this).some_spec.snd ha },
    have v_of_not_mem : ∀ a ∉ I, v a = u a, from λ a ha, dif_neg ha,
    have mem_cases : ∀ a, (∃ (tv : T) (htv : tv ∈ c), a ∈ tv.1) ∨ a ∉ I,
    { refine λ a, (em (a ∈ I)).imp _ id, simp only [I, mem_Union], exact id },
    refine ⟨⟨I, ⟨v, _, _, _, _⟩⟩, _⟩,
    { sorry },
    { intro a,  },
    { intros a ha,
      simp only [v], rw dif_pos ha,
      exact (mem_bUnion_iff.1 ha).some.2.2.2.2.1 _ (mem_bUnion_iff.1 ha).some_spec.snd },
    { intros a ha, simp only [v], rw dif_neg ha },
    { intros tv htv,
      have hsub : tv.fst ⊆ I, from subset_bUnion_of_mem htv,
      refine ⟨hsub, λ a ha, _⟩,
      simp only [v], rw [dif_pos],
       } }
end

/-
Apply Zorn's lemma to
 T = Σ (i : set α), {v : α → set X // s ⊆ Union v ∧ (∀ a, is_open (v a)) ∧
                                      (∀ a ∈ i, closure (v a) ⊆ u a) ∧ (∀ a ∉ i, v a = u a)}
with the ordering
 ⟨i, v, _⟩ ≤ ⟨i', v', _⟩ ↔ i ⊆ i' ∧ ∀ a ∈ i, v a = v' a
The hypothesis that `X` is normal implies that a maximal element must have `i = univ`.
Point-finiteness of `u` (hypothesis `uf`) implies that
the least upper bound of a chain in `T` again yields a covering of `s`.

Compare proofs in
* https://ncatlab.org/nlab/show/shrinking+lemma#ShrinkingLemmaForLocallyFiniteCountableCovers
* Bourbaki, General Topology, Chapter IX, §4.3
* Dugundji, Topology, Chapter VII, Theorem 6.1
-/
--434611
