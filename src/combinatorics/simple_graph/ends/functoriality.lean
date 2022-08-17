import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition
import category_theory.filtered
import topology.category.Top.limits
import data.finset.basic
import category_theory.category.basic
import category_theory.full_subcategory
import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition
import set_theory.cardinal.basic
import data.fintype.basic
import data.opposite



import .mathlib
import .reachable_outside


open function
open finset
open category_theory
open set
open classical
open simple_graph.walk
open relation

universes u v w



noncomputable theory
local attribute [instance] prop_decidable


namespace inverse_system

variables {J : Type u} [preorder J] [is_directed J ge] (F : J ⥤ Type v)
variables {I : Type u} [preorder I] [is_directed I ge] (G : I ⥤ Type v)

-- Tried finding a suitable "general" notion, but it's probably misguided for now
def sections_map
  (φ : I → J)
  (ψ : Π i, F.obj (φ i) → G.obj i)
  --(∀ i : I, ∃ j ≤ φ i, )
  : F.sections → G.sections := sorry

end inverse_system

namespace simple_graph

variables  {V : Type u}
           (G : simple_graph V)
           {V' : Type v}
           (G' : simple_graph V')
           {V'' : Type w}
           (G'' : simple_graph V'')

namespace ends

open ro_component
open simple_graph

def cofinite (f : V → V') := ∀ x : V', (set.preimage f {x}).finite

lemma cofinite.list_preimage (f : V → V') (cof : cofinite f) : ∀ l : list V', (set.preimage f l.to_finset).finite :=
begin
  intro l,
  induction l,
  { simp, },
  { simp, rw [set.insert_eq, set.preimage_union],
    apply set.finite.union,
    {apply cof,},
    {assumption,} }
end

lemma cofinite.finite_preimage (f : V → V') (cof : cofinite f) : ∀ S : set V', S.finite → (set.preimage f S).finite :=
begin
  intros S Sfin,
  rcases set.finite.exists_finset_coe Sfin with ⟨fS, hcoefin⟩,
  rcases (list.to_finset_surjective fS) with ⟨l, hcoelst⟩,
  rw [← hcoefin, ← hcoelst],
  apply cofinite.list_preimage _ cof,
end

lemma cofinite.finite_preimage_iff (f : V → V') : cofinite f ↔ ∀ S : set V', S.finite → (set.preimage f S).finite :=
⟨cofinite.finite_preimage _, λ h x, h {x} (set.finite_singleton x)⟩

lemma cofinite.comp {f : V → V'} {f' : V' → V''} (cof : cofinite f) (cof' : cofinite f') : cofinite (f' ∘ f) :=
begin
  intro x,
  rw [set.preimage_comp],
  apply cofinite.finite_preimage _ cof,
  apply cof',
end

lemma cofinite.id : cofinite (@id V) := by {intro,simp}


def cofinite.preimage {f : V → V'} (cof : cofinite f) (K : finset V') : finset V :=
set.finite.to_finset (cofinite.finite_preimage f cof K (finset.finite_to_set K))

lemma cofinite.preimage.coe {f : V → V'} (cof : cofinite f) (K : finset V') : ↑(cof.preimage K) = set.preimage f K :=
begin
  show ↑(set.finite.to_finset (cofinite.finite_preimage f cof K (finset.finite_to_set K))) = f⁻¹' ↑K,
  simp,
end

def good_finset (f : V → V') (cof : cofinite f) (K : finset V') :=
  {L : finset V | cofinite.preimage cof K ⊆ L
                ∧ ∀ D : inf_ro_components G L, ∃! C : inf_ro_components G' K, f '' D ⊆ C}

structure coarse :=
  (to_fun : V → V')
  (cof : cofinite to_fun)
  (coarse : ∀ (K : finset V'), good_finset G G' to_fun cof K)

def close (f g : coarse G G') :=
  ∀ (K : finset V') (L : good_finset G G' f.to_fun f.cof K) (M : good_finset G G' f.to_fun f.cof K),
    ∃ N : finset V, ↑L ⊆ N ∧ ↑M ⊆ N
                  ∧ ∀ D : inf_ro_components G N,
                    ∃! C : inf_ro_components G' K, f.to_fun '' D ⊆ C ∧ g.to_fun '' D ⊆ C


/-
  Any map which is cofinite and coarsely Lipschitz
  (in the case for graphs, this means simply ∃m, ∀ (u v), G.adj u v → dist (f u) (f v) ≤ m)
  is coarse in the present sense.
  So, assume f is coarsely Lipschitz with constant m as above, and cofinite.
  Given K, we must find a good_finset L for K.
  We choose `K' = {x : V | exists k : K, d k x ≤ m}`, i.e. the m-neighborhood of K, and `L := f⁻¹ K'`
  Now, clearly f '' L contains K.
  Fix D an infinite ro component for L, since D does not intersect L, f '' D does not intersect K'.
  Thus, f '' D is contained in the union of all ro components for K', and a fortiori for K.
  If f '' D is entirely contained in one such C, then C must be infinite, since f '' D is infinite (f being cofinite and D infinite).
  It remains to check that f '' D really is contained in one such C.
  Assume that f '' D intersects C and C' (assumed unequal). Since D is connected, f '' D is "m-connected" in the sense that
  any two elements of f '' D can be joined by a sequence of elements of f '' D each at a distance at most k from its successor/predecessor.
  Fix c ∈ C ∩ (f '' D) and c' ∈ C' ∩ (f '' D) and take such an "m-path" c = c₀ , c₁ , …, cₙ = c'.
  There is a last cᵢ contained in C, and necessarily cᵢ₊₁ is not contained in C, and not in K either, thus
  wlog is contained in C'.
  In summary, we have some c ∈ C ∩ (f'' D) and c' ∈ C' ∩ (f'' D) joined by a path w of length at most m.
  Then w must pass through K, since otherwise we'd have a path outside of K joining C and C', hence they would be equal ro components.
  But now note that c c' ∉ K', obviously, meaning that c and c' are "far" from K, and the existence of this path w intersecting K is a contradiction.


-/

def qi_embedding (f : V → V') : Prop := sorry -- ∃ (K : ℕ), ∀ (u v : V), dist (f u) (f v) ≤ K * (dist u v) + K ∧ dist u v ≤ K * (dist (f u) (f v)) + K

def coarse.of_qi_embedding (f : V → V') (qie : qi_embedding f) : coarse G G' f := sorry

def coarse.comp {f : V → V'} {f' : V' → V''} (coa : coarse G G' f) (coa' : coarse G' G'' f') : coarse G G'' (f' ∘ f) := sorry

def ends_map {f : V → V'} (coa : coarse G G' f) : @ends V G → @ends V' G' := sorry



end ends

end simple_graph
