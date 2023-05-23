/-
Copyright © 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import geometry.manifold.local_invariant_properties
import topology.sheaves.local_predicate

/-! # Generic construction of a sheaf from a `local_invariant_prop` on a manifold -/

open_locale manifold topological_space
open set topological_space structure_groupoid structure_groupoid.local_invariant_prop opposite

variables {H : Type*} [topological_space H]
  {H' : Type*} [topological_space H']
  {G : structure_groupoid H} [closed_under_restriction G] {G' : structure_groupoid H'}
  (M : Type) [topological_space M] [charted_space H M] [has_groupoid M G]
  (M' : Type) [topological_space M'] [charted_space H' M'] [has_groupoid M' G']
  {P : (H → H') → (set H) → H → Prop}

instance Top.of.charted_space : charted_space H (Top.of M) := (infer_instance : charted_space H M)

instance Top.of.has_groupoid : has_groupoid (Top.of M) G := (infer_instance : has_groupoid M G)

namespace structure_groupoid.local_invariant_prop
variables {M M'}

lemma foo₁ (hG : local_invariant_prop G G' P) {U V : opens (Top.of M)} {i : U ⟶ V} {f : V → M'}
  {x : U} :
  continuous_within_at f univ (i x) ↔ continuous_within_at (f ∘ i) univ x :=
begin
  simp only [continuous_within_at_univ],
  have hUV : U ≤ V := category_theory.le_of_hom i,
  split,
  { intro h,
    exact h.comp (continuous_inclusion hUV).continuous_at },
  { intro h,
    have hi : open_embedding i := topological_space.opens.open_embedding_of_le hUV,
    simpa [hi.continuous_at_iff] using h }
end

lemma foo₂ (hG : local_invariant_prop G G' P) {U V : opens (Top.of M)} {i : U ⟶ V} {f : V → M'}
  (e : M' →H') {x : U} :
  P (e ∘ f ∘ (chart_at H (i x)).symm) univ (chart_at H (i x) (i x))
  ↔ P (e ∘ (f ∘ i) ∘ ((chart_at H x).symm)) univ (chart_at H x x) :=
begin
  haveI : nonempty U := ⟨x⟩,
  haveI : nonempty V := ⟨i x⟩,
  set e' := chart_at H x.val,
  apply hG.congr_iff,
  apply filter.eventually_eq_of_mem,
  apply (e'.subtype_restr U).symm.open_source.mem_nhds,
  { show e' x ∈ (e'.subtype_restr U).symm.source,
    sorry },
  { show ∀ y ∈ (e'.subtype_restr U).symm.source,
      e (f ((e'.subtype_restr V).symm y)) = e (f (i ((e'.subtype_restr U).symm y))),
    sorry },
end

lemma foo (hG : local_invariant_prop G G' P) {U V : opens (Top.of M)} {i : U ⟶ V} {f : V → M'}
  {x : U} :
  lift_prop_at P f (i x) ↔ lift_prop_at P (f ∘ i) x :=
⟨λh, ⟨(foo₁ hG).1 h.1, (foo₂ hG _).1 h.2⟩, λh, ⟨(foo₁ hG).2 h.1, (foo₂ hG _).2 h.2⟩⟩

end structure_groupoid.local_invariant_prop

/-- Let `M`, `M'` be charted spaces with transition functions in the groupoids `G`, `G'`, and let
`P` be a `local_invariant_prop` for functions between spaces with these groupoids.  Then there is an
induced `local_predicate` for the sheaf of functions from `M` to `M'`. -/
def local_predicate_of_local_invariant_prop (hG : local_invariant_prop G G' P) :
  Top.local_predicate (λ (x : Top.of M), M') :=
{ pred := λ {U : opens (Top.of M)}, λ (f : U → M'), lift_prop P f,
  res := begin
    intros U V i f h x,
    exact hG.foo.1 (h (i x)),
  end,
  locality := begin
    intros V f h x,
    obtain ⟨U, hxU, i, hU : lift_prop P (f ∘ i)⟩ := h x,
    let x' : U := ⟨x, hxU⟩,
    convert hG.foo.2 (hU x'),
    ext1,
    refl
  end }

def structure_groupoid.local_invariant_prop.sheaf (hG : local_invariant_prop G G' P) :
  Top.sheaf Type (Top.of M) :=
Top.subsheaf_to_Types (local_predicate_of_local_invariant_prop M M' hG)

instance (hG : local_invariant_prop G G' P) (U : (opens (Top.of M))ᵒᵖ) :
  has_coe_to_fun ((hG.sheaf M M').val.obj U) (λ _, (unop U) → M') :=
{ coe := λ a, a.1 }
