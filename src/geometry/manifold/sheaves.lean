import geometry.manifold.local_invariant_properties
import topology.sheaves.local_predicate

noncomputable theory
open_locale classical manifold topological_space

open set topological_space
open structure_groupoid
open structure_groupoid.local_invariant_prop

variables {H : Type*} {M : Type} [topological_space H] [topological_space M] [charted_space H (Top.of M)]
{H' : Type*} {M' : Type} [topological_space H'] [topological_space M'] [charted_space H' M']
variables (G : structure_groupoid H) (G' : structure_groupoid H')
variables (P : (H → H') → (set H) → H → Prop)

/-- Extension of a function defined on a subtype `U ⊆ M` to a function on `M`, by taking the junk
value `default M'` outside `U`. Rather general-purpose; where in mathlib should this live? -/
def extend [inhabited M'] (U : set M) (f : U → M') : M → M' :=
λ x, if h : x ∈ U then f ⟨x, h⟩ else default M'

/-- Let `M`, `M'` be charted spaces with transition functions in the groupoids `G`, `G'`, and let
`P` be a `local_invariant_prop` for functions between spaces with these groupoids.  Then there is an
induced `local_predicate` for the sheaf of functions from `M` to `M'`. -/
def local_predicate_of_local_invariant_prop [inhabited M'] (hG : local_invariant_prop G G' P) :
  Top.local_predicate (λ (x : Top.of M), M') :=
{ pred := λ {U : opens (Top.of M)}, λ (f : U → M'),
    ∀ (x : M), x ∈ U → lift_prop_at P (extend U.1 f) x,
  res := begin
    intros U V i f h x hx,
    have hUV : U ≤ V := category_theory.le_of_hom i,
    refine lift_prop_at_congr_of_eventually_eq hG (h x (hUV hx)) _,
    refine filter.eventually_eq_of_mem (mem_nhds_sets U.2 hx) _,
    intros y hy,
    unfold extend,
    rw dif_pos hy,
    rw dif_pos (hUV hy),
    refl,
  end,
  locality := begin
    intros V f h x hx,
    rcases h ⟨x, hx⟩ with ⟨U, hx, i, hU⟩,
    have hUV : U ≤ V := category_theory.le_of_hom i,
    refine lift_prop_at_congr_of_eventually_eq hG (hU x hx) _,
    refine filter.eventually_eq_of_mem (mem_nhds_sets U.2 hx) _,
    intros y hy,
    unfold extend,
    rw dif_pos hy,
    rw dif_pos (hUV hy),
    refl,
  end }
