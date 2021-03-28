import category_theory.model_categories.arrow_classes
import category_theory.limits.preserves.shapes.terminal
import category_theory.model_categories.weak_factorization_system

namespace category_theory

universes v v' u u'

namespace category_theory

open category_theory

variables {M : Type u} [category.{v} M]
variables {D : Type u'} [category.{v'} D]

/-- A model category is a finitely bicomplete category together with three distinguished
arrow classes. The weak equivalences `W` need to satisfy the 2-out-of-3-condition,
and `C` vs. `W ∩ F` as well as `W ∩ C` vs. `F` need to be weak factorization systems.  -/
structure model_structure (M : Type u) [category.{v} M]:=
  (finite_lim : limits.has_finite_limits M)
  (finite_colim : limits.has_finite_colimits M)
  (W C F : arrow_cond M)
  (W_23 : two_out_of_three W)
  (weak_factorization_system_C_WF : weak_factorization_system C (W ∩ F))
  (weak_factorization_system_WC_F : weak_factorization_system (W ∩ C) F)

/-- An object `X` is cofibrant if any arrow from an initial object to `X` is a cofibration. -/
def cofibrant (R : model_structure M) (X : M) : Prop :=
  ∀ i : arrow M, category_theory.limits.is_initial i.left → R.C i

def cofibrant_source (R : model_structure M) : arrow_cond M :=
  λ i, (cofibrant R i.left)

def cofibrant_target (R : model_structure M) : arrow_cond M :=
  λ i, (cofibrant R i.right)

/-- An object `X` is fibrant if any arrow from `X` to a terminal object is a fibration. -/
def fibrant {R : model_structure M} (X : M) : Prop :=
  ∀ i : arrow M, category_theory.limits.is_terminal i.right → R.F i


/-- Brown's lemma: Given a functor `F: C ⥤ D` from a model category to a category equipped with
weak equivalences, such that `F` maps cofibrations with cofibrant source to weak equivalences,
then it sends weak equivalences between cofibrant objects to weak equivalences. -/
theorem browns_lemma {F : M ⥤ D} {R : model_structure M}
  {W' : arrow_cond D} {W'_23 : two_out_of_three W'} :
  (cofibrant_source R) ∩ R.C ⊆ arrow_cond.preimage F W' →
  (cofibrant_source R) ∩ (cofibrant_target R) ⊆ arrow_cond.preimage F W' :=
begin
  intro hyp,
  intros f hf,
  sorry
end

end category_theory

end category_theory
