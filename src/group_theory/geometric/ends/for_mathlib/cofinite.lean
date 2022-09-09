import data.set.finite
import data.finset.basic

variables {V V' V'' : Type*}
local attribute [instance] classical.prop_decidable

open set finset

/--
A function is *cofinite* if the pre-image of every point is a finite set.

Equivalently, as proved below, a function is *cofinite* if the pre-image of every
finite set is finite.
-/
def cofinite (f : V → V') := ∀ x : V', (set.preimage f {x}).finite

lemma cofinite.list_preimage (f : V → V') (cof : cofinite f) : ∀ l : list V', (set.preimage f l.to_finset).finite :=
begin
  intro l,
  induction l,
  { simp only [list.to_finset_nil, coe_empty, set.preimage_empty, finite_empty], },
  { simp only [list.to_finset_cons, coe_insert],
    rw [set.insert_eq, set.preimage_union],
    apply set.finite.union,
    {apply cof,},
    {assumption,} }
end

/--
The preimage of a finite set under a *cofinite* map is finite.
-/
lemma cofinite.finite_preimage (f : V → V') (cof : cofinite f) : ∀ S : set V', S.finite → (set.preimage f S).finite :=
begin
  intros S Sfin,
  rcases set.finite.exists_finset_coe Sfin with ⟨fS, hcoefin⟩,
  rcases (list.to_finset_surjective fS) with ⟨l, hcoelst⟩,
  rw [← hcoefin, ← hcoelst],
  apply cofinite.list_preimage _ cof,
end

/--
A function is *cofinite* if and only if the pre-image of any finite set is finite.
-/
lemma cofinite.finite_preimage_iff (f : V → V') : cofinite f ↔ ∀ S : set V', S.finite → (set.preimage f S).finite :=
⟨cofinite.finite_preimage _, λ h x, h {x} (set.finite_singleton x)⟩

/-- The composition of cofinite maps is cofinite. -/
lemma cofinite.comp {f : V → V'} {f' : V' → V''} (cof : cofinite f) (cof' : cofinite f') : cofinite (f' ∘ f) :=
begin
  intro x,
  rw [set.preimage_comp],
  apply cofinite.finite_preimage _ cof,
  apply cof',
end

/-- The identity map is cofinite. -/
lemma cofinite.id : cofinite (@id V) := by {intro,simp only [set.preimage_id, finite_singleton]}
/-- An injective map is cofinite. -/
lemma cofinite.of_inj {f : V → V'} (inj : function.injective f) : cofinite f := by
{ intro,
  refine subsingleton.finite _,
  refine (function.injective.subsingleton_image_iff inj).mp _,
  tidy, } -- can we show it constructively?

/-- `cofinite.preimage` computes the preimage of a finite set under a cofinite map (as a `finset`). -/
noncomputable def cofinite.preimage {f : V → V'} (cof : cofinite f) (K : finset V') : finset V :=
set.finite.to_finset (cofinite.finite_preimage f cof K (finset.finite_to_set K))

/-- The value of `cofinite.preimage is the preimage of the cofinite function. -/
@[simp]
lemma cofinite.preimage.coe {f : V → V'} (cof : cofinite f) (K : finset V') : ↑(cof.preimage K) = set.preimage f K :=
begin
  show ↑(set.finite.to_finset (cofinite.finite_preimage f cof K (finset.finite_to_set K))) = f⁻¹' ↑K,
  simp,
end

/-- The direct image of an infinite set under a cofinite map is infinite. -/
lemma cofinite.image_infinite {f : V → V'} (cof : cofinite f) {S : set V} (Sinf : S.infinite) :
  (f '' S).infinite :=
begin
  intro hfin, apply Sinf,
  have := cofinite.finite_preimage _ cof _ hfin,
  refine finite.subset this _,
  exact subset_preimage_image f S,
end
