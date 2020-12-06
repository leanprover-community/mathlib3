/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import category_theory.sites.canonical
import category_theory.sites.sheaf

/-!
# Grothendieck Topology and Sheaves on the Category of Types

In this file we define a grothendieck topology on the category of types,
and construct the canonical function that sends a type to a sheaf over
the category of types.
-/

universe u

namespace category_theory

/-- A Grothendieck topology associated to the category of all types.
A sieve is a covering iff it is jointly surjective. -/
def types_grothendieck_topology : grothendieck_topology (Type u) :=
{ sieves := λ α S, ∀ x : α, S (λ _ : punit, x),
  top_mem' := λ α x, trivial,
  pullback_stable' := λ α β S f hs x, hs (f x),
  transitive' := λ α S hs R hr x, hr (hs x) punit.star }

/-- The discrete sieve on a type, which only includes arrows whose image is a subsingleton. -/
def discrete_sieve (α : Type u) : sieve α :=
{ arrows := λ β f, ∃ x, ∀ y, f y = x,
  downward_closed' := λ β γ f ⟨x, hx⟩ g, ⟨x, λ y, hx $ g y⟩ }

lemma discrete_sieve_mem (α : Type u) : discrete_sieve α ∈ types_grothendieck_topology α :=
λ x, ⟨x, λ y, rfl⟩

/-- The discrete presieve on a type, which only includes arrows whose domain is a singleton. -/
def discrete_presieve (α : Type u) : presieve α :=
λ β f, ∃ x : β, ∀ y : β, y = x

lemma generate_discrete_presieve_mem (α : Type u) :
  sieve.generate (discrete_presieve α) ∈ types_grothendieck_topology α :=
λ x, ⟨punit, id, λ _, x, ⟨punit.star, λ _, subsingleton.elim _ _⟩, rfl⟩

namespace presieve

theorem is_sheaf_yoneda' {α : Type u} : is_sheaf types_grothendieck_topology (yoneda.obj α) :=
λ β S hs x hx, ⟨λ y, x _ (hs y) punit.star,
λ γ f h, funext $ λ z : γ,
  have _ := congr_fun (hx (𝟙 _) (λ _ : punit, z) (hs $ f z) h rfl) punit.star,
  by { convert this, exact rfl },
λ (f : β → α) hf, funext $ λ y : β, have _ := congr_fun (hf _ (hs y)) punit.star, by convert this⟩

open opposite

/-- Given a presheaf `P` on the category of types, construct
a map `P(α) → (α → P(*))` for all type `α`. -/
def eval (P : (Type u)ᵒᵖ ⥤ Type u) (α : Type u) (s : P.obj (op α)) (x : α) : P.obj (op punit) :=
P.map (has_hom.hom.op (λ _, x : punit ⟶ α)) s

/-- Given a sheaf `S` on the category of types, construct a map
`(α → P(*)) → P(α)` that is inverse to `eval`. -/
noncomputable def types_glue (P : (Type u)ᵒᵖ ⥤ Type u)
  (hp : is_sheaf types_grothendieck_topology P)
  (α : Type u) (f : α → P.obj (op punit)) : P.obj (op α) :=
(hp.is_sheaf_for _ _ (generate_discrete_presieve_mem α)).amalgamate
  (λ β g hg, P.map (has_hom.hom.op $ λ x, punit.star) $ f $ g $ classical.some hg)
  (λ β γ δ g₁ g₂ f₁ f₂ hf₁ hf₂ h,
    (hp.is_sheaf_for _ _ (generate_discrete_presieve_mem δ)).is_separated_for.ext $
    λ ε g ⟨x, hx⟩, have f₁ (classical.some hf₁) = f₂ (classical.some hf₂),
      from classical.some_spec hf₁ (g₁ $ g x) ▸ classical.some_spec hf₂ (g₂ $ g x) ▸ congr_fun h _,
      by { dsimp only, simp_rw [← functor_to_types.map_comp_apply, this, ← op_comp], refl })

lemma eval_types_glue {P hp α} (f) : eval.{u} P α (types_glue P hp α f) = f :=
funext $ λ x, (is_sheaf_for.valid_glue _ _ _ $
  by exact ⟨punit.star, λ _, subsingleton.elim _ _⟩).trans $
by { convert functor_to_types.map_id_apply _ _, rw ← op_id, congr }

lemma types_glue_eval {P hp α} (s) : types_glue.{u} P hp α (eval P α s) = s :=
(hp.is_sheaf_for _ _ (generate_discrete_presieve_mem α)).is_separated_for.ext $ λ β f hf,
(is_sheaf_for.valid_glue _ _ _ hf).trans $ (functor_to_types.map_comp_apply _ _ _ _).symm.trans $
by { rw ← op_comp, congr' 2, exact funext (λ x, congr_arg f (classical.some_spec hf x).symm) }

/-- Given a sheaf `S`, construct an equivalence `P(α) ≃ (α → P(*))`. -/
noncomputable def eval_equiv (P : (Type u)ᵒᵖ ⥤ Type u)
  (hp : is_sheaf types_grothendieck_topology P)
  (α : Type u) : P.obj (op α) ≃ (α → P.obj (op punit)) :=
{ to_fun := eval P α,
  inv_fun := types_glue P hp α,
  left_inv := types_glue_eval,
  right_inv := eval_types_glue }

end presieve

lemma subcanonical_types_grothendieck_topology :
  sheaf.subcanonical types_grothendieck_topology.{u} :=
sheaf.le_finest_topology _ _ $ λ P ⟨α, hα⟩, hα ▸ presieve.is_sheaf_yoneda'

end category_theory
