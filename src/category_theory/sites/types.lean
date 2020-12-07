/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import category_theory.sites.canonical
import category_theory.sites.sheaf

/-!
# Grothendieck Topology and Sheaves on the Category of Types

In this file we define a Grothendieck topology on the category of types,
and construct the canonical function that sends a type to a sheaf over
the category of types.

Then we prove that the topology defined is the canonical topology.
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

open presieve

theorem is_sheaf_yoneda' {α : Type u} : is_sheaf types_grothendieck_topology (yoneda.obj α) :=
λ β S hs x hx, ⟨λ y, x _ (hs y) punit.star,
λ γ f h, funext $ λ z,
  have _ := congr_fun (hx (𝟙 _) (λ _, z) (hs $ f z) h rfl) punit.star,
  by { convert this, exact rfl },
λ f hf, funext $ λ y, by convert congr_fun (hf _ (hs y)) punit.star⟩

open opposite

/-- Given a presheaf `P` on the category of types, construct
a map `P(α) → (α → P(*))` for all type `α`. -/
def eval (P : (Type u)ᵒᵖ ⥤ Type u) (α : Type u) (s : P.obj (op α)) (x : α) : P.obj (op punit) :=
P.map (↾λ _, x).op s

/-- Given a sheaf `S` on the category of types, construct a map
`(α → S(*)) → S(α)` that is inverse to `eval`. -/
noncomputable def types_glue (S : (Type u)ᵒᵖ ⥤ Type u)
  (hs : is_sheaf types_grothendieck_topology S)
  (α : Type u) (f : α → S.obj (op punit)) : S.obj (op α) :=
(hs.is_sheaf_for _ _ (generate_discrete_presieve_mem α)).amalgamate
  (λ β g hg, S.map (↾λ x, punit.star).op $ f $ g $ classical.some hg)
  (λ β γ δ g₁ g₂ f₁ f₂ hf₁ hf₂ h,
    (hs.is_sheaf_for _ _ (generate_discrete_presieve_mem δ)).is_separated_for.ext $
    λ ε g ⟨x, hx⟩, have f₁ (classical.some hf₁) = f₂ (classical.some hf₂),
      from classical.some_spec hf₁ (g₁ $ g x) ▸ classical.some_spec hf₂ (g₂ $ g x) ▸ congr_fun h _,
      by { simp_rw [← functor_to_types.map_comp_apply, this, ← op_comp], refl })

lemma eval_types_glue {S hs α} (f) : eval.{u} S α (types_glue S hs α f) = f :=
funext $ λ x, (is_sheaf_for.valid_glue _ _ _ $
  by exact ⟨punit.star, λ _, subsingleton.elim _ _⟩).trans $
by { convert functor_to_types.map_id_apply _ _, rw ← op_id, congr }

lemma types_glue_eval {S hs α} (s) : types_glue.{u} S hs α (eval S α s) = s :=
(hs.is_sheaf_for _ _ (generate_discrete_presieve_mem α)).is_separated_for.ext $ λ β f hf,
(is_sheaf_for.valid_glue _ _ _ hf).trans $ (functor_to_types.map_comp_apply _ _ _ _).symm.trans $
by { rw ← op_comp, congr' 2, exact funext (λ x, congr_arg f (classical.some_spec hf x).symm) }

/-- Given a sheaf `S`, construct an equivalence `S(α) ≃ (α → S(*))`. -/
@[simps] noncomputable def eval_equiv (S : (Type u)ᵒᵖ ⥤ Type u)
  (hs : is_sheaf types_grothendieck_topology S)
  (α : Type u) : S.obj (op α) ≃ (α → S.obj (op punit)) :=
{ to_fun := eval S α,
  inv_fun := types_glue S hs α,
  left_inv := types_glue_eval,
  right_inv := eval_types_glue }

lemma eval_map (S : (Type u)ᵒᵖ ⥤ Type u) (α β) (f : β ⟶ α) (s x) :
  eval S β (S.map f.op s) x = eval S α s (f x) :=
by { simp_rw [eval, ← functor_to_types.map_comp_apply, ← op_comp], refl }

/-- Given a sheaf `S`, construct an isomorphism `S ≅ [-, S(*)]`. -/
@[simps {rhs_md := semireducible}] noncomputable def equiv_yoneda (S : (Type u)ᵒᵖ ⥤ Type u)
  (hs : is_sheaf types_grothendieck_topology S) :
  S ≅ yoneda.obj (S.obj (op punit)) :=
nat_iso.of_components (λ α, equiv.to_iso $ eval_equiv S hs $ unop α) $ λ α β f,
funext $ λ s, funext $ λ x, eval_map S (unop α) (unop β) f.unop _ _

lemma subcanonical_types_grothendieck_topology :
  sheaf.subcanonical types_grothendieck_topology.{u} :=
sheaf.subcanonical.of_yoneda_is_sheaf _ (λ X, is_sheaf_yoneda')

lemma types_grothendieck_topology_eq_canonical :
  types_grothendieck_topology.{u} = sheaf.canonical_topology (Type u) :=
le_antisymm subcanonical_types_grothendieck_topology $ Inf_le ⟨yoneda.obj (ulift bool), ⟨_, rfl⟩,
grothendieck_topology.ext $ funext $ λ α, set.ext $ λ S,
⟨λ hs x, classical.by_contradiction $ λ hsx,
  have (λ _, ulift.up tt : (yoneda.obj (ulift bool)).obj (op punit)) = λ _, ulift.up ff :=
    (hs punit (λ _, x)).is_separated_for.ext $ λ β f hf, funext $ λ y, hsx.elim $ S.2 hf $ λ _, y,
  bool.no_confusion $ ulift.up.inj $ (congr_fun this punit.star : _),
λ hs β f, is_sheaf_yoneda' _ $ λ y, hs _⟩⟩

end category_theory
