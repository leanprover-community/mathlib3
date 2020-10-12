/-
Copyright (c) 2020 Bhavik Mehta, E. W. Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, E. W. Ayers
-/

import category_theory.sites.grothendieck
import category_theory.full_subcategory
import category_theory.types

universes v u
namespace category_theory

open category_theory category sieve

variables {C : Type u} [category.{v} C]

namespace grothendieck_topology
variables {X Y : C} {S R : sieve X}
variables {J : sieve_set C} [grothendieck_topology J]

open sieve_set

open opposite

def matching_family (P : Cᵒᵖ ⥤ Type v) (S : sieve X) :=
S.functor ⟶ P

def amalgamation {P : Cᵒᵖ ⥤ Type v} {S : sieve X} (γ : matching_family P S) :=
{α : yoneda.obj X ⟶ P // sieve.functor_inclusion S ≫ α = γ}

@[derive subsingleton]
def sheaf_condition (J : sieve_set C) (P : Cᵒᵖ ⥤ Type v) : Type (max u v) :=
Π (X : C) (S : sieve X) (γ : matching_family P S), S ∈ J X → unique (amalgamation γ)

def matching_family' (P : Cᵒᵖ ⥤ Type v) {c : C} (S : sieve c) :=
{x : Π {d : C} {f : d ⟶ c}, S.arrows f → P.obj (opposite.op d) //
 ∀ {d e : C} (f : d ⟶ c) (g : e ⟶ d) (h : S.arrows f), x (S.downward_closed h g) = P.map g.op (x h)}

def amalgamation' {P : Cᵒᵖ ⥤ Type v} {c : C} {S : sieve c} (γ : matching_family' P S) :=
{y : P.obj (opposite.op c) // ∀ {d : C} (f : d ⟶ c) (hf : S.arrows f), P.map f.op y = γ.1 hf}

@[derive subsingleton]
def sheaf_condition' (J : sieve_set C) (P : Cᵒᵖ ⥤ Type v) : Type (max u v) :=
Π (c : C) (S : sieve c) (γ : matching_family' P S), S ∈ J c → unique (amalgamation' γ)

def matching_family'_equiv_matching_family (P : Cᵒᵖ ⥤ Type v) :
  matching_family' P S ≃ matching_family P S :=
{ to_fun := λ x, ⟨λ _ t, x.1 t.2, λ c c' f, funext $ λ t, x.2 _ _ t.2⟩,
  inv_fun := λ x, ⟨λ d f hf, x.app _ ⟨f, hf⟩, λ d d' f g h, congr_fun (x.2 g.op) ⟨f, h⟩⟩,
  left_inv := λ _, subtype.ext $ funext $ λ _, funext $ λ _, funext $ λ _, rfl,
  right_inv := λ _, by { ext _ ⟨_, _⟩, refl } }

def amalgamation'_equiv_amalgamation (P : Cᵒᵖ ⥤ Type v) (x : matching_family' P S) :
  amalgamation (matching_family'_equiv_matching_family P x) ≃ (amalgamation' x) :=
{ to_fun := λ γ,
  { val := γ.1.app _ (𝟙 X),
    property := λ d f hf,
    begin
      have := congr_fun (γ.1.naturality f.op) (𝟙 _),
      dsimp at this,
      erw ← this,
      rw comp_id,
      have q := congr_arg (λ t, nat_trans.app t (opposite.op d)) γ.2,
      dsimp at q,
      have := congr_fun q ⟨f, hf⟩,
      exact this,
    end },
  inv_fun := λ γ,
  { val :=
    { app := λ c f, P.map f.op γ.1,
      naturality' := λ c c' f, funext $ λ g, functor_to_types.map_comp_apply P g.op f γ.1 },
    property :=
    begin
      ext c ⟨f, hf⟩,
      apply γ.2,
    end },
  left_inv :=
  begin
    rintro ⟨γ₁, γ₂⟩,
    ext d f,
    dsimp,
    rw ← functor_to_types.naturality _ _ γ₁ f.op (𝟙 X),
    dsimp,
    simp,
  end,
  right_inv :=
  begin
    intro γ,
    ext1,
    apply functor_to_types.map_id_apply,
  end }

def sheaf'_equiv_sheaf (J : sieve_set C) (P : Cᵒᵖ ⥤ Type v) :
  sheaf_condition J P ≅ sheaf_condition' J P :=
{ hom :=
  begin
    intros h c S γ hS,
    apply equiv.unique (amalgamation'_equiv_amalgamation _ _).symm,
    apply h _ _ _ hS,
  end,
  inv :=
  begin
    intros h c S γ hS,
    haveI := h _ _ ((matching_family'_equiv_matching_family P).symm γ) hS,
    have := equiv.unique (amalgamation'_equiv_amalgamation P ((matching_family'_equiv_matching_family P).symm γ)),
    simpa using this,
  end }

variables (C J)

structure Sheaf :=
(P : Cᵒᵖ ⥤ Type v)
(sheaf_cond : sheaf_condition J P)

instance : category (Sheaf C J) := induced_category.category Sheaf.P

end grothendieck_topology

end category_theory
