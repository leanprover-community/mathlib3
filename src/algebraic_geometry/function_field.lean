/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.properties

/-!
# Function field of integral schemes

We define the function field of an irreducible scheme as the stalk of the generic point.
This is a field when the scheme is integral.

## Main definition
* `algebraic_geometry.Scheme.function_field`: The function field of an integral scheme.
* `algebraic_geometry.germ_to_function_field`: The canonical map from a component into the function
  field. This map is injective.
-/

universes u v

open topological_space opposite category_theory category_theory.limits Top

namespace algebraic_geometry

variable (X : Scheme)

/-- The function field of an irreducible scheme is the local ring at its generic point.
Despite the name, this is a field only when the scheme is integral. -/
noncomputable
abbreviation Scheme.function_field [irreducible_space X.carrier] : CommRing :=
X.presheaf.stalk (generic_point X.carrier)

/-- The restriction map from a component to the function field. -/
noncomputable
abbreviation Scheme.germ_to_function_field [irreducible_space X.carrier] (U : opens X.carrier)
  [h : nonempty U] : X.presheaf.obj (op U) ⟶ X.function_field :=
X.presheaf.germ ⟨generic_point X.carrier,
  ((generic_point_spec X.carrier).mem_open_set_iff U.prop).mpr (by simpa using h)⟩

noncomputable
instance [is_integral X] : field X.function_field :=
begin
  apply field_of_is_unit_or_eq_zero,
  intro a,
  obtain ⟨U, m, s, rfl⟩ := Top.presheaf.germ_exist _ _ a,
  rw [or_iff_not_imp_right, ← (X.presheaf.germ ⟨_, m⟩).map_zero],
  intro ha,
  replace ha := ne_of_apply_ne _ ha,
  have hs : generic_point X.carrier ∈ RingedSpace.basic_open _ s,
  { rw [← opens.mem_coe, (generic_point_spec X.carrier).mem_open_set_iff, set.top_eq_univ,
      set.univ_inter, ← set.ne_empty_iff_nonempty, ne.def, ← opens.coe_bot,
      subtype.coe_injective.eq_iff, ← opens.empty_eq],
    erw basic_open_eq_bot_iff,
    exacts [ha, (RingedSpace.basic_open _ _).prop] },
  have := (X.presheaf.germ ⟨_, hs⟩).is_unit_map (RingedSpace.is_unit_res_basic_open _ s),
  rwa Top.presheaf.germ_res_apply at this
end

lemma germ_injective_of_is_integral [is_integral X] {U : opens X.carrier} (x : U) :
  function.injective (X.presheaf.germ x) :=
begin
  rw ring_hom.injective_iff,
  intros y hy,
  rw ← (X.presheaf.germ x).map_zero at hy,
  obtain ⟨W, hW, iU, iV, e⟩ := X.presheaf.germ_eq _ x.prop x.prop _ _ hy,
  cases (show iU = iV, from subsingleton.elim _ _),
  haveI : nonempty W := ⟨⟨_, hW⟩⟩,
  exact map_injective_of_is_integral X iU e
end

lemma Scheme.germ_to_function_field_injective [is_integral X] (U : opens X.carrier)
  [nonempty U] : function.injective (X.germ_to_function_field U) :=
germ_injective_of_is_integral _ _

end algebraic_geometry
