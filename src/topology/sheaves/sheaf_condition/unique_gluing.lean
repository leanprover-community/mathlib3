/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import topology.sheaves.sheaf
import category_theory.limits.shapes.types
import category_theory.types

/-!
# The sheaf condition for a type-valued presheaf

We provide an alternative formulation of the sheaf condition for type-valued presheaves.

A presheaf `F : presheaf (Type u) X` satisfies the sheaf condition if and only if, for every
compatible family of sections `sf : Π i : ι, F.obj (op (U i))`, there exists a unique gluing
`s : F.obj (op (supr U))`.

Here, the family `sf` is called compatible, if for all `i j : ι`, the restrictions of `sf i`
and `sf j` to `U i ⊓ U j` agree. A section `s : F.obj (op (supr U))` is a gluing for the
family `sf`, if `s` restricts to `sf i` on `U i` for all `i : ι`

We show that the sheaf condition in terms of unique gluings is equivalent to the definition
in terms of equalizers.

-/

noncomputable theory

universe u

open Top
open Top.presheaf
open Top.presheaf.sheaf_condition_equalizer_products
open category_theory
open category_theory.limits
open topological_space
open topological_space.opens
open opposite

namespace Top

namespace presheaf

variables {X : Top.{u}} (F : presheaf (Type u) X) {ι : Type u} (U : ι → opens X)

@[simp] lemma res_π_apply (i : ι) (s : F.obj (op (supr U))) :
  limit.π (discrete.functor (λ i : ι, F.obj (op (U i)))) i (res F U s) =
  F.map (opens.le_supr U i).op s :=
congr_fun (res_π F U i) s

/--
A family of sections `sf` is compatible, if the restrictions of `sf i` and `sf j` to `U i ⊓ U j`
agree, for all `i` and `j`
-/
def is_compatible (sf : Π i : ι, F.obj (op (U i))) : Prop :=
  ∀ i j : ι, F.map (inf_le_left (U i) (U j)).op (sf i) = F.map (inf_le_right (U i) (U j)).op (sf j)

/--
For presheaves of types, terms of `pi_opens F U` are just families of sections
-/
def pi_opens_iso_sections_family : pi_opens F U ≅ Π i : ι, F.obj (op (U i)) :=
  limits.is_limit.cone_point_unique_up_to_iso
    (limit.is_limit (discrete.functor (λ i : ι, F.obj (op (U i)))))
    ((types.product_limit_cone (λ i : ι, F.obj (op (U i)))).is_limit)

/--
Under the isomorphism `pi_opens_iso_sections_family`, compatibility of sections is the same
as being equalized by the arrows `left_res` and `right_res` of the equalizer diagram.
-/
lemma compatible_iff_left_res_eq_right_res (sf : pi_opens F U) :
  is_compatible F U ((pi_opens_iso_sections_family F U).hom sf)
    ↔ left_res F U sf = right_res F U sf :=
begin
  split ; intros h,
  { ext ⟨i,j⟩,
    rw [left_res, types.limit.lift_π_apply, fan.mk_π_app,
        right_res, types.limit.lift_π_apply, fan.mk_π_app],
    exact h i j, },
  { intros i j,
    convert congr_arg (limits.pi.π (λ p : ι × ι, F.obj (op (U p.1 ⊓ U p.2))) (i,j)) h,
    {rw [left_res, types.pi_lift_π_apply], refl},
    {rw [right_res, types.pi_lift_π_apply], refl}, }
end

/--
A section `s` is a gluing for a family of sections `sf` if it restricts to `sf i` on `U i`,
for all `i`
-/
def is_gluing (sf : Π i : ι, F.obj (op (U i))) (s : F.obj (op (supr U))) : Prop :=
  ∀ i : ι, F.map (opens.le_supr U i).op s = sf i

/--
Under the isomorphism `pi_opens_iso_sections_family`, being a gluing of a family of
sections `sf` is the same as lying in the preimage of `res` (the leftmost arrow of the
equalizer diagram).
-/
@[simp]
lemma is_gluing_iff_eq_res (sf : pi_opens F U) (s : F.obj (op (supr U))):
  is_gluing F U ((pi_opens_iso_sections_family F U).hom sf) s ↔ res F U s = sf :=
begin
  split ; intros h,
  { ext i,
    rw [res, types.limit.lift_π_apply, fan.mk_π_app],
    exact h i, },
  { intro i,
    convert congr_arg (limits.pi.π (λ i : ι, F.obj (op (U i))) i) h,
    rw [res, types.pi_lift_π_apply] },
end

/--
The subtype of all gluings for a given family of sections
-/
@[nolint has_inhabited_instance]
def gluing (sf : Π i : ι, F.obj (op (U i))) : Type u :=
  {s : F.obj (op (supr U)) // is_gluing F U sf s}

/--
The sheaf condition of type-valued presheaves in terms of unique gluings. A presheaf
`F : presheaf (Type u) X` satisfies this sheaf condition if and only if, for every
compatible family of sections `sf : Π i : ι, F.obj (op (U i))`, there exists a unique
gluing `s : F.obj (op (supr U))`.

We prove this to be equivalent to the usual one below in
`sheaf_condition_equiv_sheaf_condition_unique_gluing`
-/
@[derive subsingleton, nolint has_inhabited_instance]
def sheaf_condition_unique_gluing : Type (u+1) :=
  Π ⦃ι : Type u⦄ (U : ι → opens X) (sf : Π i : ι, F.obj (op (U i))),
    is_compatible F U sf → unique (gluing F U sf)

/--
The "equalizer" sheaf condition can be obtained from the sheaf condition
in terms of unique gluings
-/
def sheaf_condition_of_sheaf_condition_unique_gluing :
  F.sheaf_condition_unique_gluing → F.sheaf_condition := λ Fsh ι U,
begin
  refine fork.is_limit.mk' _ (λ s, ⟨_,_,_⟩) ; dsimp,
  { intro x,
    refine (Fsh U ((pi_opens_iso_sections_family F U).hom (s.ι x)) _).default.1,
    apply (compatible_iff_left_res_eq_right_res F U (s.ι x)).mpr,
    convert congr_fun s.condition x, },
  { ext i x,
    simp [res],
    let t : gluing F U _ := _,
    exact t.2 i },
  { intros m hm,
    ext x,
    refine congr_arg subtype.val
      ((Fsh U ((pi_opens_iso_sections_family F U).hom (s.ι x)) _).uniq ⟨m x, _⟩),
    apply (is_gluing_iff_eq_res F U _ _).mpr,
    exact congr_fun hm x },
end

/--
The sheaf condition in terms of unique gluings can be obtained from the usual
"equalizer" sheaf condition
-/
def sheaf_condition_unique_gluing_of_sheaf_condition :
  F.sheaf_condition → F.sheaf_condition_unique_gluing := λ Fsh ι U sf hsf,
{ default := begin
    let sf' := (pi_opens_iso_sections_family F U).inv sf,
    have hsf' : left_res F U sf' = right_res F U sf' := by
      rwa [← compatible_iff_left_res_eq_right_res F U sf', inv_hom_id_apply],
    choose s s_spec s_uniq using types.unique_of_type_equalizer _ _ (Fsh U) sf' hsf',
    use s,
    convert (is_gluing_iff_eq_res F U _ _).mpr s_spec,
    rw inv_hom_id_apply
  end,
  uniq := begin
    intro s,
    /- Unfortunately, type inference doesn't yet know about the `inhabited` instance of
    `gluing F U sf` We therefore introduce a metavariable and use unification to get our hands
    on the default value of `gluing F U sf`. -/
    let t : F.gluing U sf := _,
    change s = t,
    ext,
    let sf' := (pi_opens_iso_sections_family F U).inv sf,
    have hsf' : left_res F U sf' = right_res F U sf' := by
      rwa [← compatible_iff_left_res_eq_right_res F U sf', inv_hom_id_apply],
    choose gl gl_spec gl_uniq using types.unique_of_type_equalizer _ _ (Fsh U) sf' hsf',
    refine eq.trans (gl_uniq s.1 _) (gl_uniq t.1 _).symm ;
      rw [← is_gluing_iff_eq_res F U _ _, inv_hom_id_apply],
    exacts [s.2, t.2]
  end
}

/--
The sheaf condition in terms of unique gluings is equivalent to the usual sheaf condition
in terms of equalizer diagrams.
-/
def sheaf_condition_equiv_sheaf_condition_unique_gluing :
  F.sheaf_condition ≃ F.sheaf_condition_unique_gluing :=
equiv_of_subsingleton_of_subsingleton
  F.sheaf_condition_unique_gluing_of_sheaf_condition
  F.sheaf_condition_of_sheaf_condition_unique_gluing

/--
A slightly more convenient way of obtaining the sheaf condition for type-valued sheaves
-/
def sheaf_condition_of_exists_unique_gluing
  (h : ∀ ⦃ι : Type u⦄ (U : ι → opens X) (sf : Π i : ι, F.obj (op (U i))),
        is_compatible F U sf → ∃! s : F.obj (op (supr U)), is_gluing F U sf s) :
  F.sheaf_condition :=
sheaf_condition_of_sheaf_condition_unique_gluing F $ λ ι U sf hsf,
{ default := by {
    choose gl gl_spec gl_uniq using h U sf hsf,
    exact ⟨gl, gl_spec⟩, },
  uniq := by {
    intro s,
    let t : F.gluing U sf := _,
    change s = t,
    ext,
    choose gl gl_spec gl_uniq using h U sf hsf,
    refine eq.trans (gl_uniq s.1 _) (gl_uniq t.1 _).symm,
    exacts [s.2, t.2] },
}

end presheaf


namespace sheaf
open presheaf
open category_theory

variables {X : Top.{u}} (F : sheaf (Type u) X) {ι : Type u} (U : ι → opens X)

/--
A more convenient way of obtaining a unique gluing of sections for a sheaf
-/
lemma exists_unique_gluing (sf : Π i : ι, F.presheaf.obj (op (U i)))
  (h : is_compatible F.presheaf U sf ) :
  ∃! s : F.presheaf.obj (op (supr U)), is_gluing F.presheaf U sf s :=
begin
  have := (sheaf_condition_unique_gluing_of_sheaf_condition _ F.sheaf_condition U sf h),
  refine ⟨this.default.1,this.default.2,_⟩,
  intros s hs,
  exact congr_arg subtype.val (this.uniq ⟨s,hs⟩),
end

/--
In this version of the lemma, the inclusion homs `iUV` can be specified directly by the user,
which can be more convenient in practice.
-/
lemma exists_unique_gluing' (V : opens X) (iUV : Π i : ι, U i ⟶ V) (hcover : V ≤ supr U)
  (sf : Π i : ι, F.presheaf.obj (op (U i))) (h : is_compatible F.presheaf U sf) :
  ∃! s : F.presheaf.obj (op V), ∀ i : ι, F.presheaf.map (iUV i).op s = sf i :=
begin
  have V_eq_supr_U : V = supr U := le_antisymm hcover (supr_le (λ i, (iUV i).le)),
  obtain ⟨gl, gl_spec, gl_uniq⟩ := F.exists_unique_gluing U sf h,
  refine ⟨F.presheaf.map (eq_to_hom V_eq_supr_U).op gl, (λ i,_), (λ gl' gl'_spec,_)⟩,
  { rw ← functor_to_types.map_comp_apply,
    exact gl_spec i },
  { convert congr_arg _ (gl_uniq (F.presheaf.map (eq_to_hom V_eq_supr_U.symm).op gl') (λ i,_)) ;
      rw ← functor_to_types.map_comp_apply,
    { exact (functor_to_types.map_id_apply _ _).symm },
    { convert gl'_spec i }}
end

@[ext]
lemma eq_of_locally_eq (s t : F.presheaf.obj (op (supr U)))
  (h : ∀ i, F.presheaf.map (opens.le_supr U i).op s = F.presheaf.map (opens.le_supr U i).op t) :
  s = t :=
begin
  apply (mono_iff_injective _).mp (mono_of_is_limit_parallel_pair (F.sheaf_condition U)),
  ext,
  simp only [fork_ι, res_π_apply, h],
end

/--
In this version of the lemma, the inclusion homs `iUV` can be specified directly by the user,
which can be more convenient in practice.
-/
lemma eq_of_locally_eq' (V : opens X) (iUV : Π i : ι, U i ⟶ V) (hcover : V ≤ supr U)
  (s t : F.presheaf.obj (op V))
  (h : ∀ i, F.presheaf.map (iUV i).op s = F.presheaf.map (iUV i).op t) : s = t :=
begin
  have V_eq_supr_U : V = supr U := le_antisymm hcover (supr_le (λ i, (iUV i).le)),
  suffices : F.presheaf.map (eq_to_hom V_eq_supr_U.symm).op s =
             F.presheaf.map (eq_to_hom V_eq_supr_U.symm).op t,
  { convert congr_arg (F.presheaf.map (eq_to_hom V_eq_supr_U).op) this ;
    rw ← functor_to_types.map_comp_apply ;
    exact (functor_to_types.map_id_apply _ _).symm },
  apply eq_of_locally_eq,
  intro i,
  rw [← functor_to_types.map_comp_apply, ← functor_to_types.map_comp_apply],
  convert h i
end

end sheaf

end Top
