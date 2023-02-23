import combinatorics.quiver.basic
import combinatorics.quiver.single_obj
import group_theory.group_action.basic
import group_theory.group_action.group
import combinatorics.quiver.covering
import group_theory.subgroup.basic
import group_theory.coset
import group_theory.quotient_group
import group_theory.group_action.quotient
import combinatorics.quiver.iso
/-!

## TODO

* When are two automorphisms of a schreier graph (of a group action) equal ?
* Same when the quiver is preconnected (let's only care about the preconnected case)
* Same for Cayley graphs (this is exactly when they agree on vertices and on stars)

* When is an automorphism of a schreier_coset_graph for a normal subgroup given by a group element
  i.e. as `as_autom` ?

-/

universes u v w

namespace quiver

section basic

/--
Alias for the Schreier graph vertex type.
-/
def schreier_graph (V : Type*) {M : Type*} [has_smul M V] {S : Type*} (ι : S → M) := V

/--
Converting between the original vertex type and the alias.
-/
@[simps] def equiv_schreier_graph {V : Type*} {M : Type*} [has_smul M V] {S : Type*} {ι : S → M} :
  V ≃ schreier_graph V ι := equiv.refl V

variables (V : Type*) {M : Type*} [has_smul M V] {S : Type*} (ι : S → M)

/-- Transporting the action to the alias -/
instance : has_smul M (schreier_graph V ι) :=
{ smul := λ x y, equiv_schreier_graph $ x • (equiv_schreier_graph.symm y)}

/--
The `quiver` instance on `schreier_graph V ι`.
The set of arrow from `x` to `y` is the subset of `S` such that `(ι s) x = y`.
-/
instance schreier_graph.quiver : quiver (schreier_graph V ι) :=
{ hom := λ x y, {s : S // (ι s) • x = y} }

/--
Any arrow in `schreier_graph V ι` is labelled by an element of `S`.
This is encoded as mapping to the `single_obj S` quiver.
-/
@[simps] def schreier_graph_labelling : (schreier_graph V ι) ⥤q single_obj S :=
{ obj := λ (x : schreier_graph V ι), single_obj.star S,
  map := λ x y e, subtype.rec_on e (λ s h, s), }

end basic

section group_action
/-!
### Schreier graphs for group actions.

In that case, the labelling is a covering, meaning that the stars and costars around each vertex
are in bijection with `S`.
-/

variables (V : Type*) {M : Type*} [group M] [mul_action M V] {S : Type*} (ι : S → M)

instance : mul_action M (schreier_graph V ι) :=
{ smul := has_smul.smul,
  one_smul := mul_action.one_smul,
  mul_smul := mul_action.mul_smul }

lemma schreier_graph_labelling_is_covering : (schreier_graph_labelling V ι).is_covering :=
begin
  refine ⟨λ u, ⟨_, _⟩, λ u, ⟨_, _⟩⟩,
  { rintro ⟨v,⟨x,hx⟩⟩ ⟨w,⟨y,hy⟩⟩ h,
    simp only [prefunctor.star_apply, schreier_graph_labelling_map, single_obj.to_hom_apply,
               eq_iff_true_of_subsingleton, heq_iff_eq, true_and] at h,
    subst_vars, },
  { rintro ⟨⟨⟩,x⟩, exact ⟨⟨(ι x) • u, ⟨x, rfl⟩⟩, rfl⟩, },
  { rintro ⟨v,⟨x,hx⟩⟩ ⟨w,⟨y,hy⟩⟩ h,
    simp only [prefunctor.costar_apply, schreier_graph_labelling_map, single_obj.to_hom_apply,
               eq_iff_true_of_subsingleton, heq_iff_eq, true_and] at h,
    subst_vars,
    simp only [smul_left_cancel_iff] at hy,
    subst hy, },
  { rintro ⟨⟨⟩,x⟩,
    exact ⟨⟨(ι x) ⁻¹ • u, ⟨x, by simp⟩⟩, by simp⟩, },
end

/-
The sorry should be easy but would benefit from infrastructure:
* `symmetrify (single_obj α)` is isomorphic to `single_obj (α ⊕ α)`
* need a usable def of isomorphisms
* isomorphisms induce equivalence of `star_path` etc

-/
noncomputable def schreier_graph.path_star_equiv (x : schreier_graph V ι) :
  path_star (symmetrify.of.obj x) ≃ list (S ⊕ S) :=
calc  path_star (symmetrify.of.obj x)
    ≃ path_star (symmetrify.of.obj (single_obj.star S) : symmetrify (single_obj S)) :
      equiv.of_bijective _ (prefunctor.path_star_bijective _
        (schreier_graph_labelling_is_covering V ι).symmetrify x)
... ≃ path_star (single_obj.star (S ⊕ S)) : sorry
... ≃ list (S ⊕ S) : single_obj.path_star_equiv _

/- need to fine a usable def probably in `free_group` -/
@[simp] def val : list (S ⊕ S) → M
| list.nil := 1
| (list.cons (sum.inl s) l) := (ι s) * (val l)
| (list.cons (sum.inr s) l) := (ι s) ⁻¹ * (val l)

lemma _root_.subgroup.closure_eq_range_val :
  (subgroup.closure $ set.range ι).carrier = set.range (val ι) :=
begin
  apply subset_antisymm,
  { rintro x hx, apply subgroup.closure_induction hx,
    { rintro _ ⟨s, rfl⟩, refine ⟨[sum.inl s], mul_one _⟩, },
    { refine ⟨[], rfl⟩, },
    { rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩, refine ⟨x.append y, _⟩, sorry, },
    { rintro _ ⟨x, rfl⟩, refine ⟨x.reverse, _⟩,  sorry, }, },
  { rintro _ ⟨x, rfl⟩, induction x,
    simp only [subgroup.one_mem, val, subgroup.mem_carrier],
    cases x_hd,
    sorry,
    sorry, },
end

/-
I'm using `id p.1` because `symmetrify` has no converse to `of`
That should be remedied.
-/
lemma schreier_graph.path_star_equiv_end_eq_mul
  (x : schreier_graph V ι) (p : path_star $ symmetrify.of.obj x) :
  (id p.1 : schreier_graph V ι) = (val ι $ (schreier_graph.path_star_equiv V ι x) p) • x := sorry


/--
Using the equivalence above:
* paths starting at `x` are in bijection with words over `S`
* this bijection maps the end of the path to the value of the path applied to `x`
Thus:
* Now use `_root_.subgroup.closure_eq_range_val`
-/
lemma schreier_graph.reachable_iff (x y : schreier_graph V ι) :
  nonempty (path (symmetrify.of.obj x) (symmetrify.of.obj y)) ↔
  ∃ g ∈ (subgroup.closure $ set.range ι), g • x = y := sorry

section schreier_coset_graph

/--
A Schreier coset graph is the Schreier graph of the action of a group `M` on the cosets `M ⧸ H`.
-/
abbreviation schreier_coset_graph (H : subgroup M) := schreier_graph (M ⧸ H) ι
abbreviation schreier_coset_graph_labelling (H : subgroup M) := schreier_graph_labelling (M ⧸ H) ι

notation `𝑺` := schreier_coset_graph
notation `𝑺l` := schreier_coset_graph_labelling

@[simps] noncomputable def from_coset_graph (v₀ : V) :
  schreier_coset_graph ι (mul_action.stabilizer M v₀) ⥤q schreier_graph (mul_action.orbit M v₀) ι :=
{ obj := (mul_action.orbit_equiv_quotient_stabilizer M v₀).symm,
  map := λ X Y e, ⟨e.val, by obtain ⟨e,rfl⟩ := e;
                          simp only [mul_action.smul_orbit_equiv_quotient_stabilizer_symm_apply]⟩ }

lemma from_coset_graph_labelling (v₀ : V) :
  (from_coset_graph V ι v₀) ⋙q schreier_graph_labelling (mul_action.orbit M v₀) ι =
  schreier_graph_labelling (M ⧸ mul_action.stabilizer M v₀) ι :=
begin
  dsimp only [from_coset_graph, schreier_graph_labelling],
  fapply prefunctor.ext,
  { simp only [eq_iff_true_of_subsingleton, implies_true_iff], },
  { rintros _ _ ⟨e, he⟩,
    simp only [prefunctor.comp_map, eq_rec_constant], },
end

@[simps] noncomputable def to_coset_graph (v₀ : V) :
  schreier_graph (mul_action.orbit M v₀) ι ⥤q schreier_coset_graph ι (mul_action.stabilizer M v₀) :=
{ obj := (mul_action.orbit_equiv_quotient_stabilizer M v₀),
  map := λ X Y e, ⟨e.val, by obtain ⟨e,rfl⟩ := e;
                          simp only [mul_action.smul_orbit_equiv_quotient_stabilizer_apply]⟩ }

lemma to_coset_graph_labelling (v₀ : V) :
  (to_coset_graph V ι v₀) ⋙q schreier_graph_labelling (M ⧸ mul_action.stabilizer M v₀) ι =
  schreier_graph_labelling (mul_action.orbit M v₀) ι:=
begin
  dsimp only [to_coset_graph, schreier_graph_labelling],
  fapply prefunctor.ext,
  { simp only [eq_iff_true_of_subsingleton, implies_true_iff], },
  { rintros _ _ ⟨_,_⟩,
    simp only [prefunctor.comp_map, eq_rec_constant], },
end

lemma from_coset_graph_to_coset_graph (v₀ : V) :
  from_coset_graph V ι v₀ ⋙q to_coset_graph V ι v₀ = 𝟭q _ :=
begin
  have obj : ∀ x, (from_coset_graph V ι v₀ ⋙q to_coset_graph V ι v₀).obj x = (𝟭q _).obj x, by
  { rintro _,
    simp only [to_coset_graph, from_coset_graph, prefunctor.comp_obj, equiv.apply_symm_apply,
               prefunctor.id_obj, id.def], },
  apply prefunctor.ext obj,
  rintro u v e,
  let hu := obj u,
  let hv := obj v,
  change (from_coset_graph V ι v₀ ⋙q to_coset_graph V ι v₀).map e =
         eq.rec_on hv.symm (eq.rec_on hu.symm ((𝟭q _).map e)),
  sorry,
end

lemma to_coset_graph_from_coset_graph (v₀ : V) :
  to_coset_graph V ι v₀ ⋙q from_coset_graph V ι v₀ = 𝟭q _ :=
begin
  dsimp only [to_coset_graph, from_coset_graph, prefunctor.comp, prefunctor.id],
  simp only [subtype.val_eq_coe, equiv.symm_apply_apply],
  fsplit,
  { ext ⟨_, _⟩,
    simp only [id.def], },
  { sorry, },
end

def covering_iso_lol (v₀ : V) : schreier_graph_labelling (mul_action.orbit M v₀) ι ≃qc
                                schreier_coset_graph_labelling ι (mul_action.stabilizer M v₀) := sorry

section automs

variables {N : subgroup M} [Nn : N.normal]
include Nn

@[simps] def as_autom (g : M) : schreier_coset_graph ι N ⥤q schreier_coset_graph ι N :=
{ obj := λ x, equiv_schreier_graph ((equiv_schreier_graph.symm x) * (g⁻¹)),
  map := λ x y a, ⟨a.val, by
    begin
      obtain ⟨a,rfl⟩ := a,
      obtain ⟨x⟩ := x,
      change ι a • ((↑x : M ⧸ N) * (↑g)⁻¹) = ι a • (↑x : M ⧸ N) * (↑g)⁻¹,
      simpa only [mul_action.quotient.smul_coe, smul_eq_mul, quotient_group.coe_mul, mul_assoc],
    end⟩ }

lemma as_autom_labelling (g : M) :
  as_autom ι g ⋙q schreier_coset_graph_labelling ι N = schreier_coset_graph_labelling ι N :=
begin
  dsimp only [as_autom, schreier_graph_labelling],
  fapply prefunctor.ext,
  { simp only [eq_iff_true_of_subsingleton, implies_true_iff], },
  { rintro _ _ ⟨_, rfl⟩,
    simp [subtype.coe_mk, prefunctor.comp_map, schreier_graph_labelling_map,
    eq_rec_constant], },
end

lemma as_autom_one : as_autom ι 1 = 𝟭q (𝑺 ι N) :=
begin
  dsimp only [as_autom],
  fapply prefunctor.ext,
  { simp only [equiv_schreier_graph_symm_apply, quotient_group.coe_one, inv_one, mul_one,
               equiv_schreier_graph_apply, prefunctor.id_obj, id.def, eq_self_iff_true,
               implies_true_iff], },
  { rintro _ _ ⟨_, rfl⟩,
    simp only [prefunctor.id_map],
    sorry, },
end

lemma as_autom_mul (g h : M) :
  (as_autom ι (g * h) : 𝑺 ι N ⥤q  𝑺 ι N) = (as_autom ι h) ⋙q (as_autom ι g) :=
begin
  dsimp only [as_autom],
  fapply prefunctor.ext,
  { simp only [mul_assoc, equiv_schreier_graph_symm_apply, quotient_group.coe_mul, mul_inv_rev,
               equiv_schreier_graph_apply, prefunctor.comp_obj, eq_self_iff_true,
               implies_true_iff], },
  { rintro _ _ ⟨_, rfl⟩,
    simp only [prefunctor.comp_map],
    sorry, },
end

lemma as_autom_eq_iff (g₁ g₂ : M) :
  (as_autom ι g₁ : 𝑺 ι N ⥤q 𝑺 ι N) = (as_autom ι g₂ : 𝑺 ι N ⥤q 𝑺 ι N) ↔ g₁ / g₂ ∈ N :=
begin
  dsimp only [as_autom],
  refine ⟨λ h, _, λ h, _⟩,
  { simp only [subtype.val_eq_coe, equiv_schreier_graph_symm_apply,
               equiv_schreier_graph_apply] at h ⊢,
    simpa [←quotient_group.coe_one, quotient_group.eq_iff_div_mem] using
            (congr_fun h.left (equiv_schreier_graph 1)), },
  { fapply prefunctor.ext,
    { rintro ⟨x⟩,
      change (↑x : M ⧸ N) * (g₁)⁻¹ = (↑x : M ⧸ N) * (↑g₂)⁻¹,
      simpa [quotient_group.eq_iff_div_mem] using h, },
    { simp, rintro ⟨x⟩ ⟨y⟩ f,
      sorry, }, },
end

lemma exists_as_autom_iff  {φ ψ : 𝑺 ι N ⥤q 𝑺 ι N}
  (φψ : φ ⋙q ψ = 𝟭q _) (ψφ : ψ ⋙q φ = 𝟭q _) (φc : φ ⋙q 𝑺l ι N = 𝑺l ι N) :
  ∃ g, as_autom ι g = φ ↔ sorry := sorry


end automs

end schreier_coset_graph

/--
The Cayley graph of `M` w.r.t. `ι : S → M` is the Schreier coset graph where `H` is the trivial
subgroup of `M`.
-/
abbreviation cayley_graph := schreier_coset_graph ι (⊥ : subgroup M)
abbreviation cayley_graph_labelling := schreier_graph_labelling (M ⧸ (⊥ : subgroup M)) ι

notation `𝑪` := cayley_graph
notation `𝑪l` := cayley_graph_labelling

namespace cayley_graph

variables {N : subgroup M} [Nn : N.normal]
include Nn

def cayley_eq_schreier :
  iso (cayley_graph $ (quotient_group.mk : M → M ⧸ N) ∘ ι) (schreier_coset_graph ι N) :=

-- the isomorphism `cayley_eq_schreier` preserves labelling.
lemma cayley_eq_schreier_labelling := sorry

end cayley_graph

end group_action

end quiver
