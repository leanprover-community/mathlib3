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
import group_theory.free_group

/-

## TODO

* Should `action_graph` be defined just for `[has_smul M V]` without the `ι : S → M`, and then
  specialized when talking about group actions ?

-/

universes u v w

namespace quiver

section basic

/--
Alias for the Schreier graph vertex type.
-/
def action_graph (V : Type*) {M : Type*} [has_smul M V] {S : Type*} (ι : S → M) := V

/--
Converting between the original vertex type and the alias.
-/
@[simps] def equiv_action_graph {V : Type*} {M : Type*} [has_smul M V] {S : Type*} {ι : S → M} :
  V ≃ action_graph V ι := equiv.refl V

variables (V : Type*) {M : Type*} [has_smul M V] {S : Type*} (ι : S → M)

/-- Transporting the action to the alias -/
instance : has_smul M (action_graph V ι) :=
{ smul := λ x y, equiv_action_graph $ x • (equiv_action_graph.symm y)}

/--
The `quiver` instance on `action_graph V ι`.
The set of arrow from `x` to `y` is the subset of `S` such that `(ι s) x = y`.
-/
instance action_graph.quiver : quiver (action_graph V ι) :=
{ hom := λ x y, {s : S // (ι s) • x = y} }

abbreviation mk_hom (x : action_graph V ι) (s : S) : x ⟶ ι s • x := ⟨s, rfl⟩

lemma cast_mk_hom {x x' : action_graph V ι} (h : x = x') {s : S} (h' : ι s • x = ι s • x') :
  (mk_hom V ι x s).cast h h' = mk_hom V ι x' s :=
by { cases h, cases h', refl, }

/--
The star around a vertex is just `S`.
-/
@[simps] def action_graph.star_equiv (x : action_graph V ι) : star x ≃ S :=
{ to_fun := λ p, p.2,
  inv_fun := λ s, ⟨ι s • x, ⟨s, rfl⟩⟩,
  left_inv := λ ⟨_, ⟨s, rfl⟩⟩, rfl,
  right_inv := λ s, rfl }

def action_graph.path_star_equiv (x : action_graph V ι) : path_star x ≃ list S :=
{ to_fun := λ p, @quiver.path.rec_on _ _ x (λ y p, list S) p.1 p.2 [] (λ _ _ q e ih, ih.cons e.1),
  inv_fun := @list.rec _ (λ l, path_star x) ⟨x, path.nil⟩ (λ h l ih, ⟨_, ih.2.cons ⟨h, rfl⟩⟩),
  left_inv :=
    begin
      rintro ⟨v, p⟩,
      induction p with y z q e ih, { refl, },
      { obtain ⟨s, rfl⟩ := e,
        simp only [path_star_eq_iff] at ih,
        obtain ⟨h₁, h₂⟩ := ih,
        dsimp at h₁,
        simp only [←h₁, ←h₂],
        refine ⟨rfl, _⟩,
        rw [←path.eq_cast_iff_heq rfl (congr_arg (λ x, ι s • x) h₁.symm),
            path.cast_cons, path.cast_cast],
        fapply cons_eq_cons_of_exist_cast h₁,
        { rw [hom.cast_eq_iff_eq_cast, hom.cast_cast, cast_mk_hom], refl, },
        { apply path.cast_irrelevant, }, },
    end,
  right_inv :=
    begin
      rintro l,
      induction l with s l ih,
      { refl, },
      { simp only [subtype.val_eq_coe, eq_self_iff_true, true_and, ←ih], },
    end }

/--
Any arrow in `action_graph V ι` is labelled by an element of `S`.
This is encoded as mapping to the `single_obj S` quiver.
-/
@[simps] def action_graph_labelling : (action_graph V ι) ⥤q single_obj S :=
{ obj := λ (x : action_graph V ι), single_obj.star S,
  map := λ x y e, action_graph.star_equiv V ι x ⟨y, e⟩, }

notation `𝑨` := action_graph
notation `𝑨l` := action_graph_labelling

lemma action_graph.labelling_star_bijective (x : 𝑨 V ι) : ((𝑨l V ι).star x).bijective :=
begin
  split,
  { rintro ⟨_, ⟨_, rfl⟩⟩ ⟨_, ⟨_, rfl⟩⟩ h,
    simp only [prefunctor.star_apply, action_graph_labelling_map, action_graph.star_equiv_apply,
               subtype.coe_mk, eq_iff_true_of_subsingleton, heq_iff_eq, true_and] at h,
    subst h, },
  { rintro ⟨⟨⟩, s⟩, refine ⟨⟨_, ⟨s, rfl⟩⟩, rfl⟩, }
end

end basic

section group_action
/-!
### Schreier graphs for group actions.

In that case, the labelling is a covering, meaning that the stars and costars around each vertex
are in bijection with `S`.
-/

variables (V : Type*) {M : Type*} [group M] [mul_action M V] {S : Type*} (ι : S → M)

instance : mul_action M (𝑨 V ι) :=
{ smul := has_smul.smul,
  one_smul := mul_action.one_smul,
  mul_smul := mul_action.mul_smul }

@[simps] def action_graph.costar_equiv (x : action_graph V ι) : costar x ≃ S :=
{ to_fun := λ p, p.2,
  inv_fun := λ s, ⟨(ι s)⁻¹ • x, ⟨s, by simp⟩⟩,
  left_inv := by { rintro ⟨y, ⟨s, rfl⟩⟩, simp [subtype.heq_iff_coe_eq], },
  right_inv := λ s, rfl }

lemma action_graph.labelling_costar_bijective (x : 𝑨 V ι) : ((𝑨l V ι).costar x).bijective :=
begin
  split,
  { rintro ⟨y, ⟨s, hy⟩⟩ ⟨z, ⟨t, hz⟩⟩ h,
    subst_vars,
    simp only [prefunctor.costar_apply, action_graph_labelling_map, action_graph.star_equiv_apply,
               subtype.coe_mk, eq_iff_true_of_subsingleton, heq_iff_eq, true_and] at h,
    subst h,
    simp only [smul_eq_iff_eq_inv_smul, inv_smul_smul] at hz,
    subst hz, },
  { rintro ⟨⟨⟩, s⟩, refine ⟨⟨(ι s)⁻¹ • x, ⟨s, _⟩⟩, _⟩, simp, simp, },
end

lemma action_graph_labelling_is_covering : (𝑨l V ι).is_covering :=
⟨action_graph.labelling_star_bijective V ι, action_graph.labelling_costar_bijective V ι⟩


notation `𝑨c` := action_graph_labelling_is_covering

@[simps] def _root_.equiv.sum {α₀ α₁ β₀ β₁ : Type*} (hα : α₀ ≃ α₁) (hβ : β₀ ≃ β₁) :
  α₀ ⊕ β₀ ≃ α₁ ⊕ β₁ :=
{ to_fun := sum.elim (@sum.inl _ β₁ ∘ hα) (@sum.inr α₁ _ ∘ hβ),
  inv_fun := sum.elim (@sum.inl _ β₀ ∘ hα.symm) (@sum.inr α₀ _ ∘ hβ.symm),
  left_inv := by
  { rintro (_|_);
    simp only [sum.elim_inl, sum.elim_inr, function.comp_app, equiv.symm_apply_apply], },
  right_inv :=  by
  { rintro (_|_);
    simp only [sum.elim_inl, sum.elim_inr, function.comp_app, equiv.apply_symm_apply], } }

/-
The sorry should be easy but would benefit from infrastructure:
* `symmetrify (single_obj α)` is isomorphic to `single_obj (α ⊕ α)`
* need a usable def of isomorphisms
* isomorphisms induce equivalence of `star` and `star_path` etc
-/
@[simps] def action_graph.symmetrify_star_equiv (x : 𝑨 V ι ) :
  star (symmetrify.of.obj x) ≃ S ⊕ S :=
begin
  transitivity,
  apply quiver.symmetrify_star,
  apply equiv.sum,
  apply action_graph.star_equiv,
  apply action_graph.costar_equiv,
end

noncomputable def action_graph.symmetrify_path_star_equiv (x : 𝑨 V ι) :
  path_star (symmetrify.of.obj x) ≃ list (S ⊕ S) :=
{ to_fun := by
  begin
    rintros ⟨y, p⟩,
    induction p with a b p e ih,
    exact list.nil,
    exact ih.append [(action_graph.symmetrify_star_equiv V ι a).to_fun ⟨_, e⟩],
  end,
  inv_fun :=
  begin
    rintros l,
    induction l with a l ih,
    exact ⟨_, path.nil⟩,
    exact ⟨_, ih.2.cons $ ((action_graph.symmetrify_star_equiv V ι ih.1).inv_fun a).2⟩,
  end,
  left_inv :=
  begin
    rintros ⟨y, p⟩,
    induction p with a b p e ih,
    { simp, },
    sorry
  end,
  right_inv := sorry }

/-
Need to fine a usable def probably in `free_group`
* `free_group.lift.aux`, but `free_group` uses `bool × S` …
 -/
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
lemma action_graph.path_star_equiv_end_eq_mul
  (x : 𝑨 V ι) (p : path_star $ symmetrify.of.obj x) :
  (id p.1 : 𝑨 V ι) = (val ι $ (action_graph.symmetrify_path_star_equiv V ι x) p) • x := sorry


/--
Using the equivalence above:
* paths starting at `x` are in bijection with words over `S`
* this bijection maps the end of the path to the value of the path applied to `x`
Thus:
* Now use `_root_.subgroup.closure_eq_range_val`
-/
lemma action_graph.reachable_iff (x y : 𝑨 V ι) :
  nonempty (path (symmetrify.of.obj x) (symmetrify.of.obj y)) ↔
  ∃ g ∈ (subgroup.closure $ set.range ι), g • x = y := sorry

/- A endomorphism of the graph (with labelling) commutes with the `smul`. -/
lemma action_graph.action_commute (φ : 𝑨 V ι ⥤q 𝑨 V ι) (φm : φ ⋙q 𝑨l V ι = 𝑨l V ι)
  (v : 𝑨 V ι) (s : S) : φ.obj (ι s • v) = ι s • (φ.obj v) :=
begin
  let e : v ⟶ ι s • v := ⟨_, rfl⟩,
  let e' : φ.obj v ⟶ ι s • (φ.obj v) := ⟨_, rfl⟩,
  have : φ.star _ ⟨_, e⟩ = ⟨_, e'⟩, by
  { suffices : (φ ⋙q 𝑨l _ _).star _ ⟨_, e⟩ = (𝑨l _ _).star _ ⟨_, e'⟩,
    { dsimp only [prefunctor.star_comp] at this,
      apply ((𝑨c _ _).1 _).left this, },
    rw [φm],
    refl },
  simp only [prefunctor.star_apply] at this,
  exact this.1,
end

/--
Given a pretransitive action, and assuming `set.range ι` generates the group,
any automorphism is uniquely determined by where it sends one vertex.
Barring those two conditions, the statement would be that the choice of image of a vertex determines
the automorphism on the weakly connected component of the vertex.
-/
lemma eq_of_eq_on  (φ ψ : 𝑨l V ι ≃qc 𝑨l V ι) (v₀ : V)
  (ha : mul_action.is_pretransitive M V)
  (hv₀ : φ.to_prefunctor.obj v₀ = ψ.to_prefunctor.obj v₀)
  (h : subgroup.closure (set.range ι) = (⊤ : subgroup M)) : φ = ψ :=
begin
  apply covering_iso.ext,
  apply iso.to_prefunctor_ext,
  apply (𝑨c _ _).eq_of_eq_of_preconnected _ _ hv₀,
  { rw [φ.commute_left, ψ.commute_left], },
  { rintro u v,
    refine (action_graph.reachable_iff V ι u v).mpr _,
    simp only [h, subgroup.mem_top, exists_true_left],
    exact ha.exists_smul_eq u v, },
end

section schreier_graph

/--
A Schreier coset graph is the Schreier graph of the action of a group `M` on the cosets `M ⧸ H`.
-/
abbreviation schreier_graph (H : subgroup M) := 𝑨 (M ⧸ H) ι
abbreviation schreier_graph_labelling (H : subgroup M) := 𝑨l (M ⧸ H) ι

notation `𝑺` := schreier_graph
notation `𝑺l` := schreier_graph_labelling

@[simps] noncomputable def from_coset_graph (v₀ : V) :
  𝑺 ι (mul_action.stabilizer M v₀) ⥤q 𝑨 (mul_action.orbit M v₀) ι :=
{ obj := (mul_action.orbit_equiv_quotient_stabilizer M v₀).symm,
  map := λ X Y e, ⟨e.val, by obtain ⟨e,rfl⟩ := e;
                          simp only [mul_action.smul_orbit_equiv_quotient_stabilizer_symm_apply]⟩ }

lemma from_coset_graph_labelling (v₀ : V) :
  (from_coset_graph V ι v₀) ⋙q 𝑨l (mul_action.orbit M v₀) ι =
  𝑨l (M ⧸ mul_action.stabilizer M v₀) ι :=
begin
  dsimp only [from_coset_graph, action_graph_labelling],
  fapply prefunctor.ext,
  { simp only [eq_iff_true_of_subsingleton, implies_true_iff], },
  { rintros _ _ ⟨e, he⟩,
    simp only [prefunctor.comp_map, eq_rec_constant, action_graph.star_equiv_apply, subtype.coe_mk], },
end

@[simps] noncomputable def to_coset_graph (v₀ : V) :
  𝑨 (mul_action.orbit M v₀) ι ⥤q 𝑺 ι (mul_action.stabilizer M v₀) :=
{ obj := (mul_action.orbit_equiv_quotient_stabilizer M v₀),
  map := λ X Y e, ⟨e.val, by obtain ⟨e,rfl⟩ := e;
                          simp only [mul_action.smul_orbit_equiv_quotient_stabilizer_apply]⟩ }

lemma to_coset_graph_labelling (v₀ : V) :
  (to_coset_graph V ι v₀) ⋙q 𝑨l (M ⧸ mul_action.stabilizer M v₀) ι =
  𝑨l (mul_action.orbit M v₀) ι:=
begin
  dsimp only [to_coset_graph, action_graph_labelling],
  fapply prefunctor.ext,
  { simp only [eq_iff_true_of_subsingleton, implies_true_iff], },
  { rintros _ _ ⟨_,_⟩,
    simp only [prefunctor.comp_map, eq_rec_constant, action_graph.star_equiv_apply, subtype.coe_mk], },
end

lemma from_coset_graph_to_coset_graph (v₀ : V) :
  from_coset_graph V ι v₀ ⋙q to_coset_graph V ι v₀ = 𝟭q _ :=
begin
  apply (𝑨c _ _).eq_of_eq_obj,
  { simp only [to_coset_graph_labelling, from_coset_graph_labelling, prefunctor.comp_assoc,
               prefunctor.id_comp], },
  { ext ⟨_⟩,
    simp only [prefunctor.comp_obj, from_coset_graph_obj, to_coset_graph_obj,
               equiv.apply_symm_apply, prefunctor.id_obj, id.def], },
end

lemma to_coset_graph_from_coset_graph (v₀ : V) :
  to_coset_graph V ι v₀ ⋙q from_coset_graph V ι v₀ = 𝟭q _ :=
begin
  apply (𝑨c _ _).eq_of_eq_obj,
  { simp only [to_coset_graph_labelling, from_coset_graph_labelling, prefunctor.comp_assoc,
               prefunctor.id_comp], },
  { ext _,
    simp only [prefunctor.comp_obj, to_coset_graph_obj, from_coset_graph_obj,
               equiv.symm_apply_apply, prefunctor.id_obj, id.def], },
end

noncomputable def orbit_stabilizer_covering_iso (v₀ : V) :
  𝑨l (mul_action.orbit M v₀) ι ≃qc 𝑺l ι (mul_action.stabilizer M v₀) :=
{ inv_prefunctor := from_coset_graph V ι v₀,
  to_prefunctor := to_coset_graph V ι v₀,
  right_inv := from_coset_graph_to_coset_graph V ι v₀,
  left_inv := to_coset_graph_from_coset_graph V ι v₀,
  commute_left := to_coset_graph_labelling V ι v₀,
  commute_right := from_coset_graph_labelling V ι v₀ }

section automs

variables {N : subgroup M} [Nn : N.normal]
include Nn

@[simps] def as_autom (g : M) : 𝑺 ι N ⥤q 𝑺 ι N :=
{ obj := λ x, equiv_action_graph ((equiv_action_graph.symm x) * (g⁻¹)),
  map := λ x y a, ⟨a.val, by
    begin
      obtain ⟨a,rfl⟩ := a,
      obtain ⟨x⟩ := x,
      change ι a • ((↑x : M ⧸ N) * (↑g)⁻¹) = ι a • (↑x : M ⧸ N) * (↑g)⁻¹,
      simpa only [mul_action.quotient.smul_coe, smul_eq_mul, quotient_group.coe_mul, mul_assoc],
    end⟩ }

lemma as_autom_labelling (g : M) :
  as_autom ι g ⋙q 𝑺l ι N = 𝑺l ι N :=
begin
  dsimp only [as_autom, action_graph_labelling],
  fapply prefunctor.ext,
  { simp only [eq_iff_true_of_subsingleton, implies_true_iff], },
  { rintro _ _ ⟨_, rfl⟩,
    simp [subtype.coe_mk, prefunctor.comp_map, action_graph_labelling_map,
    eq_rec_constant], },
end

lemma as_autom_one : as_autom ι 1 = 𝟭q (𝑺 ι N) :=
begin
  fapply (𝑨c _ _).eq_of_eq_obj,
  { rw [as_autom_labelling, prefunctor.id_comp], },
  { ext x,
    simp only [equiv_action_graph_symm_apply, quotient_group.coe_one, inv_one, mul_one,
               equiv_action_graph_apply, prefunctor.id_obj, id.def, as_autom], },
end

lemma as_autom_mul (g h : M) :
  (as_autom ι (g * h) : 𝑺 ι N ⥤q  𝑺 ι N) = (as_autom ι h) ⋙q (as_autom ι g) :=
begin
  fapply (𝑨c _ _).eq_of_eq_obj,
  { simp_rw [prefunctor.comp_assoc, as_autom_labelling], },
  { ext x,
    simp only [equiv_action_graph_symm_apply, equiv_action_graph_apply, as_autom,
               quotient_group.coe_mul, mul_inv_rev, prefunctor.comp_obj, mul_assoc], },
end

def as_autom_covering_iso (g : M) : 𝑺l ι N ≃qc 𝑺l ι N :=
{ to_prefunctor := as_autom ι g,
  inv_prefunctor := as_autom ι (g⁻¹),
  left_inv := by simp [←as_autom_mul, ←as_autom_one],
  right_inv := by simp [←as_autom_mul, ←as_autom_one],
  commute_left := as_autom_labelling ι g,
  commute_right := as_autom_labelling ι (g⁻¹), }

lemma as_autom_eq_iff (g₁ g₂ : M) :
  (as_autom ι g₁ : 𝑺 ι N ⥤q 𝑺 ι N) = (as_autom ι g₂ : 𝑺 ι N ⥤q 𝑺 ι N) ↔ g₁ / g₂ ∈ N :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { dsimp only [as_autom] at h,
    simp only [subtype.val_eq_coe, equiv_action_graph_symm_apply,
               equiv_action_graph_apply] at h ⊢,
    simpa [←quotient_group.coe_one, quotient_group.eq_iff_div_mem] using
            (congr_fun h.left (equiv_action_graph 1)), },
  { fapply (𝑨c _ _).eq_of_eq_obj,
    { simp_rw [as_autom_labelling], },
    { ext ⟨x⟩,
      change (↑x : M ⧸ N) * (g₁)⁻¹ = (↑x : M ⧸ N) * (↑g₂)⁻¹,
      simpa [quotient_group.eq_iff_div_mem] using h, }, },
end

lemma exists_as_autom {φ : 𝑺l ι N ≃qc 𝑺l ι N} {g : M}
  (h : subgroup.closure (set.range ι) = (⊤ : subgroup M))
  (hv : φ.obj (1 : M ⧸ N) = quotient_group.mk g) : φ = as_autom_covering_iso ι (g⁻¹) :=
begin
  apply covering_iso.ext,
  apply iso.to_prefunctor_ext,
  fapply (𝑨c _ _).eq_of_eq_of_preconnected,
  { simp [covering_iso.commute_left], },
  { rintro ⟨x⟩ ⟨y⟩,
    refine (action_graph.reachable_iff _ _ _ _).mpr _,
    simp only [h, subgroup.mem_top, exists_true_left],
    refine ⟨y * x⁻¹, _⟩,
    change (y * x⁻¹) • quotient_group.mk x = quotient_group.mk y,
    simp only [mul_action.quotient.smul_mk, smul_eq_mul, inv_mul_cancel_right], },
  { exact (1 : M ⧸ N), },
  { simpa [hv, as_autom_covering_iso], },
end

end automs

end schreier_graph

/--
The Cayley graph of `M` w.r.t. `ι : S → M` is the Schreier coset graph where `H` is the trivial
subgroup of `M`.
-/
abbreviation cayley_graph := 𝑺 ι (⊥ : subgroup M)
abbreviation cayley_graph_labelling := 𝑺l ι (⊥ : subgroup M)

notation `𝑪` := cayley_graph
notation `𝑪l` := cayley_graph_labelling

namespace cayley_graph

variables {N : subgroup M} [Nn : N.normal]
include Nn

-- Maybe there is an official mathlib way to state that `ι` generates the group.
lemma preconnected_iff : is_preconnected (symmetrify $ 𝑪 ι) ↔ subgroup.closure (set.range ι) = ⊤ := sorry

def cayley_iso_schreier : 𝑪l ((quotient_group.mk : M → M ⧸ N) ∘ ι) ≃qc (𝑺l ι N) := sorry


end cayley_graph

end group_action

end quiver
