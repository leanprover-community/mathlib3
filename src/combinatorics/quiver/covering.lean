/-
Copyright (c) 2022 Antoine Labelle, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle, Rémi Bottinelli
-/
import combinatorics.quiver.basic
import combinatorics.quiver.symmetric
import combinatorics.quiver.cast
import combinatorics.quiver.single_obj
import combinatorics.quiver.iso

/-!
# Covering

This file defines coverings of quivers as prefunctors that are bijective on the
so-called stars and costars at each vertex of the domain.

## Main definitions

* `quiver.star u` is the type of all arrows with source `u`;
* `quiver.costar u` is the type of all arrows with target `u`;
* `prefunctor.star φ u` is the obvious function `star u → star (φ.obj u)`;
* `prefunctor.costar φ u` is the obvious function `costar u → costar (φ.obj u)`;
* `prefunctor.is_covering φ` means that `φ.star u` and `φ.costar u` are bijections for all `u`;
* `quiver.star_path u` is the type of all paths with source `u`;
* `prefunctor.star_path u` is the obvious function `star_path u → star_path (φ.obj u)`.

## Main statements

* `prefunctor.path_star_bijective` states that if `φ` is a covering, then `φ.star_path u` is a
  bijection for al `u`.
  In other words, any path in the codomain of `φ` lifts uniquely to its domain.

## TODO

Clean up the namespaces by renaming `prefunctor` to `quiver.prefunctor`.

## Tags

Cover, covering, quiver, path, lift
-/

open function quiver

universes u v w z

variables {U : Type*} [quiver.{u+1} U]
          {V : Type*} [quiver.{v+1} V] (φ : U ⥤q V)
          {W : Type*} [quiver.{w+1} W] (ψ : V ⥤q W)
          {Z : Type*} [quiver.{z+1} Z]

/-- The `quiver.star` at a vertex is the collection of arrows whose source is the vertex. -/
@[reducible] def quiver.star (u : U) := Σ (v : U), (u ⟶ v)

/-- The `quiver.costar` at a vertex is the collection of arrows whose target is the vertex. -/
@[reducible] def quiver.costar (u : U) := Σ (v : U), (v ⟶ u)

@[simp] lemma quiver.star_eq_iff {u : U} (F G : quiver.star u) :
  F = G ↔ ∃ h : F.1 = G.1, F.2.cast rfl h = G.2 :=
begin
  split,
  { rintro ⟨⟩, exact ⟨rfl, rfl⟩, },
  { induction F, induction G, rintro ⟨h, H⟩, cases h, cases H,
    simp only [eq_self_iff_true, heq_iff_eq, and_self], }
end

@[simp] lemma quiver.costar_eq_iff {u : U} (F G : quiver.costar u) :
  F = G ↔ ∃ h : F.1 = G.1, F.2.cast h rfl = G.2 :=
begin
  split,
  { rintro ⟨⟩, exact ⟨rfl, rfl⟩, },
  { induction F, induction G, rintro ⟨h, H⟩, cases h, cases H,
    simp only [eq_self_iff_true, heq_iff_eq, and_self], }
end

/-- A prefunctor induces a map of quiver.stars at any vertex. -/
@[simps] def prefunctor.star (u : U) : quiver.star u → quiver.star (φ.obj u) :=
λ F, ⟨φ.obj F.1, φ.map F.2⟩

/-- A prefunctor induces a map of quiver.costars at any vertex. -/
@[simps] def prefunctor.costar (u : U) : quiver.costar u → quiver.costar (φ.obj u) :=
λ F, ⟨φ.obj F.1, φ.map F.2⟩

@[simp] lemma prefunctor.star_apply {u v : U} (e : u ⟶ v) :
  φ.star u ⟨v, e⟩ = ⟨φ.obj v, φ.map e⟩ := rfl

@[simp] lemma prefunctor.costar_apply {u v : U} (e : v ⟶ u) :
  φ.costar u ⟨v, e⟩ = ⟨φ.obj v, φ.map e⟩ := rfl

@[simp] lemma prefunctor.star_comp (u : U) :
  (φ ⋙q ψ).star u = (ψ.star (φ.obj u)) ∘ ((φ.star) u) := rfl

@[simp] lemma prefunctor.costar_comp (u : U) :
  (φ ⋙q ψ).costar u = (ψ.costar (φ.obj u)) ∘ ((φ.costar) u) := rfl

/-- A prefunctor is a covering of quivers if it defines bijections on all stars and costars. -/
@[reducible] def prefunctor.is_covering :=
  (∀ u, function.bijective (φ.star u)) ∧ (∀ u, function.bijective (φ.costar u))

@[simp] lemma prefunctor.map_inj_of_is_covering (hφ : φ.is_covering) {u v : U} :
  function.injective (λ (f : u ⟶ v), φ.map f) :=
begin
  rintro f g he,
  have : φ.star u (⟨_, f⟩ : quiver.star u) = φ.star u (⟨_, g⟩ : quiver.star u), by
  { simpa only [prefunctor.star, eq_self_iff_true, heq_iff_eq, true_and] using he, },
  simpa only [eq_self_iff_true, heq_iff_eq, true_and] using (hφ.left u).left this,
end

lemma prefunctor.is_covering.comp (hφ : φ.is_covering) (hψ : ψ.is_covering) :
  (φ ⋙q ψ).is_covering :=
⟨λ u, (hψ.left (φ.obj u)).comp (hφ.left u), λ u, (hψ.right (φ.obj u)).comp (hφ.right u)⟩

lemma prefunctor.is_covering.of_comp_right (hψ : ψ.is_covering) (hφψ : (φ ⋙q ψ).is_covering) :
  φ.is_covering :=
⟨ λ u, (function.bijective.of_comp_iff' (hψ.left $ φ.obj u) (φ.star u)).mp (hφψ.left u),
  λ u, (function.bijective.of_comp_iff' (hψ.right $ φ.obj u) (φ.costar u)).mp (hφψ.right u)⟩

lemma prefunctor.is_covering.of_comp_left (hφ : φ.is_covering) (hφψ : (φ ⋙q ψ).is_covering)
  (φsur : function.surjective φ.obj) : ψ.is_covering :=
begin
  refine ⟨λ v, _, λ v, _⟩;
  obtain ⟨u, rfl⟩ := φsur v,
  exacts [(function.bijective.of_comp_iff _ (hφ.left u)).mp (hφψ.left u),
          (function.bijective.of_comp_iff _ (hφ.right u)).mp (hφψ.right u)],
end

/--
The star of the symmetrification of a quiver at a vertex `u` is equivalent to the sum of the star
and the costar at `u` in the original quiver.
 -/
@[simps] def quiver.symmetrify_star (u : U) :
  quiver.star (symmetrify.of.obj u) ≃ quiver.star u ⊕ quiver.costar u :=
begin
  fsplit,
  { rintro ⟨v, (f|g)⟩, exacts [sum.inl ⟨v, f⟩, sum.inr ⟨v, g⟩], },
  { rintro (⟨v, f⟩|⟨v, g⟩), exacts [⟨v, f.to_pos⟩, ⟨v, g.to_neg⟩], },
  { rintro ⟨v, (f|g)⟩, simp, },
  { rintro (⟨v, f⟩|⟨v, g⟩), simp, },
end

@[simp] lemma quiver.symmetrify_star_lapply {u v : U} (e : u ⟶ v) :
  quiver.symmetrify_star u ⟨v, sum.inl e⟩ = sum.inl ⟨v, e⟩ := rfl

@[simp] lemma quiver.symmetrify_star_rapply {u v : U} (e : v ⟶ u) :
  quiver.symmetrify_star u ⟨v, sum.inr e⟩ = sum.inr ⟨v, e⟩ := rfl

/--
The costar of the symmetrification of a quiver at a vertex `u` is equivalent to the sum of the
costar and the star at `u` in the original quiver.
 -/
@[simps] def symmetrify_costar (u : U) :
  quiver.costar (symmetrify.of.obj u) ≃ quiver.costar u ⊕ quiver.star u :=
begin
  fsplit,
  { rintro ⟨v, (f|g)⟩, exacts [sum.inl ⟨v, f⟩, sum.inr ⟨v, g⟩], },
  { rintro (⟨v, f⟩|⟨v, g⟩), exacts [⟨v, quiver.hom.to_pos f⟩, ⟨v, quiver.hom.to_neg g⟩], },
  { rintro ⟨v, (f|g)⟩, simp, },
  { rintro (⟨v, f⟩|⟨v, g⟩), simp, },
end

lemma prefunctor.symmetrify_star (u : U) : φ.symmetrify.star u =
 (quiver.symmetrify_star (φ.obj u)).symm ∘ sum.map (φ.star u) (φ.costar u) ∘
 quiver.symmetrify_star u :=
begin
  rw equiv.eq_symm_comp,
  ext ⟨v, (f|g)⟩;
  simp,
end

protected lemma prefunctor.symmetrify_costar (u : U) : φ.symmetrify.costar u =
 (symmetrify_costar (φ.obj u)).symm ∘ sum.map (φ.costar u) (φ.star u) ∘ symmetrify_costar u :=
begin
  rw equiv.eq_symm_comp,
  ext ⟨v, (f|g)⟩;
  simp,
end

protected lemma prefunctor.is_covering.symmetrify {φ : U ⥤q V} (hφ : φ.is_covering) :
  φ.symmetrify.is_covering :=
begin
  refine ⟨λ u, _, λ u, _⟩;
  simp only [φ.symmetrify_star u, φ.symmetrify_costar u,
             equiv_like.comp_bijective, equiv_like.bijective_comp],
  exacts [⟨function.injective.sum_map (hφ.left u).left (hφ.right u).left,
           function.surjective.sum_map (hφ.left u).right (hφ.right u).right⟩,
          ⟨function.injective.sum_map (hφ.right u).left (hφ.left u).left,
           function.surjective.sum_map (hφ.right u).right (hφ.left u).right⟩],
end

/-- The path star at a vertex `u` is the type of all paths starting at `u`. -/
@[reducible] def quiver.path_star (u : U) := Σ v : U, path u v

@[simp] lemma quiver.path_star_eq_iff {u : U} (P Q : quiver.path_star u) :
  P = Q ↔ ∃ h : P.1 = Q.1, P.2.cast rfl h = Q.2 :=
begin
  split,
  { rintro rfl, exact ⟨rfl, rfl⟩, },
  { rintro ⟨h, H⟩, induction P, induction Q, cases h, cases H, refl, }
end

/-- A prefunctor induces a map of path stars. -/
def prefunctor.path_star (u : U) : quiver.path_star u → quiver.path_star (φ.obj u) :=
λ p, ⟨φ.obj p.1, φ.map_path p.2⟩

@[simp] lemma prefunctor.path_star_apply {u v : U} (p : path u v) :
  φ.path_star u ⟨v, p⟩ = ⟨φ.obj v, φ.map_path p⟩ := rfl

theorem prefunctor.path_star_bijective (hφ : φ.is_covering) (u : U) :
  function.bijective (φ.path_star u) :=
begin
  dsimp [prefunctor.path_star],
  split,
  { rintro ⟨v₁, p₁⟩,
    induction p₁ with  x₁ y₁ p₁ e₁ ih;
    rintro ⟨y₂, p₂⟩; cases p₂ with x₂ _ p₂ e₂;
    intro h;
    simp only [prefunctor.path_star_apply, prefunctor.map_path_nil,
                 prefunctor.map_path_cons] at h,
    { exfalso,
      cases h with h h',
      rw [←path.eq_cast_iff_heq rfl h.symm, path.cast_cons] at h',
      exact (path.nil_ne_cons _ _) h', },
    { exfalso,
      cases h with h h',
      rw [←path.cast_eq_iff_heq rfl h, path.cast_cons] at h',
      exact (path.cons_ne_nil _ _) h', },
    { cases h with hφy h',
      rw [←path.cast_eq_iff_heq rfl hφy, path.cast_cons, path.cast_rfl_rfl] at h',
      have hφx := path.obj_eq_of_cons_eq_cons h',
      have hφp := path.heq_of_cons_eq_cons h',
      have hφe := heq.trans (hom.cast_heq rfl hφy _).symm (path.hom_heq_of_cons_eq_cons h'),
      have h_path_star : φ.path_star u ⟨x₁, p₁⟩ = φ.path_star u ⟨x₂, p₂⟩,
      { simp only [prefunctor.path_star_apply], exact ⟨hφx, hφp⟩, },
      cases ih h_path_star,
      have h_star : φ.star x₁ ⟨y₁, e₁⟩ = φ.star x₁ ⟨y₂, e₂⟩,
      { simp only [prefunctor.star_apply], exact ⟨hφy, hφe⟩, },
      cases (hφ.1 x₁).1 h_star, refl, }, },
  { rintro ⟨v, p⟩,
    induction p with v' v'' p' ev ih,
    { use ⟨u, path.nil⟩,
      simp only [prefunctor.map_path_nil, eq_self_iff_true, heq_iff_eq, and_self], },
    { obtain ⟨⟨u', q'⟩, h⟩ := ih,
      simp only at h,
      obtain ⟨rfl,rfl⟩ := h,
      obtain ⟨⟨u'', eu⟩, k⟩ := (hφ.left u').right ⟨_, ev⟩,
      simp at k,
      obtain ⟨rfl,rfl⟩ := k,
      use ⟨_, q'.cons eu⟩,
      simp only [prefunctor.map_path_cons, eq_self_iff_true, heq_iff_eq, and_self], } }
end

section single_obj

variable (α : Type*)

@[simps] def _root_.sigma.unit (β : unit → Type*) : (Σ (x : unit), β x) ≃ β unit.star :=
{ to_fun := λ (p : sigma β), p.rec_on $ punit.rec $ by { exact id }, -- term mode unhappy
  inv_fun := λ h, ⟨unit.star, h⟩,
  left_inv := λ ⟨(), h⟩, by simp only [id.def, heq_iff_eq, eq_self_iff_true, and_self],
  right_inv := λ h, by simp only [id.def] }

/--
The star around the single object is equivalent to the type of arrows used for `single_obj`.
Confusing nomenclature though.
-/
def single_obj.star_equiv : quiver.star (single_obj.star α) ≃ α := sigma.unit _

/--
The path star around the single object is equivalent to the type of lists over the type of arrows
used for `single_obj`.
-/
def single_obj.path_star_equiv : quiver.path_star (single_obj.star α) ≃ list α :=
(sigma.unit _).trans single_obj.path_equiv_list

end single_obj

section has_involutive_reverse

variables [has_involutive_reverse U] [has_involutive_reverse V] [prefunctor.map_reverse φ]

/-- In a quiver with involutive inverses, the star and costar at any vertex are equivalent. -/
@[simps] def quiver.star_equiv_costar (u : U) :
  quiver.star u ≃ quiver.costar u :=
{ to_fun := λ e, ⟨e.1, reverse e.2⟩,
  inv_fun := λ e, ⟨e.1, reverse e.2⟩,
  left_inv := λ e, by simp,
  right_inv := λ e, by simp }

@[simp] lemma quiver.star_equiv_costar_apply {u v : U} (e : u ⟶ v) :
  quiver.star_equiv_costar u ⟨v, e⟩ = ⟨v, reverse e⟩ := rfl
@[simp] lemma quiver.star_equiv_costar_symm_apply {u v : U} (e : v ⟶ u) :
  (quiver.star_equiv_costar u).symm ⟨v, e⟩ = ⟨v, reverse e⟩ := rfl

lemma prefunctor.costar_conj_star (u : U) : (φ.costar u) =
  (quiver.star_equiv_costar (φ.obj u)) ∘ (φ.star u) ∘ (quiver.star_equiv_costar u).symm :=
by { ext ⟨v, f⟩; simp, }

lemma prefunctor.bijective_costar_iff_bijective_star (u : U) :
  function.bijective (φ.costar u) ↔ function.bijective (φ.star u) :=
begin
  rw [prefunctor.costar_conj_star, function.bijective.of_comp_iff', function.bijective.of_comp_iff];
  exact equiv.bijective _,
end

lemma prefunctor.is_covering_of_bijective_star (h : ∀ u, function.bijective (φ.star u)) :
  φ.is_covering := ⟨h, λ u, (φ.bijective_costar_iff_bijective_star u).2 (h u)⟩

lemma prefunctor.is_covering_of_bijective_costar (h : ∀ u, function.bijective (φ.costar u)) :
  φ.is_covering := ⟨λ u, (φ.bijective_costar_iff_bijective_star u).1 (h u), h⟩

end has_involutive_reverse

section covering_maps

/- The following all have bad names: -/

lemma prefunctor.is_covering.eq_star_of_eq
  {ψ : V ⥤q W} (ψc : ψ.is_covering) {θ₁ θ₂ : U ⥤q V} (hθ : θ₁ ⋙q ψ = θ₂ ⋙q ψ)
  {u u' : U} (e : u ⟶ u') (hu : θ₁.obj u = θ₂.obj u) :
  ∃ hu' : θ₁.obj u' = θ₂.obj u', hom.cast hu hu' (θ₁.map e) = θ₂.map e :=
begin
  have he : ψ.star _ ⟨_, hom.cast hu rfl (θ₁.map e)⟩ = ψ.star _ ⟨_, θ₂.map e⟩, by
  { rw [prefunctor.star], dsimp,
    rw [prefunctor.map_cast, ←prefunctor.comp_map, ←prefunctor.comp_map,
        ←prefunctor.map_cast_eq_of_eq hθ, quiver.star_eq_iff],
    have hu' := congr_arg (λ F : U ⥤q W, F.obj u') hθ, dsimp at hu',
    refine ⟨hu', _⟩,
    rw [hom.cast_cast],
    apply hom.cast_congr, },
  obtain ⟨hu', he'⟩ := (quiver.star_eq_iff _ _).mp ((ψc.1 (θ₂.obj u)).1 he),
  rw [hom.cast_cast] at he',
  exact ⟨hu', he'⟩,
end

lemma prefunctor.is_covering.eq_costar_of_eq
  {ψ : V ⥤q W} (ψc : ψ.is_covering) {θ₁ θ₂ : U ⥤q V} (hθ : θ₁ ⋙q ψ = θ₂ ⋙q ψ)
  {u u' : U} (e : u' ⟶ u) (hu : θ₁.obj u = θ₂.obj u) :
  ∃ hu' : θ₁.obj u' = θ₂.obj u', hom.cast hu' hu (θ₁.map e) = θ₂.map e :=
begin
  have he : ψ.costar _ ⟨_, hom.cast rfl hu (θ₁.map e)⟩ = ψ.costar _ ⟨_, θ₂.map e⟩, by
  { simp only [prefunctor.costar, ←prefunctor.comp_obj, ←prefunctor.comp_map, hθ,
               prefunctor.map_cast],
    simp only [hom.cast, rec_heq_iff_heq],
    refine ⟨rfl, _⟩,
    congr' 1, },
  obtain ⟨hu', he'⟩ := (quiver.costar_eq_iff _ _).mp ((ψc.2 (θ₂.obj u)).1 he),
  simp only [hom.cast_cast] at he',
  exact ⟨hu', he'⟩,
end

lemma prefunctor.is_covering.eq_of_eq_obj
  {ψ : V ⥤q W} (ψc : ψ.is_covering) {θ₁ θ₂ : U ⥤q V}
  (hθ : θ₁ ⋙q ψ = θ₂ ⋙q ψ) (hθobj : θ₁.obj = θ₂.obj) : θ₁ = θ₂ :=
begin
  fapply prefunctor.ext,
  { rintro x, exact congr_fun hθobj x, },
  { rintro x y e,
    obtain ⟨hy,he⟩ := ψc.eq_star_of_eq hθ e (congr_fun hθobj x),
    rw hom.cast_eq_iff_eq_cast at he,
    exact he, },
end

lemma prefunctor.is_covering.eq_of_eq_of_path
  {ψ : V ⥤q W} (ψc : ψ.is_covering) {θ₁ θ₂ : U ⥤q V}
  (hθ : θ₁ ⋙q ψ = θ₂ ⋙q ψ) {u u' : U}
  (p : path (symmetrify.of.obj u) (symmetrify.of.obj u')) :
  θ₁.obj u = θ₂.obj u → θ₁.obj u' = θ₂.obj u' :=
begin
  revert u u',
  change ∀ {u u' : symmetrify U}, path u u' → θ₁.obj u = θ₂.obj u → θ₁.obj u' = θ₂.obj u',
  rintro _ _ p, induction p with v w q e ih,
  { exact id, },
  { rintro hu,
    obtain (f|g) := e,
    { exact (ψc.eq_star_of_eq hθ f $ ih hu).some, },
    { exact (ψc.eq_costar_of_eq hθ g $ ih hu).some, }, },
end

lemma prefunctor.is_covering.eq_of_eq_of_preconnected
  {ψ : V ⥤q W} (ψc : ψ.is_covering) {θ₁ θ₂ : U ⥤q V}
  (hθ : θ₁ ⋙q ψ = θ₂ ⋙q ψ)
  (p : is_preconnected (quiver.symmetrify U)) {u : U} (hu : θ₁.obj u = θ₂.obj u) : θ₁ = θ₂ :=
begin
  apply ψc.eq_of_eq_obj hθ,
  ext u',
  apply ψc.eq_of_eq_of_path hθ (p u u').some hu,
end

@[ext] structure covering_iso (φ : U ⥤q W) (ψ : V ⥤q W) extends iso U V :=
(commute_left : to_prefunctor ⋙q ψ = φ)
(commute_right : inv_prefunctor ⋙q φ = ψ) -- `commute_right` should follow from `commute_left`

instance (φ : U ⥤q W) (ψ : V ⥤q W) : has_coe (covering_iso φ ψ) (iso U V) :=
⟨covering_iso.to_iso⟩

@[simps] def covering_iso.refl  (φ : U ⥤q W) : covering_iso φ φ :=
{ to_iso := iso.refl _,
  commute_left := by simp [iso.refl],
  commute_right := by simp [iso.refl] }

@[simps] def covering_iso.symm {φ : U ⥤q W} {ψ : V ⥤q W} (θ : covering_iso φ ψ) : covering_iso ψ φ :=
{ to_iso := θ.to_iso.symm,
  commute_left := by simp [iso.symm, covering_iso.commute_right],
  commute_right := by simp [iso.symm, covering_iso.commute_left] }

@[simps] def covering_iso.trans {φ : U ⥤q W} {ψ : V ⥤q W} {σ : Z ⥤q W}
  (θ : covering_iso φ ψ) (ζ : covering_iso ψ σ) : covering_iso φ σ :=
{ to_iso := θ.to_iso.trans ζ.to_iso,
  commute_left := by simp [iso.trans, covering_iso.commute_left],
  commute_right := by simp [iso.trans, covering_iso.commute_right] }

infix ` ≃qc `:60 := covering_iso



end covering_maps
