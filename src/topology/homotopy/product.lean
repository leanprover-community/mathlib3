/-
Copyright (c) 2021 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import topology.constructions
import topology.homotopy.path

/-!
# Product of homotopies

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we introduce definitions for the product of
homotopies. We show that the products of relative homotopies
are still relative homotopies. Finally, we specialize to the case
of path homotopies, and provide the definition for the product of path classes.
We show various lemmas associated with these products, such as the fact that
path products commute with path composition, and that projection is the inverse
of products.

## Definitions
### General homotopies
- `continuous_map.homotopy.pi homotopies`: Let f and g be a family of functions
  indexed on I, such that for each i ∈ I, fᵢ and gᵢ are maps from A to Xᵢ.
  Let `homotopies` be a family of homotopies from fᵢ to gᵢ for each i.
  Then `homotopy.pi homotopies` is the canonical homotopy
  from ∏ f to ∏ g, where ∏ f is the product map from A to Πi, Xᵢ,
  and similarly for ∏ g.

- `continuous_map.homotopy_rel.pi homotopies`: Same as `continuous_map.homotopy.pi`, but
  all homotopies are done relative to some set S ⊆ A.

- `continuous_map.homotopy.prod F G` is the product of homotopies F and G,
   where F is a homotopy between f₀ and f₁, G is a homotopy between g₀ and g₁.
   The result F × G is a homotopy between (f₀ × g₀) and (f₁ × g₁).
   Again, all homotopies are done relative to S.

- `continuous_map.homotopy_rel.prod F G`: Same as `continuous_map.homotopy.prod`, but
  all homotopies are done relative to some set S ⊆ A.

### Path products
- `path.homotopic.pi` The product of a family of path classes, where a path class is an equivalence
  class of paths up to path homotopy.

- `path.homotopic.prod` The product of two path classes.
-/

noncomputable theory

namespace continuous_map
open continuous_map

section pi

variables {I A : Type*} {X : I → Type*} [Π i, topological_space (X i)] [topological_space A]
  {f g : Π i, C(A, X i)} {S : set A}

/-- The product homotopy of `homotopies` between functions `f` and `g` -/
@[simps]
def homotopy.pi (homotopies : Π i, homotopy (f i) (g i)) : homotopy (pi f) (pi g) :=
{ to_fun := λ t i, homotopies i t,
  map_zero_left' := λ t, by { ext i, simp only [pi_eval, homotopy.apply_zero] },
  map_one_left' := λ t, by { ext i, simp only [pi_eval, homotopy.apply_one] } }

/-- The relative product homotopy of `homotopies` between functions `f` and `g` -/
@[simps]
def homotopy_rel.pi (homotopies : Π i : I, homotopy_rel (f i) (g i) S) :
  homotopy_rel (pi f) (pi g) S :=
{ prop' :=
  begin
    intros t x hx,
    dsimp only [coe_mk, pi_eval, to_fun_eq_coe, homotopy_with.coe_to_continuous_map],
    simp only [function.funext_iff, ← forall_and_distrib],
    intro i,
    exact (homotopies i).prop' t x hx,
  end,
  ..(homotopy.pi (λ i, (homotopies i).to_homotopy)), }

end pi

section prod

variables {α β : Type*} [topological_space α] [topological_space β]
  {A : Type*} [topological_space A]
  {f₀ f₁ : C(A, α)} {g₀ g₁ : C(A, β)} {S : set A}

/-- The product of homotopies `F` and `G`,
  where `F` takes `f₀` to `f₁`  and `G` takes `g₀` to `g₁` -/
@[simps]
def homotopy.prod (F : homotopy f₀ f₁) (G : homotopy g₀ g₁) :
  homotopy (prod_mk f₀ g₀) (prod_mk f₁ g₁) :=
{ to_fun := λ t, (F t, G t),
  map_zero_left' := λ x, by simp only [prod_eval, homotopy.apply_zero],
  map_one_left' := λ x, by simp only [prod_eval, homotopy.apply_one] }

/-- The relative product of homotopies `F` and `G`,
  where `F` takes `f₀` to `f₁`  and `G` takes `g₀` to `g₁` -/
@[simps]
def homotopy_rel.prod (F : homotopy_rel f₀ f₁ S) (G : homotopy_rel g₀ g₁ S) :
  homotopy_rel (prod_mk f₀ g₀) (prod_mk f₁ g₁) S :=
{ prop' :=
  begin
    intros t x hx,
    have hF := F.prop' t x hx,
    have hG := G.prop' t x hx,
    simp only [coe_mk, prod_eval, prod.mk.inj_iff, homotopy.prod] at hF hG ⊢,
    exact ⟨⟨hF.1, hG.1⟩, ⟨hF.2, hG.2⟩⟩,
  end,
  ..(homotopy.prod F.to_homotopy G.to_homotopy) }

end prod
end continuous_map


namespace path.homotopic
local attribute [instance] path.homotopic.setoid
local infix ` ⬝ `:70 := quotient.comp

section pi

variables {ι : Type*} {X : ι → Type*} [∀ i, topological_space (X i)]
  {as bs cs : Π i, X i}

/-- The product of a family of path homotopies. This is just a specialization of `homotopy_rel` -/
def pi_homotopy (γ₀ γ₁ : Π i, path (as i) (bs i)) (H : ∀ i, path.homotopy (γ₀ i) (γ₁ i)) :
  path.homotopy (path.pi γ₀) (path.pi γ₁) := continuous_map.homotopy_rel.pi H

/-- The product of a family of path homotopy classes -/
def pi (γ : Π i, path.homotopic.quotient (as i) (bs i)) : path.homotopic.quotient as bs :=
(quotient.map path.pi
  (λ x y hxy, nonempty.map (pi_homotopy x y) (classical.nonempty_pi.mpr hxy)))
  (quotient.choice γ)

lemma pi_lift (γ : Π i, path (as i) (bs i)) : path.homotopic.pi (λ i, ⟦γ i⟧) = ⟦path.pi γ⟧ :=
by { unfold pi, simp, }

/-- Composition and products commute.
  This is `path.trans_pi_eq_pi_trans` descended to path homotopy classes -/
lemma comp_pi_eq_pi_comp
  (γ₀ : Π i, path.homotopic.quotient (as i) (bs i))
  (γ₁ : Π i, path.homotopic.quotient (bs i) (cs i)) :
  pi γ₀ ⬝ pi γ₁ = pi (λ i, γ₀ i ⬝ γ₁ i) :=
begin
  apply quotient.induction_on_pi γ₁,
  apply quotient.induction_on_pi γ₀,
  intros,
  simp only [pi_lift],
  rw [← path.homotopic.comp_lift,
      path.trans_pi_eq_pi_trans,
      ← pi_lift],
  refl,
end

/-- Abbreviation for projection onto the ith coordinate -/
@[reducible]
def proj (i : ι) (p : path.homotopic.quotient as bs) : path.homotopic.quotient (as i) (bs i) :=
p.map_fn ⟨_, continuous_apply i⟩

/-- Lemmas showing projection is the inverse of pi -/
@[simp] lemma proj_pi (i : ι) (paths : Π i, path.homotopic.quotient (as i) (bs i)) :
  proj i (pi paths) = paths i :=
begin
  apply quotient.induction_on_pi paths,
  intro, unfold proj,
  rw [pi_lift, ← path.homotopic.map_lift],
  congr, ext, refl,
end

@[simp] lemma pi_proj (p : path.homotopic.quotient as bs) : pi (λ i, proj i p) = p :=
begin
  apply quotient.induction_on p,
  intro, unfold proj,
  simp_rw ← path.homotopic.map_lift,
  rw pi_lift,
  congr, ext, refl,
end

end pi

section prod

variables {α β : Type*} [topological_space α] [topological_space β]
  {a₁ a₂ a₃ : α} {b₁ b₂ b₃ : β}
  {p₁ p₁' : path a₁ a₂} {p₂ p₂' : path b₁ b₂}
  (q₁ : path.homotopic.quotient a₁ a₂) (q₂ : path.homotopic.quotient b₁ b₂)

/-- The product of homotopies h₁ and h₂.
    This is `homotopy_rel.prod` specialized for path homotopies. -/
def prod_homotopy (h₁ : path.homotopy p₁ p₁') (h₂ : path.homotopy p₂ p₂') :
  path.homotopy (p₁.prod p₂) (p₁'.prod p₂') := continuous_map.homotopy_rel.prod h₁ h₂

/-- The product of path classes q₁ and q₂. This is `path.prod` descended to the quotient -/
def prod (q₁ : path.homotopic.quotient a₁ a₂) (q₂ : path.homotopic.quotient b₁ b₂) :
  path.homotopic.quotient (a₁, b₁) (a₂, b₂) :=
quotient.map₂ path.prod (λ p₁ p₁' h₁ p₂ p₂' h₂, nonempty.map2 prod_homotopy h₁ h₂) q₁ q₂

variables (p₁ p₁' p₂ p₂')
lemma prod_lift : prod ⟦p₁⟧ ⟦p₂⟧ = ⟦p₁.prod p₂⟧ := rfl

variables (r₁ : path.homotopic.quotient a₂ a₃) (r₂ : path.homotopic.quotient b₂ b₃)
/-- Products commute with path composition.
    This is `trans_prod_eq_prod_trans` descended to the quotient.-/
lemma comp_prod_eq_prod_comp : (prod q₁ q₂) ⬝ (prod r₁ r₂) = prod (q₁ ⬝ r₁) (q₂ ⬝ r₂) :=
begin
  apply quotient.induction_on₂ q₁ q₂,
  apply quotient.induction_on₂ r₁ r₂,
  intros,
  simp only [prod_lift, ← path.homotopic.comp_lift, path.trans_prod_eq_prod_trans],
end

variables {c₁ c₂ : α × β}

/-- Abbreviation for projection onto the left coordinate of a path class -/
@[reducible]
def proj_left (p : path.homotopic.quotient c₁ c₂) : path.homotopic.quotient c₁.1 c₂.1 :=
p.map_fn ⟨_, continuous_fst⟩

/-- Abbreviation for projection onto the right coordinate of a path class -/
@[reducible]
def proj_right (p : path.homotopic.quotient c₁ c₂) : path.homotopic.quotient c₁.2 c₂.2 :=
p.map_fn ⟨_, continuous_snd⟩

/-- Lemmas showing projection is the inverse of product -/
@[simp] lemma proj_left_prod : proj_left (prod q₁ q₂) = q₁ :=
begin
  apply quotient.induction_on₂ q₁ q₂,
  intros p₁ p₂,
  unfold proj_left,
  rw [prod_lift, ← path.homotopic.map_lift],
  congr, ext, refl,
end

@[simp] lemma proj_right_prod : proj_right (prod q₁ q₂) = q₂ :=
begin
  apply quotient.induction_on₂ q₁ q₂,
  intros p₁ p₂,
  unfold proj_right,
  rw [prod_lift, ← path.homotopic.map_lift],
  congr, ext, refl,
end

@[simp] lemma prod_proj_left_proj_right (p : path.homotopic.quotient (a₁, b₁) (a₂, b₂))
  : prod (proj_left p) (proj_right p) = p :=
begin
  apply quotient.induction_on p,
  intro p',
  unfold proj_left, unfold proj_right,
  simp only [← path.homotopic.map_lift, prod_lift],
  congr, ext; refl,
end

end prod

end path.homotopic
