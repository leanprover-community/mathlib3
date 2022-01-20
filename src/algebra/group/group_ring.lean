/-
Copyright (c) 2021 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import algebra.monoid_algebra.basic
import tactic.basic

/-!
# Group rings

This file defines the group ring `ℤ[G]` of a group `G`.

This is the free abelian group on the elements of `G`, with multiplication induced by
multiplication in `G.` A `G`-module `M` is also a `ℤ[G]`-module.

We develop an API allowing us to show `ℤ[Gⁿ]` is a free `ℤ[G]`-module for `n ≥ 1`. This
will be used to construct a projective resolution of the trivial `ℤ[G]`-module `ℤ`.

## Implementation notes

Although `group_ring G` is just `monoid_algebra ℤ G`, we make the definition `group_ring`
so Lean finds the right instances for this setting, and so we can separate material relevant
to group cohomology into the namespace `group_ring`.

## Tags

group ring, group cohomology, monoid algebra
-/

noncomputable theory

/-- The group ring `ℤ[G]` of a group `G` (although this is defined for any type `G`). -/
def group_ring (G : Type*) := monoid_algebra ℤ G

namespace group_ring

instance {G : Type*} : inhabited (group_ring G) :=
by unfold group_ring; apply_instance

instance {G : Type*} : add_comm_group (group_ring G) :=
finsupp.add_comm_group

instance {G : Type*} [monoid G] : ring (group_ring G) :=
{ ..monoid_algebra.semiring, ..group_ring.add_comm_group }

/-- The natural inclusion `G → ℤ[G]`. -/
def of (G : Type*) [monoid G] : G →* group_ring G :=
monoid_algebra.of ℤ G

section

variables {G : Type*} [monoid G]

@[simp] lemma of_apply (g : G) :
  of G g = finsupp.single g (1 : ℤ) := rfl

lemma zsmul_single_one (g : G) (r : ℤ) :
  r • (of G g) = finsupp.single g r :=
by simp only [mul_one, finsupp.smul_single', zsmul_eq_smul, of_apply]

@[elab_as_eliminator]
lemma induction_on {p : group_ring G → Prop} (f : group_ring G)
  (hM : ∀ g, p (of G g)) (hadd : ∀ f g : group_ring G, p f → p g → p (f + g))
  (hsmul : ∀ (r : ℤ) f, p f → p (r • f)) : p f :=
monoid_algebra.induction_on _ hM hadd hsmul

lemma ext {P : Type*} [add_comm_group P] (f : group_ring G →+ P)
  (g : group_ring G →+ P) (H : ∀ x, f (of G x) = g (of G x)) {x} :
  f x = g x :=
begin
  congr,
  refine finsupp.add_hom_ext (λ y n, _),
  simp only [←zsmul_single_one, add_monoid_hom.map_zsmul, H],
end

/-- Makes a `ℤ[G]`-linear map from a `G`-linear hom of `ℤ[G]`-modules. -/
def mk_linear {P : Type*} {P' : Type*} [add_comm_group P] [add_comm_group P']
  [module (group_ring G) P] [module (group_ring G) P'] (f : P →+ P')
  (H : ∀ g x, f (of G g • x) = of G g • f x) : P →ₗ[group_ring G] P' :=
{ map_smul' := λ z,
  begin
  refine z.induction_on (by exact H) _ _,
  { intros a b ha hb x,
    dsimp at ⊢ ha hb,
    simp only [add_smul, f.map_add, ha, hb] },
  { intros r a ha x,
    dsimp at ⊢ ha,
    simp only [smul_assoc, f.map_zsmul, ha] }
  end, ..f }

@[simp] lemma mk_linear_apply {P : Type*} {P' : Type*} [add_comm_group P] [add_comm_group P']
  [module (group_ring G) P] [module (group_ring G) P'] (f : P →+ P')
  {H : ∀ g x, f (of G g • x) = of G g • f x} {x : P} :
  mk_linear f H x = f x := rfl

/-- Makes a `ℤ[G]`-linear isomorphism from a `G`-linear isomorphism of `ℤ[G]`-modules. -/
def mk_equiv {P : Type*} {P' : Type*} [add_comm_group P] [add_comm_group P']
  [module (group_ring G) P] [module (group_ring G) P'] (f : P ≃+ P')
  (H : ∀ g x, f (of G g • x) = of G g • f x) : P ≃ₗ[group_ring G] P' :=
{ ..f, ..mk_linear f.to_add_monoid_hom H }

@[simp] lemma mk_equiv_apply {P : Type*} {P' : Type*} [add_comm_group P] [add_comm_group P']
  [module (group_ring G) P] [module (group_ring G) P'] (f : P ≃+ P')
  {H : ∀ g x, f (of G g • x) = of G g • f x} {x : P} :
  mk_equiv f H x = f x := rfl

-- Don't know which file to put this in that won't involve adding an import...
instance {G : Type*} [monoid G] {M : Type*} [add_comm_group M]
  [H : distrib_mul_action G M] : smul_comm_class ℤ G M :=
⟨λ n g m, int.induction_on n
  ( by simp)
  ( λ i h, by { simp only [add_smul, smul_add, add_left_inj, one_zsmul, h]})
  ( λ i h, by { simp only [zsmul_sub_one, smul_neg, smul_add, h]})⟩

/-- `ℤ[G]`-module instance on an `G`-module `M`. -/
def to_module {M : Type*} [add_comm_group M]
  [H : distrib_mul_action G M] : module (group_ring G) M :=
monoid_algebra.total_to_module

end

variables {G : Type*} [group G] {n : ℕ}

instance {H : Type*} [mul_action G H] : distrib_mul_action G (group_ring H) :=
finsupp.comap_distrib_mul_action

/-- If `ℤ[H]` is a `ℤ[G]`-module, then an additive hom `f: ℤ[H] → P` of `ℤ[G]`-modules which
satisfies `f(g • h) = g • f(h)` for all `g ∈ G, h ∈ H` is `ℤ[G]`-linear. -/
lemma map_smul_of_map_smul_of {H : Type*} [monoid H] [module (group_ring G) (group_ring H)]
  {P : Type*} [add_comm_group P] [module (group_ring G) P] (f : group_ring H →+ P)
  (h : ∀ (g : G) (x : H), f (of G g • of _ x) = of G g • f (of _ x)) (g : group_ring G)
  (x : group_ring H) : f (g • x) = g • f x :=
begin
  convert (mk_linear f _).map_smul g x,
  intros a b,
  refine b.induction_on (by exact h a) _ _,
  { intros s t hs ht,
    simp only [smul_add, f.map_add, hs, ht] },
  { intros r s hs,
    simp only [smul_algebra_smul_comm, f.map_zsmul, hs] }
end

instance : module (group_ring G) (group_ring (fin n → G)) :=
group_ring.to_module

instance (M : submodule (group_ring G) (group_ring (fin n → G))) :
  has_coe M (group_ring (fin n → G)) :=
{ coe := λ m, m.1 }

lemma smul_def (g : group_ring G) (h : group_ring (fin n → G)) :
  g • h = finsupp.total G (group_ring (fin n → G)) ℤ (λ x, x • h) g :=
rfl

lemma of_smul_of (g : G) (x : fin n → G) :
  of G g • of (fin n → G) x = of (fin n → G) (g • x) :=
show finsupp.total _ _ _ _ _ = _, by simp

end group_ring
