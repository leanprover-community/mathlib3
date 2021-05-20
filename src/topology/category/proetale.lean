/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import topology.category.Profinite
import category_theory.sites.pretopology
import category_theory.sites.sheaf_of_types
import category_theory.sites.sheaf
import category_theory.limits.opposites
import algebra.category.Group
import algebra.category.CommRing

open category_theory category_theory.limits

universes v u

variables {C : Type u} [category.{v} C]

/-- A terminal Profinite type, which has the important property that morphisms to `X` are the same
thing as elements of `X`. -/
def point : Profinite.{u} := ⟨⟨punit⟩⟩

/-- There is a (natural) bijection between morphisms `* ⟶ X` and elements of `X`.  -/
def from_point {X : Profinite.{u}} :
  (point ⟶ X) ≃ X :=
{ to_fun := λ f, f punit.star,
  inv_fun := λ x, ⟨λ _, x⟩,
  left_inv := λ x, by { ext ⟨⟩, refl },
  right_inv := λ x, rfl}

lemma from_point_apply {X Y : Profinite} (f : point ⟶ X) (g : X ⟶ Y) :
  g (from_point f) = from_point (f ≫ g) :=
rfl

noncomputable def mk_pullback {X Y Z : Profinite.{u}} {f : X ⟶ Z} {g : Y ⟶ Z} {x : X} {y : Y}
  (h : f x = g y) :
  (pullback f g : Profinite) :=
from_point (pullback.lift (from_point.symm x) (from_point.symm y) (by { ext ⟨⟩, exact h }))

lemma mk_pullback_fst {X Y Z : Profinite} {f : X ⟶ Z} {g : Y ⟶ Z} {x : X} {y : Y}
  {h : f x = g y} : (pullback.fst : pullback f g ⟶ _) (mk_pullback h) = x :=
begin
  rw [mk_pullback, from_point_apply],
  simp
end

lemma mk_pullback_snd {X Y Z : Profinite.{u}} {f : X ⟶ Z} {g : Y ⟶ Z} {x : X} {y : Y}
  {h : f x = g y} : (pullback.snd : pullback f g ⟶ _) (mk_pullback h) = y :=
begin
  rw [mk_pullback, from_point_apply],
  simp
end

/-- The proetale pretopology on Profinites. -/
def proetale_pretopology : pretopology.{u} Profinite.{u} :=
{ coverings := λ X S, ∃ (ι : Type u) [fintype ι] (Y : ι → Profinite) (f : Π (i : ι), Y i ⟶ X),
      (∀ (x : X), ∃ i (y : Y i), f i y = x) ∧ S = presieve.of_arrows Y f,
  has_isos := λ X Y f i,
  begin
    refine ⟨punit, infer_instance, λ _, Y, λ _, f, _, _⟩,
    { introI x,
      refine ⟨punit.star, inv f x, _⟩,
      change (inv f ≫ f) x = x,
      rw is_iso.inv_hom_id,
      simp },
    { rw presieve.of_arrows_punit },
  end,
  pullbacks := λ X Y f S,
  begin
    rintro ⟨ι, hι, Z, g, hg, rfl⟩,
    refine ⟨ι, hι, λ i, pullback (g i) f, λ i, pullback.snd, _, _⟩,
    { intro y,
      rcases hg (f y) with ⟨i, z, hz⟩,
      exact ⟨i, mk_pullback hz, mk_pullback_snd⟩ },
    { rw presieve.of_arrows_pullback }
  end,
  transitive := λ X S Ti,
  begin
    rintro ⟨ι, hι, Z, g, hY, rfl⟩ hTi,
    choose j hj W k hk₁ hk₂ using hTi,
    resetI,
    refine ⟨Σ (i : ι), j (g i) (presieve.of_arrows.mk _), infer_instance, λ i, W _ _ i.2, _, _, _⟩,
    { intro ij,
      exact k _ _ ij.2 ≫ g ij.1 },
    { intro x,
      obtain ⟨i, y, rfl⟩ := hY x,
      obtain ⟨i', z, rfl⟩ := hk₁ (g i) (presieve.of_arrows.mk _) y,
      refine ⟨⟨i, i'⟩, z, rfl⟩ },
    { have : Ti = λ Y f H, presieve.of_arrows (W f H) (k f H),
      { ext Y f H : 3,
        apply hk₂ },
      rw this,
      apply presieve.of_arrows_bind },
  end }

def proetale_topology : grothendieck_topology.{u} Profinite.{u} :=
proetale_pretopology.to_grothendieck _

@[derive category]
def CondensedSet : Type (u+1) := SheafOfTypes.{u} proetale_topology.{u}

@[derive category]
def Condensed (A : Type (u+1)) [large_category A] : Type (u+1) := Sheaf.{u} proetale_topology A

example : category.{u+1} (Condensed Ab.{u}) := infer_instance
example : category.{u+1} (Condensed Ring.{u}) := infer_instance

open opposite

noncomputable theory

variables (P : Profinite.{u}ᵒᵖ ⥤ Type u)
lemma maps_comm {S S' : Profinite.{u}} (f : S' ⟶ S) :
  P.map f.op ≫ P.map (pullback.fst : pullback f f ⟶ S').op = P.map f.op ≫ P.map pullback.snd.op :=
by rw [←P.map_comp, ←op_comp, pullback.condition, op_comp, P.map_comp]

def natural_fork {S S' : Profinite.{u}} (f : S' ⟶ S) :
  fork (P.map pullback.fst.op) (P.map pullback.snd.op) :=
fork.of_ι (P.map (quiver.hom.op f)) (maps_comm P f)

structure condensed_condition : Prop :=
(empty : nonempty (preserves_terminal P))
(bin_prod : nonempty P.preserves_binary_products)
(pullbacks : ∀ {S S' : Profinite.{u}} (f : S' ⟶ S) [epi f], nonempty (is_limit (natural_fork P f)))

def preserves_terminal_of_is_proetale_sheaf (hP : presieve.is_sheaf proetale_topology P) :
  preserves_terminal P :=
begin
  rw [proetale_topology, presieve.is_sheaf_pretopology] at hP,
  apply preserves_terminal_of_is_terminal_obj,
  apply terminal_op_of_initial Profinite.initial_pempty,
  let R : presieve (Profinite.of pempty) := λ _, ∅,
  have hR : R ∈ proetale_pretopology (Profinite.of pempty),
  { refine ⟨pempty, infer_instance, pempty.elim, λ i, i.elim, λ i, i.elim, _⟩,
    ext X f,
    simp only [set.mem_empty_eq, false_iff],
    rintro ⟨⟨⟩⟩ },
  let t : presieve.family_of_elements P R := λ X f, false.elim,
  have ht : t.compatible,
  { rintro Y₁ Y₂ Z g₁ g₂ f₁ f₂ ⟨⟩ },
  have : nonempty (unique (P.obj (op (Profinite.of pempty)))),
  { obtain ⟨x, hx, hx'⟩ := hP _ hR _ ht,
    refine ⟨⟨⟨x⟩, λ y, hx' y _⟩⟩,
    rintro _ _ ⟨⟩ },
  letI := classical.choice this,
  apply (types.is_terminal_equiv_equiv_punit _).symm _,
  apply equiv_of_unique_of_unique,
end

def preserves_binary_products_of_is_proetale_sheaf (hP : presieve.is_sheaf proetale_topology P) :
  P.preserves_binary_products :=
begin
  rw [proetale_topology, presieve.is_sheaf_pretopology] at hP,

  -- apply preserves_terminal_of_is_terminal_obj,
  -- apply terminal_op_of_initial Profinite.initial_pempty,
  -- let R : presieve (Profinite.of pempty) := λ _, ∅,
  -- have hR : R ∈ proetale_pretopology (Profinite.of pempty),
  -- { refine ⟨pempty, infer_instance, pempty.elim, λ i, i.elim, λ i, i.elim, _⟩,
  --   ext X f,
  --   simp only [set.mem_empty_eq, false_iff],
  --   rintro ⟨⟨⟩⟩ },
  -- let t : presieve.family_of_elements P R := λ X f, false.elim,
  -- have ht : t.compatible,
  -- { rintro Y₁ Y₂ Z g₁ g₂ f₁ f₂ ⟨⟩ },
  -- have : nonempty (unique (P.obj (op (Profinite.of pempty)))),
  -- { obtain ⟨x, hx, hx'⟩ := hP _ hR _ ht,
  --   refine ⟨⟨⟨x⟩, λ y, hx' y _⟩⟩,
  --   rintro _ _ ⟨⟩ },
  -- letI := classical.choice this,
  -- apply (types.is_terminal_equiv_equiv_punit _).symm _,
  -- apply equiv_of_unique_of_unique,
end

lemma condensed_condition_of_is_sheaf (hP : presieve.is_sheaf proetale_topology P) :
  condensed_condition P :=
begin
  refine ⟨⟨_⟩, ⟨_⟩, _⟩,
  { apply preserves_terminal_of_is_proetale_sheaf _ hP },

end
