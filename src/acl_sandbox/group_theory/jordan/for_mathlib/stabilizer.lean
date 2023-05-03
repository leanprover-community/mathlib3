/-
Copyright (c) 2022 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import group_theory.group_action.basic
import group_theory.group_action.fixing_subgroup
import group_theory.group_action.sub_mul_action
import data.finset.pointwise
import .set

/-!

# Various lemmas on stabilizers of sets

* `stabilizer_compl` : the stabilizer of the complement is the stabilizer of the set.

* `le_stabilizer_iff` : proves inclusion of a *subgroup* `H` in `stabilizer G s`
from inclusions `g • s ⊆ s`  for all `g ∈ H`.

# Instances

* `mul_action.of_stabilizer G s`: the action of `stabilizer G s` on `s`.

## TODO

Put in group_theory.group_action.basic ?

-/

namespace mul_action

open_locale pointwise

variables (G : Type*) [group G] {α : Type*} [mul_action G α]

/-- The stabilizer of the complement is the stabilizer of the set. -/
@[simp] lemma stabilizer_compl {s : set α} : stabilizer G sᶜ = stabilizer G s :=
begin
  have : ∀ (s : set α), stabilizer G s ≤ stabilizer G sᶜ,
  { intros s g h,
    rw [mem_stabilizer_iff, smul_compl_set, mem_stabilizer_iff.1 h] },
  refine le_antisymm _ (this _),
  convert this _,
  exact (compl_compl _).symm,
end

/-- The instance that makes the stabilizer of a set acting on that set -/
instance has_smul.of_stabilizer (s : set α) :
  has_smul (stabilizer G s) s := {
smul := λ g x, ⟨g • x,
  begin
    conv_rhs { rw ←  mem_stabilizer_iff.mp (g.prop) },
    exact set.smul_mem_smul_set x.prop,
  end⟩, }

@[simp]
lemma has_smul.smul_stabilizer_def  (s : set α)
  (g : stabilizer G s) (x : s) : coe (g • x)  = (g : G) • (x : α) :=
begin
  rw ← subtype.coe_eta g g.prop,
  rw ← subtype.coe_eta x x.prop,
  refl,
end

/-- The mul_action of stabilizer a set on that set -/
instance of_stabilizer (s : set α) :
  mul_action (stabilizer G s) s := {
one_smul := λ x,
  by rw [← subtype.coe_inj, has_smul.smul_stabilizer_def, subgroup.coe_one, one_smul],
mul_smul := λ g k x,
by simp only [← subtype.coe_inj, has_smul.smul_stabilizer_def, subgroup.coe_mul, mul_action.mul_smul], }

lemma of_stabilizer_def (s : set α) (g : stabilizer G s) (x : s) :
  (g : G) • (x : α) = g • (x : α) := rfl

lemma of_stabilizer_set_def (s : set α) (g : stabilizer G s) (t : set α) :
  (g : G) • t = g • t := rfl

/-- To prove inclusion of a *subgroup* in a stabilizer, it is enough to prove inclusions.-/
lemma le_stabilizer_iff (s : set α) (H : subgroup G) :
  H ≤ stabilizer G s ↔ ∀ g ∈ H, g • s ⊆ s :=
begin
  split,
  { intros hyp g hg,
    apply eq.subset,
    rw ← mem_stabilizer_iff,
    exact hyp hg, },
  intro hyp,
  intros g hg,
  rw mem_stabilizer_iff,
  apply subset_antisymm,
  exact hyp g hg,
  intros x hx, use g⁻¹ • x, split,
  apply hyp g⁻¹ (inv_mem hg),
  simp only [set.smul_mem_smul_set_iff, hx],
  simp only [smul_inv_smul],
end

/-- To prove membership to stabilizer of a *finite set*, it is enough to prove inclusion. -/
lemma mem_stabilizer_of_finite_iff (s : set α) (hs : s.finite) (g : G) :
  g ∈ stabilizer G s ↔ g • s ⊆ s :=
begin
  letI : fintype s := set.finite.fintype hs,
  rw mem_stabilizer_iff,
  haveI : fintype (g • s : set α) := fintype.of_finite ↥(g • s),
  split,
  exact eq.subset,
  { rw [← set.to_finset_inj, ← set.to_finset_subset_to_finset],
    intro h,
    apply finset.eq_of_subset_of_card_le h,
    apply le_of_eq,
    apply symm,
    suffices : (g • s).to_finset = finset.map ⟨_, mul_action.injective g⟩ s.to_finset,
    rw [this, finset.card_map],
    rw ← finset.coe_inj, simp only [set.coe_to_finset, finset.coe_map, function.embedding.coe_fn_mk, set.image_smul], },
end

lemma fixing_subgroup_le_stabilizer (s : set α) :
  fixing_subgroup G s ≤ stabilizer G s :=
begin
  intros k hk,
  rw mem_fixing_subgroup_iff at hk,
  rw mem_stabilizer_iff,
  change (λ x, k • x) '' s = s,
  conv_rhs { rw ← set.image_id s},
  apply set.image_congr ,
  simp only [id.def],
  exact hk,
end

end mul_action


#exit



section stabilizers

variables {G : Type*} [group G] {X : Type*} [mul_action G X] (s : set X)

open_locale pointwise

variables (G s)
def sub_mul_action_of_stabilizer : sub_mul_action (mul_action.stabilizer G s) X :=
{ carrier := s,
  smul_mem' := λ g x hx,
  begin
    have h : g • x ∈ g • s := ⟨x, hx, rfl⟩,
    let hg := g.prop, rw mul_action.mem_stabilizer_iff at hg,
    change g • s = s at hg,
    rw hg at h, exact h,
  end}

instance mul_action_of_stabilizer : mul_action (mul_action.stabilizer G s) s :=
  (sub_mul_action_of_stabilizer G s).mul_action

variables {G s}
def sub_mul_action_of_stabilizer_hom : mul_action.stabilizer G s →* equiv.perm s :=
  mul_action.to_perm_hom (mul_action.stabilizer G s) s

lemma sub_mul_action_of_stabilizer_hom_def
  (g : G) (hg : g ∈ mul_action.stabilizer G s) (x : X) (hx : x ∈ s) :
  ↑(sub_mul_action_of_stabilizer_hom (⟨g, hg⟩ : mul_action.stabilizer G s) (⟨x, hx⟩ : s)) = g • x :=
begin
  simp only [sub_mul_action_of_stabilizer_hom],
  simp only [mul_action.to_perm_hom_apply, mul_action.to_perm_apply],
  refl,
end

end stabilizers
