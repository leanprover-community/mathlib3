import tactic

import group_theory.subgroup.basic
import group_theory.group_action.basic
import order.order_dual

section antitonicity

universes u v
variables {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β}

open order_dual

lemma monotone.dual_iff : monotone f ↔  monotone (to_dual ∘ f ∘ of_dual) :=
begin
  split; exact λ hf a b h, hf h
end

lemma monotone.dual_left_iff : monotone f ↔ antitone (f ∘ of_dual) :=
begin
  split; exact λ hf a b h, hf h
end

lemma monotone.dual_right_iff : monotone f ↔ antitone (to_dual ∘ f) :=
begin
  split; exact λ hf a b h, hf h
end

lemma antitone.dual_iff : antitone f ↔ antitone (to_dual ∘ f ∘ of_dual) :=
begin
  split; exact λ hf a b h, hf h
end

lemma antitone.dual_left_iff : antitone f ↔ monotone (f ∘ of_dual) :=
begin
  split; exact λ hf a b h, hf h
end

lemma antitone.dual_right_iff : antitone f ↔ monotone (to_dual ∘ f) :=
begin
  split; exact λ hf a b h, hf h
end

end antitonicity

section monoid

variables (M : Type*) {α : Type*} [monoid M] [mul_action M α]

/-- The submonoid fixing a set under a `mul_action`. -/
@[to_additive /-" The additive submonoid fixing a set under an `add_action`. "-/]
def fixing_submonoid (s : set α) : submonoid M :=
{ carrier := { ϕ : M | ∀ x : s, ϕ • (x : α) = x },
  one_mem' := λ _, one_smul _ _,
  mul_mem' := λ x y hx hy z, by rw [mul_smul, hy z, hx z], }

lemma mem_fixing_submonoid_iff {s : set α} {m : M} :
  m ∈ fixing_submonoid M s ↔ ∀ (y : α) (hy : y ∈ s), m • y = y :=
⟨λ hg y hy, hg ⟨y, hy⟩, λ h ⟨y, hy⟩, h y hy⟩

variable (α)
lemma fixing_submonoid_fixed_points_connection : galois_connection
  (order_dual.to_dual ∘ (λ s : set α, fixing_submonoid M s))
  ((λ P : submonoid M, (mul_action.fixed_points P α)) ∘ order_dual.of_dual) :=
begin
  unfold galois_connection,
  intros s P,
  split,
  { intro hMs,
    change P.of_dual ≤ fixing_submonoid M s at hMs,
    intros a has,
    simp only [mul_action.mem_fixed_points],
    rintro ⟨p, hp⟩,
    have : p ∈ fixing_submonoid M s := hMs hp,
    rw mem_fixing_submonoid_iff at this,
    exact this a has },
  { intro hsP,
    intros p hp,
    change p ∈ fixing_submonoid M s,
    rw mem_fixing_submonoid_iff,
    intros a ha,
    have : a ∈ mul_action.fixed_points _ α := hsP ha,
    rw mul_action.mem_fixed_points at this,
    specialize this ⟨p, hp⟩,
    conv_rhs { rw ← this },
    refl }
end

lemma fixing_submonoid_is_antitone : antitone (λ (s : set α), fixing_submonoid M s) :=
galois_connection.monotone_l (fixing_submonoid_fixed_points_connection M α)

lemma fixed_points_is_antitone :
  antitone (λ (P : submonoid M), mul_action.fixed_points P α) :=
begin
  change monotone (order_dual.to_dual ∘ λ (P : submonoid M), mul_action.fixed_points P α),
  rw [← antitone.dual_right_iff, antitone.dual_left_iff],
  exact galois_connection.monotone_u (fixing_submonoid_fixed_points_connection M α),
end

/-
lemma fixing_submonoid_is_antitone' : antitone (λ (s : set α), fixing_submonoid M s) :=
begin
  intros s t hst,
  rw set.le_eq_subset at hst,
  intro m,
  simp only [mem_fixing_submonoid_iff],
  refine forall_imp _,
  intro a,
  refine imp_imp_imp _ (imp_self.mpr trivial),
  { intro hs, exact hst hs }
end
-/

/-
lemma mem_fixing_submonoid_of_union {s t : set α} :
  fixing_submonoid M (s ∪ t) = (fixing_submonoid M s) ⊓ (fixing_submonoid M t) :=
begin
  apply le_antisymm,
  { refine le_inf _ _;
    apply fixing_submonoid_is_antitone,
    refine le_sup_left,
    refine le_sup_right },
  { intros m hm,
    simp only [submonoid.mem_inf] at hm,
    simp only [mem_fixing_submonoid_iff] at hm ⊢,
    intros a ha,
    cases ha,
    exact hm.left a ha,
    exact hm.right a ha }
end
-/

lemma fixing_submonoid_of_union {s t : set α} :
  fixing_submonoid M (s ∪ t) = (fixing_submonoid M s) ⊓ (fixing_submonoid M t) :=
galois_connection.l_sup (fixing_submonoid_fixed_points_connection M α)

lemma fixing_submonoid_of_Union {ι : Type*} {s : ι → set α} :
  fixing_submonoid M (⋃ (i : ι), s i) = infi (λ i, (fixing_submonoid M (s i))) :=
galois_connection.l_supr (fixing_submonoid_fixed_points_connection M α)

lemma fixed_points_of_sup {P Q : submonoid M} :
  mul_action.fixed_points (P ⊔ Q : submonoid M) α =
    (mul_action.fixed_points P α) ⊓ (mul_action.fixed_points Q α) :=
  galois_connection.u_inf (fixing_submonoid_fixed_points_connection M α)

lemma fixed_points_of_supr {ι : Type*} {P : ι → submonoid M} :
  mul_action.fixed_points (supr P : submonoid M) α =
    infi (λ i, (mul_action.fixed_points (P i) α)) :=
  galois_connection.u_infi (fixing_submonoid_fixed_points_connection M α)

end monoid

section group

variables (M : Type*) [group M] {α : Type*} [mul_action M α]

/-- The subgroup fixing a set under a `mul_action`. -/
@[to_additive /-" The additive subgroup fixing a set under an `add_action`. "-/]
def fixing_subgroup (s : set α) : subgroup M :=
{ inv_mem' := λ _ hx z, by rw [inv_smul_eq_iff, hx z],
  ..fixing_submonoid M s, }

lemma mem_fixing_subgroup_iff {s : set α} {m : M} :
  m ∈ fixing_subgroup M s ↔ ∀ (y : α) (hy : y ∈ s), m • y = y :=
⟨λ hg y hy, hg ⟨y, hy⟩, λ h ⟨y, hy⟩, h y hy⟩

variable (α)
lemma fixing_subgroup_fixed_points_connection : galois_connection
  (order_dual.to_dual ∘ (λ s : set α, fixing_subgroup M s))
  ((λ P : subgroup M, (mul_action.fixed_points P α)) ∘ order_dual.of_dual) :=
begin
  unfold galois_connection,
  intros s P,
  split,
  { intro hMs,
    change P.of_dual ≤ fixing_subgroup M s at hMs,
    intros a has,
    simp only [mul_action.mem_fixed_points],
    rintro ⟨p, hp⟩,
    have : p ∈ fixing_subgroup M s := hMs hp,
    rw mem_fixing_subgroup_iff at this,
    exact this a has },
  { intro hsP,
    intros p hp,
    change p ∈ fixing_subgroup M s,
    rw mem_fixing_subgroup_iff,
    intros a ha,
    have : a ∈ mul_action.fixed_points _ α := hsP ha,
    rw mul_action.mem_fixed_points at this,
    specialize this ⟨p, hp⟩,
    conv_rhs { rw ← this },
    refl }
end

lemma fixing_subgroup_is_antitone : antitone (λ (s : set α), fixing_subgroup M s) :=
galois_connection.monotone_l (fixing_subgroup_fixed_points_connection M α)

lemma fixed_points_of_group_is_antitone :
  antitone (λ (P : subgroup M), mul_action.fixed_points P α) :=
begin
  change monotone (order_dual.to_dual ∘ λ (P : subgroup M), mul_action.fixed_points P α),
  rw [← antitone.dual_right_iff, antitone.dual_left_iff],
  exact galois_connection.monotone_u (fixing_subgroup_fixed_points_connection M α),
end


lemma fixing_subgroup_of_union {s t : set α} :
  fixing_subgroup M (s ∪ t) = (fixing_subgroup M s) ⊓ (fixing_subgroup M t) :=
galois_connection.l_sup (fixing_subgroup_fixed_points_connection M α)

lemma fixing_subgroup_of_Union {ι : Type*} {s : ι → set α} :
  fixing_subgroup M (⋃ (i : ι), s i) = infi (λ i, (fixing_subgroup M (s i))) :=
galois_connection.l_supr (fixing_subgroup_fixed_points_connection M α)

lemma fixed_points_of_group_of_sup {P Q : subgroup M} :
  mul_action.fixed_points (P ⊔ Q : subgroup M) α =
    (mul_action.fixed_points P α) ⊓ (mul_action.fixed_points Q α) :=
  galois_connection.u_inf (fixing_subgroup_fixed_points_connection M α)

lemma fixed_points_of_group_of_supr {ι : Type*} {P : ι → subgroup M} :
  mul_action.fixed_points (supr P : subgroup M) α =
    infi (λ i, (mul_action.fixed_points (P i) α)) :=
  galois_connection.u_infi (fixing_subgroup_fixed_points_connection M α)

end group
