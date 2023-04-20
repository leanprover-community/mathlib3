/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.normed.group.basic
import group_theory.free_group

/-!
# Marked groups

This file defines group markings and induces a norm on marked groups.

## Main declarations

* `group_marking G S`: Marking of the group `G` by a type `S`, namely a surjective monoid
  homomorphism `free_group S →* G`.
* `marked_group`: If `m : group_marking G S`, then `marked_group m` is a type synonym for `G`
  endowed with the metric coming from `m`.
* `marked_group.normed_group`: A marked group is normed by its marking.
-/

set_option old_structure_cmd true

open function list nat

variables {G S : Type*} [group G]

/-- A marking of an additive group is a generating family of elements. -/
structure add_group_marking (G S : Type*) [add_group G] extends free_add_group S →+ G :=
(to_fun_surjective : surjective to_fun)

/-- A marking of a group is a generating family of elements. -/
@[to_additive]
structure group_marking (G S : Type*) [group G] extends free_group S →* G :=
(to_fun_surjective : surjective to_fun)

/-- Reinterpret a marking of `G` by `S` as an additive monoid homomorphism `free_add_group S →+ G`.
-/
add_decl_doc add_group_marking.to_add_monoid_hom

/-- Reinterpret a marking of `G` by `S` as a monoid homomorphism `free_group S →+ G`. -/
add_decl_doc group_marking.to_monoid_hom

namespace group_marking

@[to_additive]
instance : monoid_hom_class (group_marking G S) (free_group S) G :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_mul := λ f, f.map_mul',
  map_one := λ f, f.map_one' }

@[to_additive]
lemma coe_surjective (m : group_marking G S) : surjective m := m.to_fun_surjective

end group_marking

/-- The trivial group marking. -/
@[to_additive "The trivial additive group marking."]
def group_marking.refl : group_marking G G :=
{ to_fun_surjective := λ x, ⟨free_group.of x, free_group.lift.of⟩,
  ..free_group.lift id }

@[to_additive]
instance : inhabited (group_marking G G) := ⟨group_marking.refl⟩

variables {G S} {m : group_marking G S}

/-- A type synonym of `G`, tagged with a group marking. -/
@[derive group, nolint unused_arguments,
to_additive "A type synonym of `G`, tagged with an additive group marking."]
def marked_group (m : group_marking G S) : Type* := G

attribute [to_additive] marked_group.group

/-- "Identity" isomorphism between `G` and a group marking of it. -/
@[to_additive "\"Identity\" isomorphism between `G` and an additive group marking of it."]
def to_marked_group : G ≃* marked_group m := mul_equiv.refl _

/-- "Identity" isomorphism between a group marking of `G` and itself. -/
@[to_additive "\"Identity\" isomorphism between an additive group marking of `G` and itself."]
def of_marked_group : marked_group m ≃* G := mul_equiv.refl _

@[simp, to_additive] lemma to_marked_group_symm_eq :
  (to_marked_group : G ≃* marked_group m).symm = of_marked_group := rfl
@[simp, to_additive] lemma of_marked_group_symm_eq :
  (of_marked_group : marked_group m ≃* G).symm = to_marked_group := rfl
@[simp, to_additive] lemma to_marked_group_of_marked_group (a) :
  to_marked_group (of_marked_group (a : marked_group m)) = a := rfl
@[simp, to_additive] lemma of_marked_group_to_marked_group (a) :
  of_marked_group (to_marked_group a : marked_group m) = a := rfl
@[simp, to_additive] lemma to_marked_group_inj {a b} :
  (to_marked_group a : marked_group m) = to_marked_group b ↔ a = b := iff.rfl
@[simp, to_additive] lemma of_marked_group_inj {a b : marked_group m} :
  of_marked_group a = of_marked_group b ↔ a = b := iff.rfl

variables (α : Type*)

@[to_additive] instance [inhabited G] : inhabited (marked_group m) := ‹inhabited G›
@[to_additive] instance marked_group.has_smul [has_smul G α] : has_smul (marked_group m) α :=
‹has_smul G α›
@[to_additive] instance marked_group.mul_action [mul_action G α] : mul_action (marked_group m) α :=
‹mul_action G α›

@[simp, to_additive] lemma to_marked_group_smul (g : G) (x : α) [has_smul G α] :
  (to_marked_group g : marked_group m) • x = g • x := rfl
@[simp, to_additive] lemma of_marked_group_smul (g : marked_group m) (x : α) [has_smul G α] :
  of_marked_group g • x = g • x := rfl

@[to_additive]
private lemma mul_aux [decidable_eq S] (x : marked_group m) :
  ∃ n (l : free_group S), m l = x ∧ l.to_word.length ≤ n :=
by { classical, obtain ⟨l, rfl⟩ := m.coe_surjective x, exact ⟨_, _, rfl, le_rfl⟩ }

@[to_additive]
private lemma mul_aux' [decidable_eq S] (x : marked_group m) :
  ∃ n (l : free_group S), m l = x ∧ l.to_word.length = n :=
by { classical, obtain ⟨l, rfl⟩ := m.coe_surjective x, exact ⟨_, _, rfl, rfl⟩ }

@[to_additive]
lemma find_mul_aux [decidable_eq S] (x : marked_group m) :
  by classical; exact nat.find (mul_aux x) = nat.find (mul_aux' x) :=
le_antisymm (nat.find_mono $ λ n, Exists.imp $ λ l, and.imp_right le_of_eq) $
  (nat.le_find_iff _ _).2 $ λ k hk ⟨l, hl, hlk⟩, (nat.lt_find_iff _ _).1 hk _ hlk ⟨l, hl, rfl⟩

@[to_additive]
noncomputable instance : normed_group (marked_group m) :=
group_norm.to_normed_group
{ to_fun := λ x, by classical; exact nat.find (mul_aux x),
  map_one' := cast_eq_zero.2 $ (find_eq_zero $ mul_aux _).2 ⟨1, map_one _, le_rfl⟩,
  mul_le' := λ x y, begin
    norm_cast,
    obtain ⟨a, rfl, ha⟩ := nat.find_spec (mul_aux x),
    obtain ⟨b, rfl, hb⟩ := nat.find_spec (mul_aux y),
    refine find_le ⟨a * b, map_mul _ _ _, (a.to_word_mul_sublist _).length_le.trans _⟩,
    rw length_append,
    exact add_le_add ha hb,
  end,
  inv' := begin
    suffices : ∀ {x : marked_group m}, nat.find (mul_aux x⁻¹) ≤ nat.find (mul_aux x),
    { refine λ _, congr_arg coe (this.antisymm _),
      convert this,
      simp_rw inv_inv },
    refine λ x, find_mono (λ nI, _),
    rintro ⟨l, hl, h⟩,
    exact ⟨l⁻¹, by simp [hl], h.trans_eq' $ by simp⟩,
  end,
  eq_one_of_map_eq_zero' := λ x hx, begin
    obtain ⟨l, rfl, hl⟩ := (find_eq_zero $ mul_aux _).1 (cast_eq_zero.1 hx),
    rw [le_zero_iff, length_eq_zero, ←free_group.to_word_one] at hl,
    rw [free_group.to_word_injective hl, map_one],
  end }

@[to_additive] instance :
  discrete_topology (marked_group (group_marking.refl : group_marking G G)) :=
sorry

namespace marked_group

@[to_additive] lemma norm_def (x : marked_group m) : ‖x‖ = nat.find (mul_aux' x) :=
congr_arg coe (find_mul_aux _)

@[simp, to_additive] lemma norm_eq_one (x : marked_group m) :
  ‖x‖ = 1 ↔ ∃ s, to_marked_group (m $ free_group.of s) = x :=
begin
  rw [norm_def, nat.cast_eq_one, nat.find_eq_iff],
  sorry
end

@[simp] lemma norm_to_marked_group (s : S) :
  ‖((to_marked_group (m (free_group.of s))) : marked_group m)‖ = 1 :=


lemma gen_set_mul_right (x : marked_group m) (s : S) :
  ‖(to_marked_group (of_marked_group x * m (free_group.of s)) : marked_group m)‖ ≤ ‖x‖ + 1 :=
sorry

lemma gen_set_mul_right' (x : marked_group m) {n : ℝ} (hx : ‖x‖ ≤ n) (s : S) :
  ‖(to_marked_group (of_marked_group x * m (free_group.of s)) : marked_group m)‖ ≤ n + 1 :=
sorry

lemma gen_set_mul_left (x : marked_group m) (s : S) :
  ‖(to_marked_group (m (free_group.of s) * of_marked_group x) : marked_group m)‖ ≤ ‖x‖ + 1 :=
sorry

lemma gen_set_mul_left' (x : marked_group m) {n : ℝ} (hx : ‖x‖ ≤ n) (s : S) :
  ‖(to_marked_group (m (free_group.of s) * of_marked_group x) : marked_group m) ‖ ≤ n + 1 :=
sorry

lemma dist_one_iff (x y : marked_group m) :
  dist x y = 1 ↔ (∃ s : S, x * m (free_group.of s) = y) ∨ ∃ s : S, y * m (free_group.of s) = x :=
sorry

lemma gen_set_div (x : marked_group m) (hx : x ≠ 1) : ∃ y : marked_group m, dist x y = 1 ∧ ‖y‖ = ‖x‖ - 1 :=
sorry

lemma gen_div_left (x : marked_group m) (hx : x ≠ 1) :
  ∃ y : marked_group m,
    ((∃ s : S, m (free_group.of s) * y = x) ∨ (∃ s : S, m (free_group.of s)⁻¹ * y = x)) ∧
      ‖y‖ = ‖x‖ - 1 :=
sorry

-- same lemmas but for subsets

lemma gen_norm_le_one_sub {H : set G}  {m' : marking G H} {s : marked_group m'} (sh : s ∈ H) : ‖s‖ ≤ 1 :=
sorry

lemma gen_set_mul_right_sub {H : set G} {s : G} {m' : marking G H} (sh : s ∈ H) (g : marked_group m') :
  ‖g * s‖ ≤ ‖g‖ + 1 :=
sorry

lemma gen_set_mul_right'_sub {H : set G} {s : G} {m' : marking G H} (sh : s ∈ H) (g : marked_group m')
  {n : ℝ} (hg : ‖g‖ ≤ n) : ‖g * s‖ ≤ n + 1 :=
sorry

lemma gen_set_mul_left_sub {H : set G} {m' : marking G H} (g s: marked_group m') (sh : s ∈ H) :
  ‖s * g‖ ≤ ‖g‖ + 1 :=
sorry

lemma gen_set_mul_left'_sub {H : set G} {m' : marking G H} (g s : marked_group m')  (sh : s ∈ H) {n : ℝ}
  (hg : ‖g‖ ≤ n) : ‖s * g‖ ≤ n + 1 :=
sorry

lemma dist_one_iff_sub {H : set G} {m' : marking G H} (x y : marked_group m') :
  dist x y = 1 ↔ (∃ s ∈ H, x * s = y) ∨ ∃ s ∈ H, y * s = x :=
sorry

lemma gen_div_left_sub {H : set G} {m' : marking G H} (x : marked_group m') (hx : x ≠ 1) :
  ∃ y : marked_group m', ((∃ s ∈ H, s * y = x) ∨ (∃ s ∈ H, s⁻¹ * y = x)) ∧ ‖y‖ = ‖x‖ - 1 :=
sorry
