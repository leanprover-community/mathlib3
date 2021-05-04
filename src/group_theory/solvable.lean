/-
Copyright (c) 2021 Jordan Brown, Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jordan Brown, Thomas Browning, Patrick Lutz
-/

import group_theory.abelianization
import data.bracket
import set_theory.cardinal

/-!
# Solvable Groups

In this file we introduce the notion of a solvable group. We define a solvable group as one whose
derived series is eventually trivial. This requires defining the commutator of two subgroups and
the derived series of a group.

## Main definitions

* `general_commutator H₁ H₂` : the commutator of the subgroups `H₁` and `H₂`
* `derived_series G n` : the `n`th term in the derived series of `G`, defined by iterating
  `general_commutator` starting with the top subgroup
* `is_solvable G` : the group `G` is solvable
-/

open subgroup

variables {G G' : Type*} [group G] [group G'] {f : G →* G'}

section general_commutator

/-- The commutator of two subgroups `H₁` and `H₂`. -/
instance general_commutator : has_bracket (subgroup G) (subgroup G) :=
⟨λ H₁ H₂, closure {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x}⟩

lemma general_commutator_def (H₁ H₂ : subgroup G) :
  ⁅H₁, H₂⁆ = closure {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x} := rfl

instance general_commutator_normal (H₁ H₂ : subgroup G) [h₁ : H₁.normal]
  [h₂ : H₂.normal] : normal ⁅H₁, H₂⁆ :=
begin
  let base : set G := {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x},
  suffices h_base : base = group.conjugates_of_set base,
  { dsimp only [general_commutator_def, ←base],
    rw h_base,
    exact subgroup.normal_closure_normal },
  apply set.subset.antisymm group.subset_conjugates_of_set,
  intros a h,
  simp_rw [group.mem_conjugates_of_set_iff, is_conj_iff] at h,
  rcases h with ⟨b, ⟨c, hc, e, he, rfl⟩, d, rfl⟩,
  exact ⟨d * c * d⁻¹, h₁.conj_mem c hc d, d * e * d⁻¹, h₂.conj_mem e he d, by group⟩,
end

lemma general_commutator_mono {H₁ H₂ K₁ K₂ : subgroup G} (h₁ : H₁ ≤ K₁) (h₂ : H₂ ≤ K₂) :
  ⁅H₁, H₂⁆ ≤ ⁅K₁, K₂⁆ :=
begin
  apply closure_mono,
  rintros x ⟨p, hp, q, hq, rfl⟩,
  exact ⟨p, h₁ hp, q, h₂ hq, rfl⟩,
end

lemma general_commutator_def' (H₁ H₂ : subgroup G) [H₁.normal] [H₂.normal] :
  ⁅H₁, H₂⁆ = normal_closure {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x} :=
by rw [← normal_closure_eq_self ⁅H₁, H₂⁆, general_commutator_def,
  normal_closure_closure_eq_normal_closure]

lemma general_commutator_le (H₁ H₂ : subgroup G) (K : subgroup G) :
  ⁅H₁, H₂⁆ ≤ K ↔ ∀ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ ∈ K :=
begin
  rw [general_commutator, closure_le],
  split,
  { intros h p hp q hq,
    exact h ⟨p, hp, q, hq, rfl⟩, },
  { rintros h x ⟨p, hp, q, hq, rfl⟩,
    exact h p hp q hq, }
end

lemma general_commutator_containment (H₁ H₂ : subgroup G) {p q : G} (hp : p ∈ H₁) (hq : q ∈ H₂) :
  p * q * p⁻¹ * q⁻¹∈ ⁅H₁, H₂⁆:=
(general_commutator_le H₁ H₂ ⁅H₁, H₂⁆).mp (le_refl ⁅H₁, H₂⁆) p hp q hq

lemma general_commutator_comm (H₁ H₂ : subgroup G) : ⁅H₁, H₂⁆ = ⁅H₂, H₁⁆ :=
begin
  suffices : ∀ H₁ H₂ : subgroup G, ⁅H₁, H₂⁆ ≤ ⁅H₂, H₁⁆, { exact le_antisymm (this _ _) (this _ _) },
  intros H₁ H₂,
  rw general_commutator_le,
  intros p hp q hq,
  have h : (p * q * p⁻¹ * q⁻¹)⁻¹ ∈ ⁅H₂, H₁⁆ := subset_closure ⟨q, hq, p, hp, by group⟩,
  convert inv_mem ⁅H₂, H₁⁆ h,
  group,
end

lemma general_commutator_le_right (H₁ H₂ : subgroup G) [h : normal H₂] :
  ⁅H₁, H₂⁆ ≤ H₂ :=
begin
  rw general_commutator_le,
  intros p hp q hq,
  exact mul_mem H₂ (h.conj_mem q hq p) (inv_mem H₂ hq),
end

lemma general_commutator_le_left (H₁ H₂ : subgroup G) [h : normal H₁] :
  ⁅H₁, H₂⁆ ≤ H₁ :=
begin
  rw general_commutator_comm,
  exact general_commutator_le_right H₂ H₁,
end

@[simp] lemma general_commutator_bot (H : subgroup G) : ⁅H, ⊥⁆ = (⊥ : subgroup G) :=
by { rw eq_bot_iff, exact general_commutator_le_right H ⊥ }

@[simp] lemma bot_general_commutator (H : subgroup G) : ⁅(⊥ : subgroup G), H⁆ = (⊥ : subgroup G) :=
by { rw eq_bot_iff, exact general_commutator_le_left ⊥ H }

lemma general_commutator_le_inf (H₁ H₂ : subgroup G) [normal H₁] [normal H₂] :
  ⁅H₁, H₂⁆ ≤ H₁ ⊓ H₂ :=
by simp only [general_commutator_le_left, general_commutator_le_right, le_inf_iff, and_self]

end general_commutator

section derived_series

variables (G)

/-- The derived series of the group `G`, obtained by starting from the subgroup `⊤` and repeatedly
  taking the commutator of the previous subgroup with itself for `n` times. -/
def derived_series : ℕ → subgroup G
| 0       := ⊤
| (n + 1) := ⁅(derived_series n), (derived_series n)⁆

@[simp] lemma derived_series_zero : derived_series G 0 = ⊤ := rfl

@[simp] lemma derived_series_succ (n : ℕ) :
  derived_series G (n + 1) = ⁅(derived_series G n), (derived_series G n)⁆ := rfl

lemma derived_series_normal (n : ℕ) : (derived_series G n).normal :=
begin
  induction n with n ih,
  { exact subgroup.top_normal, },
  { rw derived_series_succ,
    exactI general_commutator_normal (derived_series G n) (derived_series G n), }
end

@[simp] lemma general_commutator_eq_commutator :
  ⁅(⊤ : subgroup G), (⊤ : subgroup G)⁆ = commutator G :=
begin
  rw [commutator, general_commutator_def'],
  apply le_antisymm; apply normal_closure_mono,
  { exact λ x ⟨p, _, q, _, h⟩, ⟨p, q, h⟩, },
  { exact λ x ⟨p, q, h⟩, ⟨p, mem_top p, q, mem_top q, h⟩, }
end

lemma commutator_def' : commutator G = subgroup.closure {x : G | ∃ p q, p * q * p⁻¹ * q⁻¹ = x} :=
begin
  rw [← general_commutator_eq_commutator, general_commutator],
  apply le_antisymm; apply closure_mono,
  { exact λ x ⟨p, _, q, _, h⟩, ⟨p, q, h⟩ },
  { exact λ x ⟨p, q, h⟩, ⟨p, mem_top p, q, mem_top q, h⟩ }
end

@[simp] lemma derived_series_one : derived_series G 1 = commutator G :=
general_commutator_eq_commutator G

end derived_series

section commutator_map

lemma map_commutator_eq_commutator_map (H₁ H₂ : subgroup G) :
  ⁅H₁, H₂⁆.map f = ⁅H₁.map f, H₂.map f⁆ :=
begin
  rw [general_commutator, general_commutator, monoid_hom.map_closure],
  apply le_antisymm; apply closure_mono,
  { rintros _ ⟨x, ⟨p, hp, q, hq, rfl⟩, rfl⟩,
    refine ⟨f p, mem_map.mpr ⟨p, hp, rfl⟩, f q, mem_map.mpr ⟨q, hq, rfl⟩, by simp *⟩, },
  { rintros x ⟨_, ⟨p, hp, rfl⟩, _, ⟨q, hq, rfl⟩, rfl⟩,
    refine ⟨p * q * p⁻¹ * q⁻¹, ⟨p, hp, q, hq, rfl⟩, by simp *⟩, },
end

lemma commutator_le_map_commutator {H₁ H₂ : subgroup G} {K₁ K₂ : subgroup G'} (h₁ : K₁ ≤ H₁.map f)
  (h₂ : K₂ ≤ H₂.map f) : ⁅K₁, K₂⁆ ≤ ⁅H₁, H₂⁆.map f :=
by { rw map_commutator_eq_commutator_map, exact general_commutator_mono h₁ h₂ }

section derived_series_map

variables (f)

lemma map_derived_series_le_derived_series (n : ℕ) :
  (derived_series G n).map f ≤ derived_series G' n :=
begin
  induction n with n ih,
  { simp only [derived_series_zero, le_top], },
  { simp only [derived_series_succ, map_commutator_eq_commutator_map, general_commutator_mono, *], }
end

variables {f}

lemma derived_series_le_map_derived_series (hf : function.surjective f) (n : ℕ) :
  derived_series G' n ≤ (derived_series G n).map f :=
begin
  induction n with n ih,
  { rwa [derived_series_zero, derived_series_zero, top_le_iff, ← monoid_hom.range_eq_map,
    ← monoid_hom.range_top_iff_surjective.mpr], },
  { simp only [*, derived_series_succ, commutator_le_map_commutator], }
end

lemma map_derived_series_eq (hf : function.surjective f) (n : ℕ) :
  (derived_series G n).map f = derived_series G' n :=
le_antisymm (map_derived_series_le_derived_series f n) (derived_series_le_map_derived_series hf n)

end derived_series_map
end commutator_map

section solvable

variables (G)

/-- A group `G` is solvable if its derived series is eventually trivial. We use this definition
  because it's the most convenient one to work with. -/
class is_solvable : Prop :=
(solvable : ∃ n : ℕ, derived_series G n = ⊥)

lemma is_solvable_def : is_solvable G ↔ ∃ n : ℕ, derived_series G n = ⊥ :=
⟨λ h, h.solvable, λ h, ⟨h⟩⟩

@[priority 100]
instance comm_group.is_solvable {G : Type*} [comm_group G] : is_solvable G :=
begin
  use 1,
  rw [eq_bot_iff, derived_series_one],
  calc commutator G ≤ (monoid_hom.id G).ker : abelianization.commutator_subset_ker (monoid_hom.id G)
  ... = ⊥ : rfl,
end

lemma is_solvable_of_comm {G : Type*} [hG : group G]
  (h : ∀ a b : G, a * b = b * a) : is_solvable G :=
begin
  letI hG' : comm_group G := { mul_comm := h .. hG },
  tactic.unfreeze_local_instances,
  cases hG,
  exact comm_group.is_solvable,
end

lemma is_solvable_of_top_eq_bot (h : (⊤ : subgroup G) = ⊥) : is_solvable G :=
⟨⟨0, h⟩⟩

@[priority 100]
instance is_solvable_of_subsingleton [subsingleton G] : is_solvable G :=
is_solvable_of_top_eq_bot G (by ext; simp at *)

variables {G}

lemma solvable_of_solvable_injective (hf : function.injective f) [h : is_solvable G'] :
  is_solvable G :=
begin
  rw is_solvable_def at *,
  cases h with n hn,
  use n,
  rw ← map_eq_bot_iff_of_injective _ hf,
  rw eq_bot_iff at *,
  calc map f (derived_series G n) ≤ derived_series G' n : map_derived_series_le_derived_series f n
  ... ≤ ⊥ : hn,
end

instance subgroup_solvable_of_solvable (H : subgroup G) [h : is_solvable G] : is_solvable H :=
solvable_of_solvable_injective (show function.injective (subtype H), from subtype.val_injective)

lemma solvable_of_surjective (hf : function.surjective f) [h : is_solvable G] :
  is_solvable G' :=
begin
  rw is_solvable_def at *,
  cases h with n hn,
  use n,
  calc derived_series G' n = (derived_series G n).map f : eq.symm (map_derived_series_eq hf n)
    ... = (⊥ : subgroup G).map f : by rw hn
    ... = ⊥ : map_bot f,
end

instance solvable_quotient_of_solvable (H : subgroup G) [H.normal] [h : is_solvable G] :
  is_solvable (quotient_group.quotient H) :=
solvable_of_surjective (show function.surjective (quotient_group.mk' H), by tidy)

lemma solvable_of_ker_le_range {G' G'' : Type*} [group G'] [group G''] (f : G' →* G)
  (g : G →* G'') (hfg : g.ker ≤ f.range) [hG' : is_solvable G'] [hG'' : is_solvable G''] :
  is_solvable G :=
begin
  tactic.unfreeze_local_instances,
  obtain ⟨n, hn⟩ := hG'',
  suffices : ∀ k : ℕ, derived_series G (n + k) ≤ (derived_series G' k).map f,
  { obtain ⟨m, hm⟩ := hG',
    use n + m,
    specialize this m,
    rwa [hm, map_bot, le_bot_iff] at this },
  intro k,
  induction k with k hk,
  { rw [add_zero, derived_series_zero, ←monoid_hom.range_eq_map],
    refine le_trans _ hfg,
    rw [←map_eq_bot_iff, eq_bot_iff, ←hn],
    exact map_derived_series_le_derived_series g n },
  { rw [nat.add_succ, derived_series_succ, derived_series_succ],
    exact commutator_le_map_commutator hk hk },
end

instance solvable_prod {G' : Type*} [group G'] [h : is_solvable G] [h' : is_solvable G'] :
  is_solvable (G × G') :=
solvable_of_ker_le_range (monoid_hom.inl G G') (monoid_hom.snd G G')
  (λ x hx, ⟨x.1, prod.ext rfl hx.symm⟩)

end solvable

section is_simple_group

variable [is_simple_group G]

lemma is_simple_group.derived_series_succ {n : ℕ} : derived_series G n.succ = commutator G :=
begin
  induction n with n ih,
  { exact derived_series_one _ },
  rw [derived_series_succ, ih],
  cases (commutator.normal G).eq_bot_or_eq_top with h h; simp [h]
end

lemma is_simple_group.comm_iff_is_solvable :
  (∀ a b : G, a * b = b * a) ↔ is_solvable G :=
⟨is_solvable_of_comm, λ ⟨⟨n, hn⟩⟩, begin
  cases n,
  { rw derived_series_zero at hn,
    intros a b,
    refine (mem_bot.1 _).trans (mem_bot.1 _).symm;
    { rw ← hn,
      exact mem_top _ } },
  { rw is_simple_group.derived_series_succ at hn,
    intros a b,
    rw [← mul_inv_eq_one, mul_inv_rev, ← mul_assoc, ← mem_bot, ← hn],
    exact subset_normal_closure ⟨a, b, rfl⟩ }
end⟩

end is_simple_group

section perm_not_solvable

lemma not_solvable_of_mem_derived_series {g : G} (h1 : g ≠ 1)
  (h2 : ∀ n : ℕ, g ∈ derived_series G n) : ¬ is_solvable G :=
mt (is_solvable_def _).mp (not_exists_of_forall_not
  (λ n h, h1 (subgroup.mem_bot.mp ((congr_arg (has_mem.mem g) h).mp (h2 n)))))

/-- A type with 5 terms -/
inductive weekday : Type
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday

namespace weekday

instance : inhabited weekday := ⟨monday⟩

instance : decidable_eq weekday :=
begin
  rintros (_ | _) (_ | _),
  any_goals { exact is_true rfl },
  all_goals { exact is_false (by trivial) },
end

/-- A 3-cycle -/
def g1 : weekday → weekday
| monday := monday
| tuesday := tuesday
| wednesday := thursday
| thursday := friday
| friday := wednesday

/-- A 3-cycle -/
def g2 : weekday → weekday
| monday := monday
| tuesday := tuesday
| wednesday := friday
| thursday := wednesday
| friday := thursday

/-- A (2,2)-cycle -/
def g3 : weekday → weekday
| monday := thursday
| tuesday := friday
| wednesday := wednesday
| thursday := monday
| friday := tuesday

/-- A 3-cycle -/
def g4 : weekday → weekday
| monday := wednesday
| tuesday := tuesday
| wednesday := friday
| thursday := thursday
| friday := monday

/-- A 3-cycle -/
def g5 : weekday → weekday
| monday := friday
| tuesday := tuesday
| wednesday := monday
| thursday := thursday
| friday := wednesday

/-- A 3-cycle -/
def σ1 : weekday ≃ weekday :=
{ to_fun := g1,
  inv_fun := g2,
  left_inv := λ x, by { cases x, all_goals { refl } },
  right_inv := λ x, by { cases x, all_goals { refl } } }

/-- A (2,2)-cycle -/
def σ2 : weekday ≃ weekday :=
{ to_fun := g3,
  inv_fun := g3,
  left_inv := λ x, by { cases x, all_goals { refl } },
  right_inv := λ x, by { cases x, all_goals { refl } } }

/-- A 3-cycle -/
def σ3 : weekday ≃ weekday :=
{ to_fun := g4,
  inv_fun := g5,
  left_inv := λ x, by { cases x, all_goals { refl } },
  right_inv := λ x, by { cases x, all_goals { refl } } }

lemma mem_derived_series (n : ℕ) : σ1 ∈ derived_series (equiv.perm weekday) n :=
begin
  induction n with n ih,
  { exact mem_top σ1 },
  rw (show σ1 = σ3 * ((σ2 * σ1 * σ2) * σ1 * (σ2 * σ1 * σ2⁻¹)⁻¹ * σ1⁻¹) * σ3⁻¹,
      by { ext, cases x, all_goals { refl } }),
  exact (derived_series_normal _ _).conj_mem _
    (general_commutator_containment _ _ ((derived_series_normal _ _).conj_mem _ ih _) ih) _,
end

lemma not_solvable : ¬ is_solvable (equiv.perm weekday) :=
 not_solvable_of_mem_derived_series (mt equiv.ext_iff.mp
  (not_forall_of_exists_not ⟨wednesday, by trivial⟩)) mem_derived_series

lemma card : cardinal.mk weekday = ↑5 :=
begin
  letI : fintype weekday := fintype.mk
    (finset.mk ↑[monday, tuesday, wednesday, thursday, friday] dec_trivial)
    (by { rintros (_ | _), all_goals { dec_trivial } }),
  exact cardinal.fintype_card weekday,
end

end weekday

lemma equiv.perm.not_solvable (X : Type*) (hX : 5 ≤ cardinal.mk X) :
  ¬ is_solvable (equiv.perm X) :=
begin
  introI h,
  have key : nonempty (weekday ↪ X),
  { rwa [←cardinal.lift_mk_le, weekday.card, cardinal.lift_nat_cast, nat.cast_bit1,
    nat.cast_bit0, nat.cast_one, cardinal.lift_id] },
  exact weekday.not_solvable (solvable_of_solvable_injective
    (equiv.perm.via_embedding_hom_injective (nonempty.some key))),
end

end perm_not_solvable
