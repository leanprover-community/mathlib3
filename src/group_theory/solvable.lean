/-
Copyright (c) 2021 Jordan Brown, Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jordan Brown, Thomas Browning and Patrick Lutz
-/

import group_theory.abelianization
import data.bracket
import set_theory.cardinal
import data.equiv.basic

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

open subgroup monoid_hom


variables {G : Type*} [group G]

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
  rw group.mem_conjugates_of_set_iff at h,
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

lemma general_commutator_containment (H₁ H₂ : subgroup G):∀ p∈ H₁,∀ q∈ H₂, p * q * p⁻¹ * q⁻¹∈ ⁅H₁, H₂ ⁆:=
begin
  apply (general_commutator_le H₁ H₂ ⁅ H₁, H₂⁆).1,
  tauto,
end

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

variables {G} {G' : Type*} [group G'] {f : G →* G'}

lemma map_commutator_eq_commutator_map (H₁ H₂ : subgroup G) :
  ⁅H₁, H₂⁆.map f = ⁅H₁.map f, H₂.map f⁆ :=
begin
  rw [general_commutator, general_commutator, map_closure],
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

variables {f}(H : subgroup G)

lemma derived_series_le_map_derived_series (hf : function.surjective f) (n : ℕ) :
  derived_series G' n ≤ (derived_series G n).map f :=
begin
  induction n with n ih,
  { rwa [derived_series_zero, derived_series_zero, top_le_iff, ← range_eq_map,
    ← range_top_iff_surjective.mpr], },
  { simp only [*, derived_series_succ, commutator_le_map_commutator], }
end

lemma map_derived_series_eq (hf : function.surjective f) (n : ℕ) :
  (derived_series G n).map f = derived_series G' n :=
le_antisymm (map_derived_series_le_derived_series f n) (derived_series_le_map_derived_series hf n)


lemma derived_series_additive (n m : ℕ) : derived_series G (n + m) = lift (derived_series (derived_series G n) m) :=
begin
  induction m with m ih,
  { simp only [derived_series_zero, add_zero, lift_top], },
  { rw [nat.add_succ, derived_series_succ, derived_series_succ, ih,
    lift_commutator_eq_commutator_lift_lift], }
end

lemma derived_series_lift_monotonic {H K : subgroup G} (h : H ≤ K) (n : ℕ) :
  (derived_series H n).lift ≤ (derived_series K n).lift :=
begin
  induction n with n ih,
  { simp only [derived_series_zero, lift_top, h], },
  { simp only [derived_series_succ, lift_commutator_eq_commutator_lift_lift,
    general_commutator_mono, ih], }
end

lemma map_derived_series_leq_derived_series {G' : Type*} [group G'] {H : subgroup G} {f : G' →* G} (h : H ≤ f.range) (n : ℕ) :
  (derived_series H n).lift ≤ (derived_series G' n).map f :=
begin
  induction n with n ih,
  { rw monoid_hom.range_eq_map at h,
    rwa [derived_series_zero, derived_series_zero, lift_top], },
  { rw [derived_series_succ, derived_series_succ, lift_commutator_eq_commutator_lift_lift],
    exact commutator_le_map_commutator ih ih, },
end

lemma map_derived_series_monotonic {G' G'' : Type*}[group G'][group G'']{f : G' →* G}{g : G'' →* G}(h : f.range ≤ g.range)
  (n : ℕ) : (derived_series G' n).map f ≤ (derived_series G'' n).map g :=
begin
  induction n with n ih,
  { rw [monoid_hom.range_eq_map, monoid_hom.range_eq_map] at h,
    rwa [derived_series_zero, derived_series_zero], },
  { simp only [derived_series_succ, map_commutator_eq_commutator_map, general_commutator_mono,ih],},
end

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
instance is_solvable_of_comm {G : Type*} [comm_group G] : is_solvable G :=
begin
  use 1,
  rw [eq_bot_iff, derived_series_one],
  calc commutator G ≤ (monoid_hom.id G).ker : abelianization.commutator_subset_ker (id G)
  ... = ⊥ : rfl,
end

lemma is_solvable_of_top_eq_bot (h : (⊤ : subgroup G) = ⊥) : is_solvable G :=
⟨⟨0, h⟩⟩

@[priority 100]
instance is_solvable_of_subsingleton [subsingleton G] : is_solvable G :=
is_solvable_of_top_eq_bot G (by ext; simp at *)

variables {G} {G' : Type*} [group G'] {f : G →* G'}

lemma solvable_of_solvable_injective (hf : function.injective f) [h : is_solvable G'] :
  is_solvable G :=
begin
  rw is_solvable_def at *,
  cases h with n hn,
  use n,
  rw ← map_eq_bot_iff hf,
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


open quotient_group

instance solvable_quotient_of_solvable (H : subgroup G) [H.normal] [h : is_solvable G] :
  is_solvable (quotient H) :=
solvable_of_surjective (show function.surjective (quotient_group.mk' H), by tidy)

lemma le_ker_iff_map_eq_bot {G' : Type*} [group G'] (f : G →* G') {H : subgroup G} :
 H.map f ≤ ⊥ ↔ H ≤ f.ker :=
begin
  split,
  { intros h x hx,
    rw [← eq_bot_iff, eq_bot_iff_forall] at h,
    exact (monoid_hom.mem_ker f).mpr (h (f x) ⟨x, hx, rfl⟩), },
  { rintros h _ ⟨x, hx, rfl⟩,
    exact mem_bot.mpr ((monoid_hom.mem_ker f).mp (h hx)), },
end

theorem eq_top_of_trivial_quotient (N:subgroup G) [N.normal]
(H : (⊤ : subgroup (quotient N)) ≤ ⊥) :
 N = ⊤ :=
begin
  rw [← ker_mk N, eq_top_iff, ker, ← subgroup.map_le_iff_le_comap],
  exact le_trans le_top H,
end

lemma derived_series_le_ker {G' : Type*} [group G'] (f : G →* G') (h : is_solvable G') :
  ∃ n, derived_series G n ≤ f.ker :=
begin
  rw is_solvable_def at h,
  cases h with n hn,
  have key := map_derived_series_le_derived_series f n,
  exact ⟨n, by rwa [hn, le_ker_iff_map_eq_bot] at key⟩,
end

lemma range_subtype (H : subgroup G) : H.subtype.range = H :=
by { ext, exact ⟨λ ⟨⟨x, hx⟩, rfl⟩, hx, λ hx, ⟨⟨x, hx⟩, rfl⟩⟩ }


lemma derived_series_le_of_solvable_quotient (H : subgroup G) [H.normal]
  (h : is_solvable (quotient_group.quotient H)) : ∃ n, (derived_series G n) ≤ H :=
by {rw ← ker_mk H, exact derived_series_le_ker (mk' H) h}


lemma solvability_sequence {G' G'' : Type*} [group G'] [group G''] {f : G' →* G}
  {g : G →* G''} (hfg : g.ker ≤ f.range) (hG' : is_solvable G') (hG'' : is_solvable G'') :
  is_solvable G :=
begin
  rw is_solvable_def at hG' ⊢,
  cases hG' with n hn,
  obtain ⟨m, hm⟩ := derived_series_le_ker g hG'',
  use m + n,
  rw [derived_series_additive, eq_bot_iff],
  replace hm := calc derived_series G m ≤ g.ker : hm
  ... ≤ f.range : hfg,
  calc (derived_series (derived_series G m) n).lift ≤ map f (derived_series G' n) :
    map_derived_series_leq_derived_series hm n
  ... = map f ⊥ : by rw hn
  ... = ⊥ : map_bot f,
end

lemma short_exact_sequence_solvable {G' G'' : Type*} [group G'] [group G''] (f : G' →* G)
  (g : G →* G'') (hfg : f.range = g.ker) (hG' : is_solvable G') (hG'' : is_solvable G'') :
  is_solvable G :=
begin
  have z : g.ker ≤ f.range,
  {rw hfg,
  exact le_refl g.ker},
  exact solvability_sequence z hG' hG'',
end


lemma subgroup_quotient_solvable_solvable (H : subgroup G) [H.normal] (h : is_solvable H)
  (h' : is_solvable (quotient_group.quotient H)) : is_solvable G :=
begin
  refine short_exact_sequence_solvable (subtype H) (mk' H) _ h h',
  rw [ker_mk, range_subtype],
end

lemma solvable_prod {G' : Type*} [group G'] (h : is_solvable G) (h' : is_solvable G') :
  is_solvable (G × G') :=
begin
  refine short_exact_sequence_solvable (monoid_hom.inl G G') (monoid_hom.snd G G') _ h h',
  ext x, split,
  { rintros ⟨y, rfl⟩,
    simp only [monoid_hom.mem_ker, monoid_hom.inl_apply, monoid_hom.coe_snd], },
  { cases x with x y,
    intros hx,
    simp only [monoid_hom.mem_ker, monoid_hom.coe_snd] at hx,
    simp only [monoid_hom.mem_range, monoid_hom.inl_apply, hx],
    use x, }
end


section symmetric_unsolvable

inductive weekday : Type
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday

open weekday

def g1 : weekday → weekday
| monday := monday
| tuesday := tuesday
| wednesday := thursday
| thursday := friday
| friday := wednesday

def g2 : weekday → weekday
| monday := monday
| tuesday := tuesday
| wednesday := friday
| thursday := wednesday
| friday := thursday

def g3 : weekday → weekday
| monday := thursday
| tuesday := friday
| wednesday := wednesday
| thursday := monday
| friday := tuesday

def g4 : weekday → weekday
| monday := wednesday
| tuesday := tuesday
| wednesday := friday
| thursday := thursday
| friday := monday

def g5 : weekday → weekday
| monday := friday
| tuesday := tuesday
| wednesday := monday
| thursday := thursday
| friday := wednesday

def σ1 : weekday ≃ weekday :=
{ to_fun := g1,
  inv_fun := g2,
  left_inv := λ x, by { cases x, all_goals { refl } },
  right_inv := λ x, by { cases x, all_goals { refl } } }

def σ2 : weekday ≃ weekday :=
{ to_fun := g3,
  inv_fun := g3,
  left_inv := λ x, by { cases x, all_goals { refl } },
  right_inv := λ x, by { cases x, all_goals { refl } } }

def σ3 : weekday ≃ weekday :=
{ to_fun := g4,
  inv_fun := g5,
  left_inv := λ x, by { cases x, all_goals { refl } },
  right_inv := λ x, by { cases x, all_goals { refl } } }

lemma alternating_stability (n : ℕ) : σ1 ∈ derived_series (equiv.perm weekday) n :=
begin
  induction n with n ih,
  { exact mem_top σ1 },
  rw (show σ1 = σ3 * ((σ2 * σ1 * σ2) * σ1 * (σ2 * σ1 * σ2⁻¹)⁻¹ * σ1⁻¹) * σ3⁻¹,
      by { ext, cases x, all_goals { refl } }),
  exact (derived_series_normal _ _).conj_mem _ (general_commutator_containment _ _ _
    ((derived_series_normal _ _).conj_mem _ ih _) _ ih) _,
end

lemma not_solvable_of_mem_derived_series {g : G} (h1 : g ≠ 1)
  (h2 : ∀ n : ℕ, g ∈ derived_series G n) : ¬ is_solvable G :=
mt (is_solvable_def _).mp (not_exists_of_forall_not (λ n, mt subgroup.ext'_iff.mp
  (mt set.ext_iff.mp (not_forall_of_exists_not
    ⟨g, λ h, (not_congr (iff.symm h)).mp (mt subgroup.mem_bot.mp h1) (h2 n)⟩))))

lemma weekday_perm_unsolvable : ¬ is_solvable (equiv.perm weekday) :=
 not_solvable_of_mem_derived_series (mt equiv.ext_iff.mp
  (not_forall_of_exists_not ⟨wednesday, by trivial⟩)) alternating_stability


open cardinal
universes u

lemma weekday_card : (5:cardinal)≤ mk weekday:=sorry

lemma five_le_iff (α: Type u): (5 : cardinal) ≤ mk α ↔ ∃x₀ x₁ x₂ x₃ x₄  : α, x₀ ≠ x₁ ∧ x₀ ≠ x₂ ∧ x₀ ≠ x₃ ∧ x₀ ≠ x₄ ∧
x₁ ≠ x₂  ∧ x₁ ≠ x₃ ∧ x₁ ≠ x₄ ∧ x₂ ≠ x₃ ∧ x₃ ≠ x₄:=
begin
  split,
  rintro ⟨f⟩, refine ⟨f $ sum.inr punit.star, _⟩,
  refine ⟨f $ (sum.inl (sum.inr (sum.inr  punit.star))),_⟩,
  refine ⟨f $ (sum.inl (sum.inr (sum.inl  punit.star))),_⟩,
  refine ⟨f $ (sum.inl (sum.inl (sum.inl  punit.star))),_⟩,
  refine ⟨f $ (sum.inl (sum.inl (sum.inr  punit.star))),_⟩,
  split,
  intro h,
  cases f.2 h,
  split,
  intro h,
  cases f.2 h,
  split,
  intro h,
  cases f.2 h,
  split,
  intro h,
  cases f.2 h,
  split,
  intro h,
  cases f.2 h,
  split,
  intro h,
  cases f.2 h,
  split,
  intro h,
  cases f.2 h,
  split,
  intro h,
  cases f.2 h,

  intro h,
  cases f.2 h,
  rintro ⟨ a,β,γ,δ,ε,hs ⟩ ,
  let five:=((punit ⊕ punit) ⊕ punit ⊕ punit) ⊕ punit,
  --have u: ∃g: five → α,function.injective g,
  let h : five → α := λ s₀, sum.rec_on s₀  (λ s₁, sum.rec_on s₁  (λ s₂ ,sum.rec_on s₂   (λ x,a)(λx,β )) (λ s₃  ,sum.rec_on s₃   (λ x,γ )(λx,δ ) ))(λ x,ε ),
  --(λ s₁, sum.rec_on s₁ ((λ s₂, (sum.rec_on s₂ ((λ x,a) (λ x,β)))(λ s₃, sum.rec_on s₃((λ x,γ) (λ x,δ) ) )))) (λ x,ε),
  have h_inj: function.injective h,

  intros x y,
  induction x,
  induction y,
  induction x,
  induction y,
  induction x,
  induction y,
  have w: x=y,
  exact unit.ext,
  rw w,
  exact λ u, refl _,
  intro k,
  exfalso,
  have t:h(sum.inl (sum.inl (sum.inl x)))=a,
  refl,

  have ξ : h(sum.inl (sum.inl (sum.inr y)))=β ,
  refl,
  rw [t,ξ ] at k,
  exact hs.1 k,

  induction y,
  intro k,
  exfalso,
  have t:h(sum.inl (sum.inl (sum.inl y)))=a,
  refl,
  have ξ : h(sum.inl (sum.inl (sum.inr x)))=β ,
  refl,
  rw [t,ξ ] at k,
  exact hs.1 k.symm,
  have w: x=y,
  exact unit.ext,
  rw w,
  exact λ u, refl _,

  induction x,
  induction y,
  intro k,
  exfalso,
  have t:h(sum.inl (sum.inl (sum.inl y)))=a,
  refl,
  have ξ : h(sum.inl (sum.inr (sum.inl x)))=γ,
  refl,
  rw [t,ξ ] at k,
  exact (hs.2).1 k,

  intro k,
  exfalso,
  have t:h(sum.inl (sum.inl (sum.inl y)))=a,
  refl,
  have ξ : h(sum.inl (sum.inr (sum.inr x)))=δ ,
  refl,
  rw [t,ξ ] at k,
  exact ((hs.2).2).1 k,

  induction y,
  intro k,
  exfalso,
  have t:h(sum.inl (sum.inr (sum.inl y)))=γ ,
  refl,
  have ξ : h(sum.inl (sum.inl (sum.inr x)))=β  ,
  refl,
  rw [t,ξ ] at k,
  exact ((((hs.2).2).2).2).1 k,
  intro k,
  exfalso,
  have t:h(sum.inl (sum.inr (sum.inr y)))=δ  ,
  refl,
  have ξ : h(sum.inl (sum.inl (sum.inr x)))=β  ,
  refl,
  rw [t,ξ ] at k,
  exact (((((hs.2).2).2).2).2).1 k,

  induction x,
  induction y,
  induction y,

  intro k,
  exfalso,
  have t:h(sum.inl (sum.inl (sum.inl y)))=a,
  refl,
  have ξ : h(sum.inl (sum.inr (sum.inl x)))=γ  ,
  refl,
  rw [t,ξ ] at k,
  exact (hs.2).1 k.symm,

  intro k,
  exfalso,
  have t:h(sum.inl (sum.inl (sum.inr y)))=β ,
  refl,
  have ξ : h(sum.inl (sum.inr (sum.inl x)))=γ  ,
  refl,
  rw [t,ξ ] at k,
  exact ((((hs.2).2).2).2).1 k.symm,

  induction y,
  have w: x=y,
  exact unit.ext,
  rw w,
  exact λ u, refl _,
  intro k,
  exfalso,
  have t:h(sum.inl (sum.inr (sum.inr y)))=δ ,
  refl,
  have ξ : h(sum.inl (sum.inr (sum.inl x)))=γ  ,
  refl,
  rw [t,ξ ] at k,
  exact (((((((hs.2).2).2).2).2).2).2).1 k,

  induction y,
  induction y,

  intro k,
  exfalso,
  have t:h(sum.inl (sum.inl (sum.inl y)))=a,
  refl,
  have ξ : h(sum.inl (sum.inr (sum.inr x)))=δ  ,
  refl,
  rw [t,ξ ] at k,
  exact ((hs.2).2).1 k.symm,

  intro k,
  exfalso,
  have t:h(sum.inl (sum.inl (sum.inr y)))=β ,
  refl,
  have ξ : h(sum.inl (sum.inr (sum.inr x)))=δ  ,
  refl,
  rw [t,ξ ] at k,
  exact (((((hs.2).2).2).2).2).1 k.symm,

  induction y,
  intro k,
  exfalso,
  have t:h(sum.inl (sum.inr (sum.inl y)))=γ  ,
  refl,
  have ξ : h(sum.inl (sum.inr (sum.inr x)))=δ  ,
  refl,
  rw [t,ξ ] at k,
  exact (((((((hs.2).2).2).2).2).2).2).1 k.symm,



  --have v:=five.cases_on a β γ δ ε ,


  --apply cardinal.mk_le_of_injective,

    --rintro ⟨x, y, h⟩, by_contra h',
    --rw [not_le, ←nat.cast_two, nat_succ, lt_succ, nat.cast_one, le_one_iff_subsingleton] at h',
    --apply h, exactI subsingleton.elim _ _
  all_goals {sorry},

end


def equiv.perm.of_embedding {α β : Type*} [fintype α] [decidable_eq β]
  (e : equiv.perm α) (f : α ↪ β) : equiv.perm β :=
  begin
    have u:=f ∘ (equiv.set.image_of_inj_on f (⊤:set α ) (set.inj_on_of_injective f.inj' ⊤ )).inv_fun,
    have t: ¬ nonempty α  ∨ nonempty α,
    finish,

    have s:=function.injective.has_left_inverse f.inj' ,
    apply equiv.perm.of_subtype,
    -- (set.image f (⊤:set α )),

  end
  --function.injective.has_left_inverse f.to_fun f.inj'
  --equiv.perm.of_subtype (set.image f (⊤:set α )),

lemma equiv.perm_of_embedding_injective {α β : Type*} [fintype α] [decidable_eq β]
   (f : α ↪ β) : function.injective (λ e, equiv.perm.of_embedding e f):=sorry



lemma unsolvability_of_S_5 (X:Type u)(big:5≤ cardinal.mk X)[fintype X]:¬ is_solvable (equiv.perm X):=
begin
  --have x:=X.elems.val.to_list,
  have x:=(five_le_iff X).1 big,
  rcases x with ⟨ x₀,x₁, x₂, x₃, x₄ , s⟩,
  let map:weekday→ X:=λ x, weekday.cases_on x x₀ x₁ x₂ x₃ x₄,
  by_contradiction,
  --apply solvable_of_solvable_injective,


  unfold is_solvable,
  push_neg,
  have moscow:=_inst_3.elems,
  have russia:=_inst_3.complete,
  let delhi:=fintype.elems X,
  let paris:=(delhi).val,
  have france:=(delhi).nodup,
  have u: list X,
  exact list.nil,


  rw cardinal.le_mk_iff_exists_set at big,
  cases big with big_subset florida,
  --have v:cardinal.mk big_subset<cardinal.omega,
  --apply cardinal.lt_omega.2,
  --use 5,

  --exact florida,

  --have u: fintype big_subset,
  --apply fintype.of_equiv,
  have w:fintype.card ↥big_subset=5,

  --library_search,


  have equiv: nonempty((fin 5)≃ big_subset),

  apply fintype.card_eq.1,


  --library_search!,
  --have first: ∃ x_1,x_1∈ big_subset,
  sorry,

end


end solvable


end  symmetric_unsolvable



end solvable
