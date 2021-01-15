/-
Copyright (c) 2021 Jordan Brown, Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jordan Brown, Thomas Browning and Patrick Lutz
-/

import group_theory.abelianization
import data.bracket

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

section general_derived_series

variables {G} (H : subgroup G)

def general_derived_series (n : ℕ) : subgroup G :=
nat.rec_on n H (λ _ H, ⁅H, H⁆)

lemma general_derived_series_succ (n : ℕ) : general_derived_series H (nat.succ n) =
  ⁅general_derived_series H n, general_derived_series H n⁆ :=
rfl

lemma general_derived_series_zero : general_derived_series H 0 = H :=
rfl

lemma general_derived_series_one :
  general_derived_series H 1 = ⁅H, H⁆ :=
by rw [general_derived_series_succ, general_derived_series_zero]

lemma additive_general_derived_series (n m : ℕ) :
  general_derived_series H (n + m) = general_derived_series (general_derived_series H n) m :=
begin
  induction m with m ih,
  { simp only [general_derived_series_zero, add_zero], },
  { simp only [general_derived_series_succ, ih], },
end

lemma additive_general_derived_series' (n m : ℕ) :
  general_derived_series H (n + m) = general_derived_series (general_derived_series H m) n :=
begin
  rw add_comm n m,
  exact additive_general_derived_series H m n,
end

lemma general_derived_series_mono (K : subgroup G) (leq : H ≤ K) (n : ℕ) :
  general_derived_series H n ≤ general_derived_series K n :=
begin
  induction n with n ih,
  { simp only [general_derived_series_zero, leq] },
  { rw [general_derived_series_succ, general_derived_series_succ],
    exact general_commutator_mono ih ih },
end

lemma derived_series_eq_general_derived_series_top :
  derived_series G = general_derived_series (⊤ : subgroup G) :=
begin
  funext n,
  induction n with n ih,
  { rw [derived_series_zero, general_derived_series_zero], },
  { rw [derived_series_succ, general_derived_series_succ, ih], },
end




end general_derived_series

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

lemma map_general_derived_series_eq_general_derived_series_map (n : ℕ) :
  (general_derived_series H n).map f = general_derived_series (H.map f) n :=
begin
  induction n with n ih,
  { simp only [general_derived_series_zero], },
  { rw [general_derived_series_succ,general_derived_series_succ,
    map_commutator_eq_commutator_map, ih], },
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
⟨⟨0, by simp *⟩⟩

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

lemma le_ker_iff_map_eq_bot {G' : Type*} [group G'] (f : G →* G') {H : subgroup G} : H.map f ≤ ⊥ ↔ H ≤ f.ker :=
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


lemma derived_series_le_of_solvable_quotient (H : subgroup G) [H.normal]
  (h : is_solvable (quotient_group.quotient H)) : ∃ n, (derived_series G n) ≤ H :=
by {rw ← ker_mk H, exact derived_series_le_ker (mk' H) h}

lemma derived_series_le_map_derived_series_of_le_map {G' : Type*} [group G'] {f : G →* G'}
  {H : subgroup G} {K : subgroup G'} (h : K ≤ H.map f) (n : ℕ) :
  general_derived_series K n ≤ (general_derived_series H n).map f :=
calc general_derived_series K n
      ≤ general_derived_series (map f H) n : general_derived_series_mono _ _ h n
  ... = (general_derived_series H n).map f : by rw ← map_general_derived_series_eq_general_derived_series_map

lemma short_exact_sequence_solvable' {G' G'' : Type*} [group G'] [group G''] (f : G' →* G)
  (g : G →* G'') (hfg : f.range = g.ker) (hG' : is_solvable G') (hG'' : is_solvable G'') :
  is_solvable G :=
begin
  rw is_solvable_def at hG' ⊢,
  cases hG' with n hn,
  obtain ⟨m, hm⟩ := derived_series_le_ker g hG'',
  use n + m,
  rw [eq_bot_iff, derived_series_eq_general_derived_series_top, additive_general_derived_series',
    ← derived_series_eq_general_derived_series_top],
  rw [← hfg, monoid_hom.range_eq_map] at hm,
  calc general_derived_series (derived_series G m) n
      ≤ (general_derived_series (⊤ : subgroup G') n).map f : derived_series_le_map_derived_series_of_le_map hm n
  ... = (derived_series G' n).map f : by rw ← derived_series_eq_general_derived_series_top
  ... = (⊥ : subgroup G').map f : by rw hn
  ... = (⊥ : subgroup G) : map_bot f,
end

end solvable
