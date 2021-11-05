/-
Copyright (c) 2021 Jordan Brown, Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jordan Brown, Thomas Browning, Patrick Lutz
-/

import data.matrix.notation
import group_theory.abelianization
import set_theory.cardinal
import group_theory.general_commutator

/-!
# Solvable Groups

In this file we introduce the notion of a solvable group. We define a solvable group as one whose
derived series is eventually trivial. This requires defining the commutator of two subgroups and
the derived series of a group.

## Main definitions

* `derived_series G n` : the `n`th term in the derived series of `G`, defined by iterating
    `general_commutator` starting with the top subgroup
* `is_solvable G` : the group `G` is solvable
-/

open subgroup

variables {G G' : Type*} [group G] [group G'] {f : G →* G'}

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
  { exact (⊤ : subgroup G).normal_of_characteristic },
  { exactI general_commutator_normal (derived_series G n) (derived_series G n) }
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

lemma equiv.perm.fin_5_not_solvable : ¬ is_solvable (equiv.perm (fin 5)) :=
begin
  let x : equiv.perm (fin 5) := ⟨![1, 2, 0, 3, 4], ![2, 0, 1, 3, 4], dec_trivial, dec_trivial⟩,
  let y : equiv.perm (fin 5) := ⟨![3, 4, 2, 0, 1], ![3, 4, 2, 0, 1], dec_trivial, dec_trivial⟩,
  let z : equiv.perm (fin 5) := ⟨![0, 3, 2, 1, 4], ![0, 3, 2, 1, 4], dec_trivial, dec_trivial⟩,
  have x_ne_one : x ≠ 1, { rw [ne.def, equiv.ext_iff], dec_trivial },
  have key : x = z * (x * (y * x * y⁻¹) * x⁻¹ * (y * x * y⁻¹)⁻¹) * z⁻¹,
  { ext a, dec_trivial! },
  refine not_solvable_of_mem_derived_series x_ne_one (λ n, _),
  induction n with n ih,
  { exact mem_top x },
  { rw key,
    exact (derived_series_normal _ _).conj_mem _
      (general_commutator_containment _ _ ih ((derived_series_normal _ _).conj_mem _ ih _)) _ },
end

lemma equiv.perm.not_solvable (X : Type*) (hX : 5 ≤ cardinal.mk X) :
  ¬ is_solvable (equiv.perm X) :=
begin
  introI h,
  have key : nonempty (fin 5 ↪ X),
  { rwa [←cardinal.lift_mk_le, cardinal.mk_fin, cardinal.lift_nat_cast,
    nat.cast_bit1, nat.cast_bit0, nat.cast_one, cardinal.lift_id] },
  exact equiv.perm.fin_5_not_solvable (solvable_of_solvable_injective
    (equiv.perm.via_embedding_hom_injective (nonempty.some key))),
end

end perm_not_solvable
