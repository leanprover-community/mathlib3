/-
Copyright (c) 2021 Jordan Brown, Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jordan Brown, Thomas Browning, Patrick Lutz
-/

import data.fin.vec_notation
import group_theory.abelianization
import group_theory.perm.via_embedding
import group_theory.subgroup.simple
import set_theory.cardinal.basic

/-!
# Solvable Groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
  { exactI subgroup.commutator_normal (derived_series G n) (derived_series G n) }
end

@[simp] lemma derived_series_one : derived_series G 1 = commutator G :=
rfl

end derived_series

section commutator_map

section derived_series_map

variables (f)

lemma map_derived_series_le_derived_series (n : ℕ) :
  (derived_series G n).map f ≤ derived_series G' n :=
begin
  induction n with n ih,
  { exact le_top },
  { simp only [derived_series_succ, map_commutator, commutator_mono, ih] }
end

variables {f}

lemma derived_series_le_map_derived_series (hf : function.surjective f) (n : ℕ) :
  derived_series G' n ≤ (derived_series G n).map f :=
begin
  induction n with n ih,
  { exact (map_top_of_surjective f hf).ge },
  { exact commutator_le_map_commutator ih ih }
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
⟨⟨1, le_bot_iff.mp (abelianization.commutator_subset_ker (monoid_hom.id G))⟩⟩

lemma is_solvable_of_comm {G : Type*} [hG : group G]
  (h : ∀ a b : G, a * b = b * a) : is_solvable G :=
begin
  letI hG' : comm_group G := { mul_comm := h .. hG },
  casesI hG,
  exact comm_group.is_solvable,
end

lemma is_solvable_of_top_eq_bot (h : (⊤ : subgroup G) = ⊥) : is_solvable G :=
⟨⟨0, h⟩⟩

@[priority 100]
instance is_solvable_of_subsingleton [subsingleton G] : is_solvable G :=
is_solvable_of_top_eq_bot G (by ext; simp at *)

variables {G}

lemma solvable_of_ker_le_range {G' G'' : Type*} [group G'] [group G''] (f : G' →* G)
  (g : G →* G'') (hfg : g.ker ≤ f.range) [hG' : is_solvable G'] [hG'' : is_solvable G''] :
  is_solvable G :=
begin
  obtain ⟨n, hn⟩ := id hG'',
  obtain ⟨m, hm⟩ := id hG',
  refine ⟨⟨n + m, le_bot_iff.mp (map_bot f ▸ (hm ▸ _))⟩⟩,
  clear hm,
  induction m with m hm,
  { exact f.range_eq_map ▸ ((derived_series G n).map_eq_bot_iff.mp (le_bot_iff.mp
      ((map_derived_series_le_derived_series g n).trans hn.le))).trans hfg },
  { exact commutator_le_map_commutator hm hm },
end

lemma solvable_of_solvable_injective (hf : function.injective f) [h : is_solvable G'] :
  is_solvable G :=
solvable_of_ker_le_range (1 : G' →* G) f ((f.ker_eq_bot_iff.mpr hf).symm ▸ bot_le)

instance subgroup_solvable_of_solvable (H : subgroup G) [h : is_solvable G] : is_solvable H :=
solvable_of_solvable_injective H.subtype_injective

lemma solvable_of_surjective (hf : function.surjective f) [h : is_solvable G] :
  is_solvable G' :=
solvable_of_ker_le_range f (1 : G' →* G) ((f.range_top_of_surjective hf).symm ▸ le_top)

instance solvable_quotient_of_solvable (H : subgroup G) [H.normal] [h : is_solvable G] :
  is_solvable (G ⧸ H) :=
solvable_of_surjective (quotient_group.mk'_surjective H)

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
  { exact derived_series_one G },
  rw [derived_series_succ, ih],
  cases (commutator.normal G).eq_bot_or_eq_top with h h,
  { rw [h, commutator_bot_left] },
  { rwa h },
end

lemma is_simple_group.comm_iff_is_solvable :
  (∀ a b : G, a * b = b * a) ↔ is_solvable G :=
⟨is_solvable_of_comm, λ ⟨⟨n, hn⟩⟩, begin
  cases n,
  { intros a b,
    refine (mem_bot.1 _).trans (mem_bot.1 _).symm;
    { rw ← hn,
      exact mem_top _ } },
  { rw is_simple_group.derived_series_succ at hn,
    intros a b,
    rw [← mul_inv_eq_one, mul_inv_rev, ← mul_assoc, ← mem_bot, ← hn, commutator_eq_closure],
    exact subset_closure ⟨a, b, rfl⟩ }
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
  have key : x = z * ⁅x, y * x * y⁻¹⁆ * z⁻¹ := by dec_trivial,
  refine not_solvable_of_mem_derived_series (show x ≠ 1, by dec_trivial) (λ n, _),
  induction n with n ih,
  { exact mem_top x },
  { rw [key, (derived_series_normal _ _).mem_comm_iff, inv_mul_cancel_left],
    exact commutator_mem_commutator ih ((derived_series_normal _ _).conj_mem _ ih _) },
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
