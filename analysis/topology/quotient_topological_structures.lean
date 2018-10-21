/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

Topological structures on quotient rings and groups.
-/
import analysis.topology.completion
import group_theory.quotient_group

@[simp] lemma {u} eq_mpr_heq {α β : Sort u} (h : β = α) (x : α) : eq.mpr h x == x :=
by subst h; refl

open function set

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
-- variables [topological_space β] [topological_space γ] [topological_space δ]

namespace quot

protected def map {α} (r r' : α → α → Prop) (h : ∀a b, r a b → r' a b) (a : quot r) : quot r' :=
quot.hrec_on a (quot.mk r') $ assume a b hab, by rw [quot.sound (h a b hab)]

/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
protected def congr {α} {r r' : α → α → Prop} (eq : ∀a b, r a b ↔ r' a b) : quot r ≃ quot r' :=
⟨quot.map r r' (assume a b, (eq a b).1), quot.map r' r (assume a b, (eq a b).2),
  by rintros ⟨a⟩; refl, by rintros ⟨a⟩; refl⟩

end quot

namespace quotient

protected def congr {α} {r r' : setoid α} (eq : ∀a b, @setoid.r α r a b ↔ @setoid.r α r' a b) :
  quotient r ≃ quotient r' :=
quot.congr eq

end quotient

/-
namespace comm_ring
open equiv

protected def map {α β} (e : α ≃ β) (r : comm_ring α) : comm_ring β :=
{ zero := e r.zero,
  one  := e r.one,
  neg  := arrow_congr e e r.neg,
  add  := arrow_congr e (arrow_congr e e) r.add,
  mul  := arrow_congr e (arrow_congr e e) r.mul }

def comm_ring_congr {α β} (e : α ≃ β) : comm_ring α ≃ comm_ring β :=
{}

end comm_ring
-/

section topological_group
variables [topological_space α] [group α] [topological_group α] (N : set α) [normal_subgroup N]

@[to_additive quotient_add_group.quotient.topological_space]
instance : topological_space (quotient_group.quotient N) :=
by dunfold quotient_group.quotient; apply_instance

attribute [instance] quotient_add_group.quotient.topological_space

open quotient_group
@[to_additive quotient_add_group_saturate]
lemma quotient_group_saturate (s : set α) :
  (coe : α → quotient N) ⁻¹' ((coe : α → quotient N) '' s) = (⋃ x : N, (λ y, y*x.1) '' s) :=
begin
  ext x,
  simp only [mem_preimage_eq, mem_image, mem_Union, quotient_group.eq],
  split,
  { exact assume ⟨a, a_in, h⟩, ⟨⟨_, h⟩, a, a_in, mul_inv_cancel_left _ _⟩ },
  { exact assume ⟨⟨i, hi⟩, a, ha, eq⟩,
      ⟨a, ha, by simp only [eq.symm, (mul_assoc _ _ _).symm, inv_mul_cancel_left, hi]⟩ }
end

@[to_additive quotient_add_group.open_coe]
lemma quotient_group.open_coe : is_open_map (coe : α →  quotient N) :=
begin
  intros s s_op,
  change is_open ((coe : α →  quotient N) ⁻¹' (coe '' s)),
  rw quotient_group_saturate N s,
  apply is_open_Union,
  rintro ⟨n, _⟩,
  exact is_open_map_mul_right n s s_op
end

@[to_additive topological_add_group_quotient]
instance topological_group_quotient : topological_group (quotient N) :=
{ continuous_mul := begin
    have cont : continuous ((coe : α → quotient N) ∘ (λ (p : α × α), p.fst * p.snd)) :=
      continuous.comp continuous_mul' continuous_quot_mk,
    have quot : quotient_map (λ p : α × α, ((p.1:quotient N), (p.2:quotient N))),
    { apply is_open_map.to_quotient_map,
      { exact is_open_map.prod (quotient_group.open_coe N) (quotient_group.open_coe N) },
      { apply continuous.prod_mk,
        { exact continuous.comp continuous_fst continuous_quot_mk },
        { exact continuous.comp continuous_snd continuous_quot_mk } },
      { rintro ⟨⟨x⟩, ⟨y⟩⟩,
        exact ⟨(x, y), rfl⟩ } },
    exact (quotient_map.continuous_iff quot).2 cont,
  end,
  continuous_inv := begin
    apply continuous_quotient_lift,
    change continuous ((coe : α → quotient N) ∘ (λ (a : α), a⁻¹)),
    exact continuous.comp continuous_inv' continuous_quot_mk
  end }

attribute [instance] topological_add_group_quotient

end topological_group

section ideal_is_add_subgroup
variables [comm_ring α] {M : Type*} [module α M] (N : set α) [is_submodule N]

instance submodule_is_add_subgroup : is_add_subgroup N :=
{ zero_mem := is_submodule.zero,
  add_mem  := λ a b, is_submodule.add,
  neg_mem  := λ a, is_submodule.neg}

end ideal_is_add_subgroup

@[to_additive normal_add_subgroup_of_comm]
instance normal_subgroup_of_comm [comm_group α] (s : set α) [hs : is_subgroup s] :
  normal_subgroup s :=
{ normal := assume a hn b, by rwa [mul_comm b, mul_inv_cancel_right] }
attribute [instance] normal_add_subgroup_of_comm

section topological_ring
variables [topological_space α] [comm_ring α] [topological_ring α] (N : set α) [is_ideal N]
open quotient_ring

instance topological_ring_quotient_topology : topological_space (quotient N) :=
by dunfold quotient_ring.quotient ; apply_instance

-- this should be quotient_add_saturate ...
lemma quotient_ring_saturate (s : set α) :
  (coe : α → quotient N) ⁻¹' ((coe : α → quotient N) '' s) = (⋃ x : N, (λ y, x.1 + y) '' s) :=
begin
  ext x,
  simp only [mem_preimage_eq, mem_image, mem_Union, quotient_ring.eq],
  split,
  { exact assume ⟨a, a_in, h⟩, ⟨⟨_, is_ideal.neg_iff.1 h⟩, a, a_in, by simp⟩ },
  { exact assume ⟨⟨i, hi⟩, a, ha, eq⟩, ⟨a, ha,
      by simp only [eq.symm, -sub_eq_add_neg, add_comm i a, sub_add_eq_sub_sub, sub_self, zero_sub,
        is_ideal.neg_iff.symm, hi]⟩ }
end

lemma quotient_ring.is_open_map_coe : is_open_map (coe : α →  quotient N) :=
begin
  assume s s_op,
  show is_open ((coe : α →  quotient N) ⁻¹' (coe '' s)),
  rw quotient_ring_saturate N s,
  exact is_open_Union (assume ⟨n, _⟩, is_open_map_add_left n s s_op)
end

lemma quotient_ring.quotient_map_coe_coe : quotient_map (λ p : α × α, ((p.1:quotient N), (p.2:quotient N))) :=
begin
  apply is_open_map.to_quotient_map,
  { exact is_open_map.prod (quotient_ring.is_open_map_coe N) (quotient_ring.is_open_map_coe N) },
  { apply continuous.prod_mk,
    { exact continuous.comp continuous_fst continuous_quot_mk },
    { exact continuous.comp continuous_snd continuous_quot_mk } },
  { rintro ⟨⟨x⟩, ⟨y⟩⟩,
    exact ⟨(x, y), rfl⟩ }
end

instance topological_ring_quotient : topological_ring (quotient N) :=
{ continuous_add :=
    have cont : continuous ((coe : α → quotient N) ∘ (λ (p : α × α), p.fst + p.snd)) :=
      continuous.comp continuous_add' continuous_quot_mk,
    (quotient_map.continuous_iff (quotient_ring.quotient_map_coe_coe N)).2 cont,
  continuous_neg := continuous_quotient_lift _ (continuous.comp continuous_neg' continuous_quot_mk),
  continuous_mul :=
    have cont : continuous ((coe : α → quotient N) ∘ (λ (p : α × α), p.fst * p.snd)) :=
      continuous.comp continuous_mul' continuous_quot_mk,
    (quotient_map.continuous_iff (quotient_ring.quotient_map_coe_coe N)).2 cont }

end topological_ring

namespace uniform_space

lemma ring_sep_rel (α) [comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] :
  separation_setoid α = quotient_ring.quotient_rel (closure $ is_ideal.trivial α) :=
setoid.ext $ assume x y, group_separation_rel x y

lemma ring_sep_quot (α) [r : comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] :
  quotient (separation_setoid α) = quotient_ring.quotient (closure $ is_ideal.trivial α) :=
by rw [@ring_sep_rel α r]; refl

def sep_quot_equiv_ring_quot (α)
  [r : comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] :
  quotient (separation_setoid α) ≃ quotient_ring.quotient (closure $ is_ideal.trivial α) :=
quotient.congr $ assume x y, group_separation_rel x y

/- TODO: use a form of transport a.k.a. lift definition a.k.a. transfer -/
instance [comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] :
  comm_ring (quotient (separation_setoid α)) :=
by rw ring_sep_quot α; apply_instance

instance [comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] :
  topological_ring (quotient (separation_setoid α)) :=
begin
  convert topological_ring_quotient (closure (is_ideal.trivial α)),
  { apply ring_sep_rel },
  { dsimp [topological_ring_quotient_topology, quotient.topological_space, to_topological_space],
    congr,
    apply ring_sep_rel,
    apply ring_sep_rel },
  { apply ring_sep_rel },
  { simp [uniform_space.comm_ring] },
end

end uniform_space
