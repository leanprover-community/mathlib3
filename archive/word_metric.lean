import analysis.normed.group.basic
import group_theory.free_group

/-! normed groups.
-/


noncomputable theory
open set function real

namespace word_metric

section marked_group

--  an S-generated group
class marked_group (G : Type*) (S : out_param Type*) [group G] :=
(marking : free_group S →* G)
(is_surjective : function.surjective marking)

variables {S : Type*} [decidable_eq S]

def free_group_norm (f : free_group S) : ℕ := (free_group.to_word f).length

variables {MG : Type*} [group MG] [marked_group MG S]

def group_norm [decidable_eq S] (g : MG) : ℕ := nat.lt.is_well_order.wf.min
  (free_group_norm '' {x | marked_group.marking x = g})
  (by { apply set.nonempty.image, exact marked_group.is_surjective g })

lemma group_norm_one [decidable_eq S] (x : MG) : group_norm x = 0 ↔ x = 1 := begin
  split,
  { intro h, sorry -- the only free group element with length 0 is identity
  },
  { intro h, rw h, sorry -- the identity has length 0
  },
end

lemma group_norm_comm [decidable_eq S] (x : MG) : group_norm x = group_norm x⁻¹ := begin
  -- extract a rep of minimum for x, use inverse for x⁻¹
  sorry
end

lemma group_norm_ineq [decidable_eq S] (x y : MG) : group_norm (x*y) ≤ group_norm x + group_norm y := begin
  -- extract reps for x, y, use product for x*y
  sorry
end

end marked_group

end word_metric

--end marked_group

--section normed_group

variables [marked_group G S]

"""a group with a norm and associated left-invariant metric"""
class normed_group extends group G, has_norm G, metric_space G :=
(dist_eq : ∀ x y : G, dist x y = ∥x⁻¹*y∥)

lemma test (x y z : ℕ) : x + y ≤ z → (x : ℝ) + (y : ℝ) ≤ (z : ℝ) :=
begin
  sorry
end

instance whatever : normed_group := { norm := λ g, (group_norm g : ℝ),
  dist := λ x y : G, group_norm (x⁻¹*y),
  dist_eq := begin
    intros x y, norm_num,
  end,
  dist_self := begin
    intro x, norm_num, rw group_norm_one (1 : G),
  end,
  dist_comm := begin
    intros x y, norm_num, rw group_norm_comm (x⁻¹*y), norm_num,
  end,
  dist_triangle := begin
    intros x y z, norm_num,
    let c := group_norm_ineq (x⁻¹*y) (y⁻¹*z),
    rw [mul_assoc,mul_inv_cancel_left] at c,
    sorry, -- almost there! must take care of coercions to real
  end,
  eq_of_dist_eq_zero := begin
    intros x y, norm_num, rw group_norm_one (x⁻¹*y), exact inv_mul_eq_one.mp
  end
}

end marked_group

section independence

lemma independence_of_generating_set [group G] [marked_group G S] [marked_group {S₁ S₂} (GS₁ : norm_generated_group G S₁) (GS₂ : norm_generated_group G S₂) : ∃ K, lipschitz_with K ((λ (g : GS₁), (g : GS₂)) : (normed_group G) → (normed_group G)) := sorry


end independence

end word_metric

namespace group_growth

--variables {G : Type*} [normed_group G]

def ball0 (r : ℕ) (G : Type*) [normed_group G] : set G := { x | ∥x∥ ≤ r }

--!! error here if I don't put the (G:Type) explicitly
lemma finite_balls (G : Type*) [normed_group.norm_generated_group G] : ∀ r, set.finite (ball0 r G) := begin
    have x : G.Spos,
    sorry
end

def ball (G : Type*) [norm_generated_group G] (r : ℕ) : finset G := (finite_balls G r).to_finset


def growth (G : Type*) [norm_generated_group G] : ℕ → ℕ := λ r, (ball G r).card

def dominates (a : ℕ → ℕ) (b : ℕ → ℕ) : Prop := ∃K, ∀(r ≥ 0), a(r) ≤ b(K*r)

--!! notation infix:`≾` for dominates, `∼` for equivalent
def equivalent (a : ℕ → ℕ) (b : ℕ → ℕ) : Prop := (dominates a b) ∧ (dominates b a)

/-
define growth types: exponential, polynomial, intermediate

then lots of basic lemmas: growth of subgroup is smaller than growth of group; if finite-index subgroup then the growth relate by at most the index; etc.
-/
end group_growth

