import linear_algebra.basic
import data.nat.basic
import tactic.apply
import tactic.omega
import ring_theory.noetherian
import ring_theory.adjoin
import data.matrix.basic

namespace dedekind_finite

section

variables (R : Type*)

class dedekind_finite extends ring R :=
( inv_comm : ∀ a b : R, a * b = 1 → b * a = 1 )

@[priority 100]
instance dedekind_finite_of_comm_ring [comm_ring R] : dedekind_finite R :=
⟨λ a b h, h ▸ mul_comm b a⟩

end
section
universes u v w
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equiped with instances
variables (x y : Π i, f i) (i : I)
instance pi.dedekind_finite [∀ i, dedekind_finite $ f i] : dedekind_finite (Π i : I, f i) := by pi_instance

end
section
universe u
variables (R : Type u)
/-  TODO
instance asubset.ring {S : set R} [is_subring S] : ring S :=
by apply_instance
instance asubtype.ring {S : set R} [is_subring S] : ring (subtype S) := subset.ring

instance subring.dedekind_finite [dedekind_finite R] (S : set R) [is_subring S] : dedekind_finite S :=
by subtype_instance
 -/
def is_nilpotent {R : Type*} [ring R] (a : R) := ∃ n : ℕ, a^n = 0
def nilpotents [ring R] := { a : R | is_nilpotent a }

class reduced extends ring R :=
(no_nilpotents : ∀ a : R, ∀ n : ℕ, a^n = 0 → a = 0)

lemma zero_nilpotent [ring R] : is_nilpotent (0 : R) := ⟨1, pow_one 0⟩
lemma zero_in_nilpotents [ring R] : (0 : R) ∈ nilpotents R := zero_nilpotent R

lemma nilpotents_of_reduced [reduced R] : nilpotents R = {0} :=
begin
apply' set.eq_of_subset_of_subset,
{
    rintros x ⟨n, hn⟩,
    rw set.mem_singleton_iff,
    exact reduced.no_nilpotents x n hn,
},
{
    rw set.singleton_subset_iff,
    exact zero_in_nilpotents R,
}
end

class reversible extends ring R :=
(zero_div_comm : ∀ a b : R, a * b = 0 → b * a = 0)

@[priority 100]
instance reversible_of_domain [domain R] : reversible R :=
⟨ λ a b h,
begin
    cases domain.eq_zero_or_eq_zero_of_mul_eq_zero a b h,
    { rw h_1, rw [mul_zero], },
    { rw h_1, rw [zero_mul], },
end⟩

@[priority 100]
instance reversible_of_reduced [reduced R] : reversible R :=
⟨ λ a b h,
begin
    apply reduced.no_nilpotents (b * a) 2,
    rw [pow_two, ← mul_assoc, mul_assoc b, h, mul_zero, zero_mul],
end⟩
@[priority 100]
instance reversible_of_comm_ring [comm_ring R] : reversible R :=
⟨ λ a b h, h ▸ mul_comm b a⟩

@[priority 100]
instance dedekind_finite_of_reversible [reversible R] : dedekind_finite R :=
⟨ λ a b h,
begin
    have :=
    calc (b * a - 1) * b = b * (a * b) - b : by rw [sub_mul, one_mul, mul_assoc]
                    ...  = 0               : by rw [h, mul_one, sub_self],
    have : b * (b * a - 1) = 0 := reversible.zero_div_comm _ _ this,
    rw [mul_sub, mul_one, ← mul_assoc, ← pow_two, sub_eq_zero] at this,
    have abba_eq_one := congr_arg ((*) a) this,
    rw [h] at abba_eq_one,
    calc b * a = (a * (b^2 * a)) * b * a : by simp [abba_eq_one]
        ...    = (a * b^2) * (a * b) * a : by simp [mul_assoc] -- I feel like ac_refl should do this
        ...    = (a * b^2 * a)           : by simp [h]
        ...    = 1                       : by assoc_rw [abba_eq_one],
end⟩

@[priority 100]
instance dedekind_finite_of_reduced [reduced R] : dedekind_finite R := by apply_instance


variable [ring R]

open linear_map
open_locale classical


example (G : Type*) [monoid G] : G := 1 * 1

@[priority 100]
instance dedekind_finite_of_noetherian [is_noetherian_ring R] : dedekind_finite R :=
⟨ λ a b h,
begin
    have : is_linear_map R _ := is_linear_map.is_linear_map_smul' b,
    set f : R →ₗ[R] R := is_linear_map.mk' _ this,
    have f_surj : function.surjective f := λ x, ⟨x * a, by simp [mul_assoc, h]⟩,
    have := well_founded_submodule_gt R R,
    rw order_embedding.well_founded_iff_no_descending_seq at this,
    set ordf : ℕ → submodule R R := λ n, linear_map.ker (iterate f n),

    suffices : ∃ n, ordf n = ordf (n + 1),
    begin
        obtain ⟨n, hn⟩ := this,
        have pow_surj := iterate_surjective f f_surj n,
        obtain ⟨c, hc⟩ := pow_surj (b * a - 1),
        have :=
        calc iterate f (n + 1) c = f (b * a - 1)   : by rw [iterate, linear_map.comp_apply, hc]
                            ...  = (b * a - 1) * b : by simp [f]
                            ...  = 0               : by rw [sub_mul, one_mul, mul_assoc, h, mul_one, sub_self],
        rw ← linear_map.mem_ker at this,
        dsimp only [ordf] at hn,
        rw ← hn at this,
        rw linear_map.mem_ker at this,
        rw this at hc,
        exact sub_eq_zero.mp (eq.symm hc),
    end,

    by_contradiction ho,
    apply this,
    push_neg at ho,
    have : ∀ n, ordf n ≤ ordf (n + 1) := λ n x hx, begin simp [ordf, iterate] at hx ⊢, rw [hx, zero_mul], end,
    have : ∀ n, ordf (n + 1) > ordf n := λ n, lt_of_le_of_ne (this n) (ho n),
    have := order_embedding.nat_gt _ this,
    exact nonempty.intro this,
end⟩

example (G : Type*) [monoid G] : G := 1 * 1


@[priority 100]
instance dedekind_finite_of_finite [fintype R] : dedekind_finite R := begin
    --TODO why is this needed?
    haveI : is_noetherian_ring R := ring.is_noetherian_of_fintype R R,
    exactI dedekind_finite.dedekind_finite_of_noetherian R,
end
end

section

private lemma aux1 {i j : ℕ} : j - i = j + 1 - (i + 1) := by omega

variable {R : Type*}

lemma mul_eq_one_pow_mul_pow_eq [ring R] {a b : R} (hab : a * b = 1) : ∀ (i j : ℕ), a^i * b^j = if i ≤ j then b^(j - i) else a^(i - j)
| 0       0       := by simp
| (i + 1) 0       := by simp only [mul_one, le_zero_iff_eq, nat.zero_sub,
                        add_eq_zero_iff, if_false, nat.sub_zero, one_ne_zero,
                        pow_zero, and_false]
| 0       (j + 1) := by simp only [one_mul, if_true, nat.zero_sub, zero_le,
                        nat.sub_zero, pow_zero]
| (i + 1) (j + 1) := begin
        rw pow_succ', rw pow_succ, assoc_rw hab,
        rw mul_one, rw mul_eq_one_pow_mul_pow_eq i j,
        apply' if_congr (iff.symm nat.lt_succ_iff),
        apply' congr_arg ((^) b),
        exact aux1,
        apply' congr_arg ((^) a),
        exact aux1,
    end

private lemma aux3 {j k : ℕ}
  (H : k < j) (hjk : ¬j = k + 1) : ¬j ≤ k + 1 :=
by omega


private lemma aux4 {j k l : ℕ}
  (H : k< j)  :
 j - (k + 1) + (l + 1) = j - k + l :=
 by omega

private lemma aux5 {j k l : ℕ}
  (H : k < j)  :
  j + 1 - (k + 1) + (l + 1) = j + 1 - k + l :=
 by omega

private def e (a b : R) [ring R] (i j : ℕ) : R := b^i * a^j - b^(i + 1) * a^(j + 1)

lemma e_orthogonal [ring R] {a b : R} (hab : a * b = 1) :
∀ {i j k l : ℕ},
(e a b i j) * (e a b k l) = if j = k then e a b i l else (0 : R) :=
begin
    intros,
    rw [e,e,e], rw [mul_sub, sub_mul, sub_mul], rw sub_right_comm,
    rw mul_assoc, rw mul_assoc, rw mul_assoc, rw mul_assoc,
    rw ← sub_add, rw ← mul_sub (b ^ i), rw ← sub_sub_assoc_swap,
    rw ← mul_sub (b ^ (i + 1)), rw ← mul_assoc, rw ← mul_assoc, rw ← mul_assoc,
    rw ← mul_assoc,
    rw mul_eq_one_pow_mul_pow_eq hab j k,
    rw mul_eq_one_pow_mul_pow_eq hab j (k + 1),
    rw mul_eq_one_pow_mul_pow_eq hab (j + 1) k,
    rw mul_eq_one_pow_mul_pow_eq hab (j + 1) (k + 1),
    rcases lt_trichotomy j k with H | rfl | H,
    {
        conv_rhs {rw if_neg (ne_of_lt H),},

        -- TODO omega gets stuck on instances
        rw if_pos (le_of_lt H),
        rw if_pos,
        rw if_pos,
        swap, exact H,
        rw if_pos,
        swap, exact le_add_right H,
        rw ← nat.succ_pred_eq_of_pos (nat.lt_sub_left_of_add_lt H : k - j > 0),
        rw ← nat.succ_pred_eq_of_pos (_ : k + 1 - j > 0),
        rw pow_succ, rw pow_succ, rw mul_assoc, rw mul_assoc,
        rw ← mul_sub b, rw ← mul_assoc, rw ← pow_succ',
        rw ← mul_sub (b ^ (i + 1)),
        convert mul_zero _,
        rw nat.pred_eq_sub_one, rw nat.pred_eq_sub_one,
        rw sub_sub_assoc_swap, rw (nat.succ_sub_succ k j : k + 1 - j - 1 = k - j),
        rw (_ : k + 1 - j - 1 = k - j),
        swap,
        exact nat.succ_sub_succ k j,
        rw nat.sub_sub, rw add_comm j 1,
        rw ← nat.sub_sub,
        abel,
        any_goals {linarith,},
        {apply nat.sub_pos_of_lt,
        transitivity k,
        exact H,
        exact lt_add_one k,},
    },
    {
        conv_rhs {rw if_pos,},

        rw if_pos (le_refl j), rw if_pos (nat.le_succ j),
        rw if_neg,
        swap,
        exact nat.lt_irrefl j,
        rw if_pos (le_refl (j + 1)),

        rw nat.sub_self, rw pow_zero, rw one_mul,
        rw (nat.sub_eq_of_eq_add rfl : j + 1 - j = 1),
        rw ← pow_add, rw pow_one, rw nat.sub_self, rw pow_zero,
        rw one_mul, rw add_comm,
        rw sub_self, rw mul_zero, rw sub_zero, rw mul_sub,
        rw ← mul_assoc, rw ← pow_succ',
    },
    {
        conv_rhs {rw if_neg (ne_of_gt H),},

        rw if_neg (not_le.mpr H),
        have : ite (j ≤ k + 1) (b ^ (k + 1 - j)) (a ^ (j - (k + 1))) = a ^ (j - (k + 1)) :=
        begin
            by_cases hjk : j = k + 1,
            {
                rw if_pos (le_of_eq hjk), rw [← hjk],
                rw nat.sub_self, refl,
            },
            {
                rw if_neg, exact aux3 H hjk,
            }
        end,
        rw this, rw if_neg,
        swap,
        exact (nat.nat.lt_asymm H),
        rw if_neg,
        swap,
        exact nat.le_lt_antisymm H,
        rw ← pow_add, rw ← pow_add, rw ← pow_add, rw ← pow_add,
        rw (aux4 H : j - (k + 1) + (l + 1) = j - k + l),
        rw sub_self, rw mul_zero, rw zero_sub,
        rw (aux5 H : j + 1 - (k + 1) + (l + 1) = j + 1 - k + l),
        rw sub_self, rw mul_zero, rw neg_zero,
    }
end

lemma e_ne_pow_two [ring R] {a b : R} (hab : a * b = 1) {i j : ℕ} (hij : i ≠ j) : (e a b i j) ^ 2 = (0 : R) :=
begin
    rw [pow_two],
    rw e_orthogonal hab,
    rw if_neg (ne.symm hij),
end

open_locale classical

@[priority 100]
instance dedekind_finite_of_fin_nilpotents (R : Type*) [ring R] (h : (nilpotents R).finite) : dedekind_finite R :=
⟨begin
    unfreezeI,
    contrapose! h,
    rcases h with ⟨a, b, hab, hba⟩,
    haveI : infinite (nilpotents R) :=
    begin
        let e1 : ℕ → nilpotents R := (λ n, ⟨e a b 0 (n + 1), 2, e_ne_pow_two hab (ne.symm (nat.succ_ne_zero n)) ⟩),
        refine infinite.of_injective e1 _,
        intros n m hnm,
        by_contradiction,
        simp [e1] at hnm,
        have :=
        calc 1 - b * a = e a b 0 0                         : by simp [e]
                  ...  = e a b 0 (n + 1) * e a b (n + 1) 0 : by rw [e_orthogonal hab, if_pos (rfl)]
                  ...  = e a b 0 (m + 1) * e a b (n + 1) 0 : by rw hnm
                  ...  = 0                                 : by rw [e_orthogonal hab, if_neg]; intro; exact a_1 ((add_right_inj 1).mp (eq.symm a_2)),
        rw sub_eq_zero at this,
        exact absurd (eq.symm this) hba,
    end,

    intro hinf,
    exact infinite.not_fintype (set.finite.fintype hinf),
end⟩

end
#lint

end dedekind_finite
