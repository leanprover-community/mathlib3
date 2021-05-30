/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import algebra.group_action_hom
import data.fin_simplicial_complex

/-!
# Group cohomology

We describe an explicit model for the group cohomology groups `Hⁿ(G,M)`,
as certain homogeneous cocycles over coboundaries.

## TODO

Write down map from usual n-cocycles to group cohomology and prove
that it's surjective with kernel precisely the classical n-coboundaries
-/

namespace add_comm_group
-- a sensible add_comm_group constructor

universe uA

variables (A : Type uA) [has_add A] [has_zero A] [has_neg A]

class add_comm_group_aux  : Prop :=
(add_assoc : ∀ (a b c : A), (a + b) + c = a + (b + c))
(zero_add : ∀ (a : A), 0 + a = a)
(add_left_neg : ∀ (a : A), -a + a = 0)
(add_comm : ∀ (a b : A), a + b = b + a)

open add_comm_group_aux

instance foo [add_comm_group_aux A] : add_comm_group A :=
{ add := (+),
  zero := 0,
  neg := has_neg.neg,
  add_zero := λ a, (add_comm_group_aux.add_comm 0 a) ▸ (zero_add a),
  ..‹add_comm_group_aux A›}

end add_comm_group

namespace group_cohomology

universes uG uM uA

variables (G : Type uG) [group G] (M : Type uM) [add_comm_group M]
  [distrib_mul_action G M] (n : ℕ)

-- need the homogeneous cochains, cocycles and coboundaries
/-- `cochain G M n.succ` is homogeneous `n`-cochains, namely functions
$$c:G^{n+1}\to M$$ which are homogeneous in the sense that $$c(s(g_i)_i)=s\bub c((g_i)_i)$$.

-/
@[ext] structure cochain_succ :=
(to_fun : (fin n → G) → M)
(smul_apply' : ∀ (s : G) (g : fin n → G), s • to_fun g = to_fun (λ i, s * g i))

namespace cochain_succ

instance : has_coe_to_fun (cochain_succ G M n) :=
{ F := _,
  coe := to_fun }

@[simp] lemma seems_useful (c : (fin n → G) → M) (hc : ∀ (s : G) (g : fin n → G), s • c g = c (λ i, s * g i))
  (g : fin n → G) : (⟨c, hc⟩ : cochain_succ G M n) g = c g := rfl

@[simp] lemma also_seems_useful (c : cochain_succ G M n) (g : fin n → G) : c.to_fun g = c g := rfl

@[ext] theorem ext' (c₁ c₂ : cochain_succ G M n) (h : ∀ g : fin n → G, c₁ g = c₂ g) : c₁ = c₂ :=
ext c₁ c₂ (funext (λ (x : fin n → G), h x))

def zero : cochain_succ G M n :=
{ to_fun := 0,
  smul_apply' := λ s g, smul_zero s }

instance : has_zero (cochain_succ G M n) := ⟨zero G M n⟩

@[simp] lemma zero_apply (g : fin n → G) : (0 : cochain_succ G M n) g = 0 := rfl

variables {G M n}

@[simp] lemma smul_apply (c : cochain_succ G M n) (s : G) (g : fin n → G) : s • c g = c (λ i, s * g i) :=
c.smul_apply' s g

def neg (c₁ : cochain_succ G M n): cochain_succ G M n :=
{ to_fun := λ g, -c₁ g,
  smul_apply' := λ s g, by {rw ← smul_apply, apply smul_neg }, }

instance : has_neg (cochain_succ G M n) := ⟨neg⟩

@[simp] lemma neg_apply (c : cochain_succ G M n) (g : fin n → G) : (-c : cochain_succ G M n) g = -(c g) := rfl

def add (c₁ c₂ : cochain_succ G M n) : cochain_succ G M n :=
{ to_fun := λ g, c₁ g + c₂ g,
  smul_apply' := by {intros, simp * at *}, }

instance : has_add (cochain_succ G M n) := ⟨add⟩

@[simp] lemma add_apply (c₁ c₂ : cochain_succ G M n) (g : fin n → G) : (c₁ + c₂) g = c₁ g + c₂ g :=
rfl


--lemma gsmul_univ {A : Type uA} [add_group A] (F : ℤ → A → A) (F_zero : ∀ a, F 0 a = 0)
--  (F_succ : ∀ (n : ℕ) (a : A), F (n.succ : ℕ) a = a + F n a)
--  (F_neg : ∀ (n : ℕ) (a : A), F -[1+ n] a = -F (n.succ : ℕ) a) : F = gsmul := sorry

instance : add_comm_group.add_comm_group_aux (cochain_succ G M n) :=
{ add_assoc := by { intros, ext, simp [add_assoc] },
  zero_add := by {intros, ext, simp },
  add_left_neg := by { intros, ext, simp },
  add_comm := by {intros, ext, simp [add_comm] },
}

@[simp] lemma sub_apply (c₁ c₂ : cochain_succ G M n) (g : fin n → G) :
  (c₁ - c₂) g = c₁ g - c₂ g :=
begin
  simp [sub_eq_add_neg],
end

lemma pred_smul {A : Type uA} [add_group A] (a : A) (n : ℤ) :
  (n - 1) • a = n • a - a :=
int.induction_on n
  (by simp)
  (λ _ _, by simp [add_gsmul, one_gsmul])
  (λ _, by simp [sub_gsmul])

lemma smul_gsmul {G : Type uG} [group G] {M : Type uM} [add_comm_group M] [distrib_mul_action G M]
  (g : G) (n : ℤ) (m : M) : g • n • m = n • g • m :=
int.induction_on n
  ( by simp)
  ( λ i h, by { simp only [add_smul, smul_add, add_left_inj, one_gsmul, h] })
  ( λ i h, by { simp only [pred_smul, smul_sub, smul_neg, neg_inj, sub_left_inj, h] } )


@[simp] lemma int_smul_apply (c : cochain_succ G M n) (z : ℤ) (g : fin n → G) :
  (z • c) g = z • (c g) :=
begin
--  cases c with c hc,
  apply int.induction_on z,
  { simp },
  { intros i this,
    simpa [add_gsmul] },
  { intros i this,
    rw [pred_smul, pred_smul, sub_apply, this] },
end


def d {i j : ℕ} (hj : j = i + 1) : cochain_succ G M i →+ cochain_succ G M j :=
{ to_fun := λ c,
  { to_fun := λ g, (finset.range j).sum (λ p, (-1 : ℤ)^p • c $ λ t, g (fin.delta hj p t)),
    smul_apply' := λ s g, begin
      rw [finset.smul_sum],
      simp,
      congr,
      ext,
      rw ← c.smul_apply,
      generalize : (c : (fin i → G) → M) _ = C,
      simp [],
      rw smul_gsmul,
    end },
  map_zero' := begin ext, simp end,
  map_add' := λ x y, by {ext, simp [finset.sum_add_distrib]} }

lemma d_eval {i j : ℕ} (hj : j = i + 1) (c : cochain_succ G M i) (g : fin j → G) :
  d hj c g = (finset.range j).sum (λ p, (-1 : ℤ)^p • c $ λ t, g $ fin.delta hj p t) := rfl

theorem d_squared {i j k : ℕ} (hj : j = i + 1) (hk : k = j + 1) (c : cochain_succ G M i) :
  (d hk (d hj c)) = 0 :=
begin
  ext g, change _ = (0 : M),
  simp only [d_eval],
  -- how do I avoid `conv` if I want to apply `d_eval` again?
  conv begin
    congr,
    congr, skip,
    funext,
    rw int_smul_apply,
    rw d_eval,
  end,
  simp_rw finset.smul_sum,
  rw ← finset.sum_product',
  apply finset.sum_involution (λ (pq : ℕ × ℕ) (hpq),
    if pq.fst ≤ pq.2 then (pq.2.succ, pq.1) else (pq.2, pq.1.pred)),
  { intros,
    simp,
    split_ifs,
    { simp [fin.delta_comm_apply hj hk h, pow_succ, smul_smul, mul_comm ((-1 : ℤ) ^ a.fst)] },
    { -- kill the pred.
      cases a with p q,
      -- pred 0 can't happen
      cases p, { push_neg at h, cases h },
      -- rewrite now succeeds
      simp [nat.pred_succ, pow_succ],
      push_neg at h,
      have hqp : q ≤ p := nat.lt_succ_iff.mp h,
      have := fin.delta_comm_apply.symm hj hk hqp,
      simp_rw this,
      simp [smul_comm ((-1 : ℤ) ^ p)] } },
  { rintros ⟨p, q⟩ h _ hfalse,
    rw prod.ext_iff at hfalse,
    rcases hfalse with ⟨h1, h2⟩,
    dsimp at *,
    split_ifs at *,
    { subst h1,revert h_1,
      apply nat.not_succ_le_self },
    { exact h_1 (h1 ▸ le_refl _) } },
  { rintro ⟨p, q⟩ hpqrange,
    simp [nat.succ_eq_add_one],
    split_ifs,
      exfalso, linarith,
      refl,
      cases p, {exfalso, exact h (zero_le _)}, refl,
      exfalso, cases p, exact h (zero_le _), rw nat.pred_succ at h_1,
        rw nat.succ_eq_add_one at h,linarith },
  { rintros ⟨p, q⟩ hpqbounds,
    rw finset.mem_product at hpqbounds,
    rcases hpqbounds with ⟨hpk : p ∈ _, hqj : q ∈ _⟩,
    rw finset.mem_range at hpk hqj,
    simp,
    split_ifs,
    { rw nat.succ_eq_add_one,
      split; linarith },
    { push_neg at h,
      cases p, cases h,
      rw nat.pred_succ,
      rw nat.succ_eq_add_one at *,
      split; linarith } },
end

end cochain_succ

--def H (n : ℕ) (G : Type uG) [group G] (M : Type uM) [add_comm_group M]
--  [distrib_mul_action G M] := sorry

end group_cohomology
