import order.basic .simplex_category data.finset data.finsupp algebra.group

local notation ` [`n`] ` := fin (n+1)

/-- Simplicial set -/
class simplicial_set :=
(objs : Π n : ℕ, Type*)
(maps {m n : ℕ} {f : [m] → [n]} (hf : monotone f) : objs n → objs m)
(comp {l m n : ℕ} {f : [l] → [m]} {g : [m] → [n]} (hf : monotone f) (hg : monotone g) :
  (maps hf) ∘ (maps hg) = (maps (monotone_comp hf hg)))

namespace simplicial_set

/-- The i-th face map of a simplicial set -/
def δ {X : simplicial_set} {n : ℕ} (i : [n+1]) :=
maps (simplex_category.δ_monotone i)

lemma simplicial_identity₁ {X : simplicial_set} {n : ℕ} {i j : [n + 1]} (H : i ≤ j) :
(@δ X n) i ∘ δ j.succ = δ j ∘ δ i.raise := by finish [δ, comp, simplex_category.simplicial_identity₁]

end simplicial_set

namespace simplicial_complex
noncomputable theory
local attribute [instance] classical.prop_decidable
open finset finsupp simplicial_set group

variables (A : Type*) [module ℤ A] (X : simplicial_set) (n : ℕ)
-- We actually want to be more general:
-- variables {R : Type*} [ring R] (A : Type*) [module R A] (X : simplicial_set) (n : ℕ)
-- However, to make this work we need to do some work on modules:
-- - finsupp.to_module needs to be generalised (as suggested in a comment above it)
-- - is_linear_map should be a class so that we can have type class inference

/-- The simplicial complex associated with a simplicial set -/
def C := (@objs X n) →₀ A

instance : add_comm_group (C A X n) := finsupp.add_comm_group

/-- The boundary morphism of the simplicial complex -/
definition boundary : C A X (n+1) → C A X n :=
λ f, f.sum (λ x a,
  (sum univ (λ i : [n+1], finsupp.single ((δ i) x) (((-1 : ℤ)^i.val) • a))))

instance: is_add_group_hom (boundary A X n) :=
⟨λ f g, begin
apply finsupp.sum_add_index,
{ intro x, simp, refl },
{ intros x k₁ k₂,
  rw ←finset.sum_add_distrib,
  apply finset.sum_congr,
  refl,
  intros i hi,
  rw ←single_add,
  congr,
  apply smul_add }
end⟩

lemma C_is_a_complex (γ : C A X (n+2)) : (boundary A X n) ((boundary A X (n+1)) γ) = 0 :=
begin
apply finsupp.induction γ,
{ apply is_add_group_hom.zero },
{ intros x a f xni ane h,
  rw is_add_group_hom.add (boundary A X (n + 1)),
  rw is_add_group_hom.add (boundary A X n),
  rw h,
  rw add_zero,
  unfold boundary,
  rw finsupp.sum_single_index,
  { let hom := (λ (y : objs (n + 1)) (b : A), sum univ (λ (i : [n+1]), single (δ i y) ((-1 : ℤ)^i.val • b))),
    show sum (sum univ (λ (i : [n+1+1]), single (δ i x) ((-1 : ℤ)^i.val • a))) hom = 0,
    rw ←finsupp.sum_finset_sum_index,
    { have triv : sum univ (λ (i : [n+1+1]), sum (single (δ i x) ((-1 : ℤ) ^ i.val • a)) hom) =
                  sum univ (λ (i : [n+1+1]), hom (δ i x) ((-1 : ℤ)^i.val • a)) :=
      begin
        apply finset.sum_congr,
        refl,
        intros j hj,
        apply finsupp.sum_single_index,
        dsimp [hom],
        simp
      end,
      rw triv,
      clear triv,
      dsimp [hom],
      clear hom,
      have triv : sum univ (λ (j : [n+1+1]), sum univ (λ (i : [n+1]),
                    single (δ i (δ j x)) ((-1 : ℤ) ^ i.val • ((-1 : ℤ) ^ j.val • a)))) =
                  sum univ (λ (j : [n+1+1]), sum univ (λ (i : [n+1]),
                    single (((δ i) ∘ (δ j)) x) ((-1 : ℤ) ^ i.val • ((-1 : ℤ) ^ j.val • a)))) :=
      by unfold function.comp,
      rw triv,
      clear triv,
      let temp := λ (p : [n+1+1] × [n+1]), single ((δ p.snd ∘ δ p.fst) x) ((-1 : ℤ)^p.snd.val • ((-1 : ℤ)^p.fst.val • a)),
      rw ←@finset.sum_product _ _ _ _ _ _ temp,
      rw ←@finset.sum_sdiff ([n+1+1] × [n+1]) _ (univ.filter (λ p : [n+1+1] × [n+1], p.fst.val ≤ p.snd.val)),
      { rw ←eq_neg_iff_add_eq_zero,
        simp at *,
        rw ←finset.sum_neg_distrib,
        apply eq.symm,
        apply @finset.sum_bij ([n+1+1] × [n+1]) _ ([n+1+1] × [n+1]) _ (univ.filter (λ p : [n+1+1] × [n+1], p.fst.val ≤ p.snd.val)) _ _ _
        (λ (p : [n+1+1] × [n+1]) hp, (p.snd.succ, ⟨p.fst.val,lt_of_le_of_lt (mem_filter.mp hp).2 p.snd.is_lt⟩)),
        { intros p hp,
          simp,
          replace hp := (mem_filter.mp hp).2,
          apply nat.succ_le_succ,
          exact hp },
        { intros p hp,
          simp,
          dsimp [temp],
          simp [fin.succ],
          let j := p.fst,
          let i := p.snd,
          show -single (δ i (δ j x)) ((-1 : ℤ)^i.val • ((-1 : ℤ)^j.val • a)) =
                single (δ ⟨j.val, _⟩ (δ i.succ x))((-1 : ℤ)^j.val • ((-1 : ℤ)^nat.succ (i.val) • a)),
          have triv : -single (δ i (δ j x)) ((-1:ℤ)^i.val • (-1:ℤ)^j.val • a) =
                       single (δ i (δ j x)) (-((-1:ℤ)^i.val • (-1:ℤ)^j.val • a)) :=
          begin
          apply finsupp.ext,
          intro γ,
          simp,
          rw single_apply,
          rw single_apply,
          by_cases H : (δ i (δ j x) = γ),
          { rw [if_pos H],
            rw [if_pos H] },
          { rw [if_neg H],
            rw [if_neg H],
            simp }
          end,
          rw triv,
          clear triv,
          apply finsupp.ext,
          intro γ,
          have you_know_this_lean : j.val < n + 1 + 1 := -- by schoolkid
          begin
            apply lt_of_le_of_lt (mem_filter.mp hp).2 i.is_lt,
          end,
          have helpme : (δ ⟨j.val, you_know_this_lean⟩ (δ (fin.succ i) x)) = (δ i (δ j x)) :=
          begin
            show ((δ ⟨j.val, you_know_this_lean⟩) ∘ (δ (fin.succ i))) x = ((δ i) ∘ (δ j)) x,
            rw simplicial_identity₁,
            { suffices foo : (fin.raise ⟨j.val, you_know_this_lean⟩) = j,
              { rw foo },
              { unfold fin.raise,
                apply fin.eq_of_veq,
                simp }},
            { show j.val ≤ i.val,
              exact (mem_filter.mp hp).2 }
          end,
          rw helpme,
          rw single_apply,
          rw single_apply,
          by_cases H : (δ i (δ j x) = γ),
          { rw [if_pos H],
            rw [if_pos H],
            rw pow_succ,
            rw ←mul_smul,
            rw ←mul_smul,
            apply eq.symm,
            rw eq_neg_iff_add_eq_zero,
            rw ←add_smul,
            rw mul_comm,
            simp },
          { rw [if_neg H],
            rw [if_neg H] }},
        { intros p q hp hq,
          simp,
          intros h2 h1,
          apply prod.ext.mpr,
          split,
          { apply fin.eq_of_veq,
            dsimp at *,
            apply fin.veq_of_eq h1 },
          { exact fin.succ.inj h2 }},
        { intros p hp,
          simp at *,
          existsi p.snd.raise,
          let helpme : [n+1] := ⟨p.fst.val.pred,begin
            induction H : p.fst.val with i,
            simp,
            apply nat.zero_lt_succ,
            rw nat.pred_succ,
            show i.succ ≤ n+2,
            rw ←H,
            apply nat.le_of_succ_le_succ p.fst.is_lt
          end⟩,
          existsi helpme,
          dsimp [helpme],
          clear helpme,
          existsi _,
          { apply prod.ext.mpr,
            split; simp [fin.succ,fin.raise],
            { apply fin.eq_of_veq,
              simp,
              apply eq.symm,
              apply nat.succ_pred_eq_of_pos,
              show 0 < p.fst.val,
              apply lt_of_le_of_lt (nat.zero_le p.snd.val) hp},
            apply fin.eq_of_veq,
            simp },
          { simp at *,
            unfold fin.raise,
            simp,
            replace hp := nat.pred_le_pred hp,
            rw nat.pred_succ at hp,
            exact hp },
          }},
      { apply filter_subset }},
    { intro y,
      dsimp [hom],
      simp },
    { intros y k₁ k₂,
      dsimp [hom],
      rw ←finset.sum_add_distrib,
      apply finset.sum_congr,
      refl,
      intros i hi,
      rw ←single_add,
      congr,
      apply smul_add }},
  { rw ←@finset.sum_const_zero (fin (n+1+1+1)) (C _ X _) univ _,
    apply finset.sum_congr,
    refl,
    intros i hi,
    simp,
    refl }}
end

end simplicial_complex