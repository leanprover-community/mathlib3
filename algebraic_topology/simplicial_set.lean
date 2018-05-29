import order.basic .simplex_category data.finset data.finsupp algebra.group

local notation ` [`n`] ` := fin (n+1)

/-- Simplicial set -/
class simplicial_set :=
(objs : Π n : ℕ, Type*)
(maps {m n : ℕ} {f : [m] → [n]} (hf : monotone f) : objs n → objs m)
(id {n : ℕ} : (maps (@monotone_id [n] _)) = id)
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
⟨λ f g,
begin
  apply finsupp.sum_add_index; finish [finset.sum_add_distrib, finset.sum_congr rfl, single_add, smul_add]
end⟩

lemma C_is_a_complex (γ : C A X (n+2)) : (boundary A X n) ((boundary A X (n+1)) γ) = 0 :=
begin
  apply finsupp.induction γ,
  { apply is_add_group_hom.zero },
  { intros x a f xni ane h,
    rw [is_add_group_hom.add (boundary A X (n + 1)), is_add_group_hom.add (boundary A X n), h, add_zero],
    unfold boundary,
    rw finsupp.sum_single_index,
    { rw ←finsupp.sum_finset_sum_index,
      { rw show sum univ (λ (i : [n+1+1]), sum (single (δ i x) ((-1 : ℤ) ^ i.val • a)) (λ (y : objs (n + 1)) (b : A), sum univ (λ (i : [n+1]), single (δ i y) ((-1 : ℤ)^i.val • b)))) =
                    sum univ (λ (i : [n+1+1]), (λ (y : objs (n + 1)) (b : A), sum univ (λ (i : [n+1]), single (δ i y) ((-1 : ℤ)^i.val • b))) (δ i x) ((-1 : ℤ)^i.val • a)),
        by finish [finset.sum_congr rfl, finsupp.sum_single_index],
        rw show sum univ (λ (j : [n+1+1]), sum univ (λ (i : [n+1]),
                      single (δ i (δ j x)) ((-1 : ℤ) ^ i.val • ((-1 : ℤ) ^ j.val • a)))) =
                    sum univ (λ (j : [n+1+1]), sum univ (λ (i : [n+1]),
                      single (((δ i) ∘ (δ j)) x) ((-1 : ℤ) ^ i.val • ((-1 : ℤ) ^ j.val • a)))), by unfold function.comp,
        rw [←@finset.sum_product _ _ _ _ _ _ (λ (p : [n+1+1] × [n+1]), single ((δ p.snd ∘ δ p.fst) x) ((-1 : ℤ)^p.snd.val • ((-1 : ℤ)^p.fst.val • a))),
            ←@finset.sum_sdiff ([n+1+1] × [n+1]) _ (univ.filter (λ p : [n+1+1] × [n+1], p.fst.val ≤ p.snd.val))],
        { rw [←eq_neg_iff_add_eq_zero, ←finset.sum_neg_distrib],
          apply eq.symm,
          apply @finset.sum_bij ([n+1+1] × [n+1]) _ ([n+1+1] × [n+1]) _ (univ.filter (λ p : [n+1+1] × [n+1], p.fst.val ≤ p.snd.val)) _ _ _
          (λ (p : [n+1+1] × [n+1]) hp, (p.snd.succ, ⟨p.fst.val,lt_of_le_of_lt (mem_filter.mp hp).2 p.snd.is_lt⟩)),
          { intros p hp,
            simp,
            apply nat.succ_le_succ,
            exact (mem_filter.mp hp).2 },
          { intros p hp,
            simp [fin.succ],
            let j := p.fst,
            let i := p.snd,
            show -single (δ i (δ j x)) ((-1:ℤ)^i.val • ((-1:ℤ)^j.val • a)) =
                  single (δ ⟨j.val, _⟩ (δ i.succ x))((-1:ℤ)^j.val • ((-1:ℤ)^nat.succ (i.val) • a)),
            rw show -single (δ i (δ j x)) ((-1:ℤ)^i.val • (-1:ℤ)^j.val • a) =
                        single (δ i (δ j x)) (-((-1:ℤ)^i.val • (-1:ℤ)^j.val • a)),
            begin
            apply finsupp.ext,
            intro γ,
            simp [single_apply],
            split_ifs; simp
            end,
            apply finsupp.ext,
            intro γ,
            rw show (δ ⟨j.val, _⟩ (δ (fin.succ i) x)) = (δ i (δ j x)),
            begin
              show ((δ ⟨j.val, _⟩) ∘ (δ (fin.succ i))) x = ((δ i) ∘ (δ j)) x,
              rw simplicial_identity₁, -- this is where it happens!!
              { suffices foo : (fin.raise ⟨j.val, lt_of_le_of_lt (mem_filter.mp hp).2 i.is_lt⟩) = j,
                { rw foo },
                { apply fin.eq_of_veq,
                  finish }},
              { exact (mem_filter.mp hp).2 }
            end,
            simp [single_apply],
            split_ifs;
            simp [pow_succ, eq.symm mul_smul, eq_neg_iff_add_eq_zero, add_smul, mul_comm] },
          { intros p q hp hq,
            simp,
            intros h2 h1,
            apply prod.ext.mpr,
            split,
            { apply fin.eq_of_veq,
              apply fin.veq_of_eq h1 },
            { exact fin.succ.inj h2 }},
          { intros p hp,
            simp at *,
            existsi p.snd.raise,
            existsi (⟨p.fst.val.pred, begin
              induction H : p.fst.val with i,
              { simp [nat.zero_lt_succ] },
              { change i.succ ≤ n+2,
                simp [eq.symm H, nat.le_of_succ_le_succ p.fst.is_lt] }
            end⟩ : [n+1]),
            existsi _,
            { apply prod.ext.mpr,
              split; simp [fin.succ,fin.raise];
                apply fin.eq_of_veq;
                simp [nat.succ_pred_eq_of_pos (lt_of_le_of_lt (nat.zero_le p.snd.val) hp)] },
            { simp,
              exact (nat.pred_succ (p.fst).val ▸ nat.pred_le_pred hp) } } },
        { apply filter_subset }},
      { finish },
      { finish [finset.sum_add_distrib, finset.sum_congr rfl, single_add, smul_add] } },
    { finish }}
end

end simplicial_complex