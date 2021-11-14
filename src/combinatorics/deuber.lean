import combinatorics.hales_jewett
import group_theory.submonoid
import combinatorics.pigeonhole
import data.fintype.sort
import data.finsupp
import data.matrix.basic

open_locale big_operators classical matrix
noncomputable theory

def order_emb_of_card_le {α β} [fintype α] [linear_order α] [fintype β] [linear_order β]
  (h : fintype.card α ≤ fintype.card β) : α ↪o β :=
(mono_equiv_of_fin α rfl).symm.to_rel_embedding.trans
    ((fin.cast_le h).trans $ mono_equiv_of_fin β rfl)

def ends_at_with {α β} [has_zero β] [linear_order α] (f : α → β) (i : α) (x : β) : Prop :=
  f i = x ∧ ∀ j, i < j → f j = 0

variables {R : Type} [semiring R] (A : submonoid R)

structure MPC :=
(m : Type)
(fintype : fintype m)
(linear_order : linear_order m)
(p : set R)
(p_finite : p.finite)
(zero_mem : (0 : R) ∈ p)
(C : A)
(C_mem : (C : R) ∈ p)

variable {A}

attribute [instance] MPC.fintype MPC.linear_order

instance : inhabited (MPC A) :=
⟨⟨fin 0, infer_instance, infer_instance, {0, 1}, set.finite.insert 0 (set.finite_pure 1),
  set.mem_insert 0 {1}, 1, set.mem_insert_of_mem 0 rfl⟩⟩

variables (S : MPC A)

section

variable (T : MPC A)

structure MPC.inclusion : Type :=
(to_fun : S.m ↪o T.m)
(mat : matrix S.m T.m R)
(scale : R)
(scale_C : (S.C : R) * scale = T.C)
(ends : ∀ i, ends_at_with (mat i) (to_fun i) scale)
(foo : T.m → option S.m)
(disj : ∀ i j, foo j ≠ some i → mat i j = 0)
(mem : ∀ i j (r ∈ S.p), r * mat i j ∈ T.p)

structure MPC.row (o : option S.m) :=
(d : S.m → R)
(d_mem : ∀ i, d i ∈ S.p)
(good : ∀ i ∈ o, ends_at_with d i S.C)

variables {S T}

def MPC.inclusion.comp {R : MPC A} (f : S.inclusion T) (g : T.inclusion R) : S.inclusion R :=
{ to_fun := f.to_fun.trans g.to_fun,
  mat := f.mat ⬝ g.mat,
  scale := f.scale * g.scale,
  scale_C := by rw [←mul_assoc, f.scale_C, g.scale_C],
  ends :=
    begin
      intro i,

    end,
  foo := _,
  disj := _,
  mem := _ }

def MPC.inclusion.map_row (inc : S.inclusion T) (o : option S.m) (v : S.row o) :
  T.row (o.map inc.to_fun) :=
{ d := λ j, ∑ i : S.m, v.d i * inc.mat i j,
  d_mem :=
    begin
      intro j,
      set i := inc.foo j with hi,
      clear_value i,
      cases i,
      { convert T.zero_mem,
        apply finset.sum_eq_zero,
        intros i junk,
        rw [inc.disj, mul_zero],
        rw ←hi, rintro ⟨⟩, },
      { rw finset.sum_eq_single_of_mem i (finset.mem_univ i),
        { apply inc.mem, apply v.d_mem, },
        { intros i' junk ine,
          rw [inc.disj, mul_zero],
          rw ←hi, apply (option.some_injective _).ne, exact ine.symm, }, },
    end,
  good :=
    begin
      cases o with i,
      { simp only [forall_false_left, implies_true_iff, option.map_none', option.not_mem_none], },
      { simp only [option.map_some', option.mem_def, forall_eq'],
        split,
        { convert inc.scale_C,
          dsimp only,
          rw [finset.sum_eq_single_of_mem i (finset.mem_univ i), (v.good _ rfl).1, (inc.ends i).1],
          { intros i' junk ine,
            cases lt_or_gt_of_ne ine,
            { rw [(inc.ends i').2, mul_zero], rw order_embedding.lt_iff_lt, assumption, },
            { rw [(v.good _ rfl).2, zero_mul], assumption, }, } },
        { intros j hj, apply finset.sum_eq_zero, intros i' junk, cases le_or_gt i' i,
          { rw [(inc.ends i').2, mul_zero], refine lt_of_le_of_lt _ hj,
            rw [order_embedding.le_iff_le], assumption, },
          { rw [(v.good _ rfl).2, zero_mul], assumption, }, }, },
    end }

variables (S T) (κ : Type)

def MPC.coloring : Type := Π i : S.m, S.row (some i) → κ

variables {S T κ}

def MPC.coloring.restrict (co : T.coloring κ) (inc : S.inclusion T) : S.coloring κ :=
λ i v, co _ (inc.map_row _ v)

def MPC.coloring.row_mono (co : S.coloring κ) (i : S.m) (k : κ) : Prop := ∀ v, co i v = k
def MPC.coloring.mono (co : S.coloring κ) (k : κ) : Prop := ∀ i, co.row_mono i k

theorem deuber [fintype κ] : ∃ T : MPC A, ∀ co : T.coloring κ,
  ∃ (inc : S.inclusion T) (k : κ), (co.restrict inc).mono k :=
begin
  suffices : ∀ r : ℕ, ∃ (R T : MPC A) (hcard : fintype.card R.m = r) (hp : R.p = S.p)
    (hC : R.C = S.C), ∀ co : T.coloring κ, ∃ (inc : R.inclusion T) (k : R.m → κ),
      ∀ i, (co.restrict inc).row_mono i (k i),
  { specialize this (fintype.card κ * fintype.card S.m),
    obtain ⟨R, T, hcard, hp, hC, hR⟩ := this,
    refine ⟨T, forall_imp _ hR⟩,
    rintros co ⟨inc, k, h⟩,
  }
end
