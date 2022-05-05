/-
Author: Russell Emerine
Based on: https://courses.engr.illinois.edu/cs373/sp2013/Lectures/lec07.pdf
TODO: write comments and TODOs, organize, etc.
-/
import computability.regular_expressions
import computability.NFA

namespace fin

theorem cast_succ_ne_last {n i} : fin.cast_succ i ≠ fin.last n :=
begin
  cases i with i lt,
  unfold last,
  simp,
  exact ne_of_lt lt,
end

end fin

universes u v

structure GNFA (α : Type u) (n : ℕ) :=
  (step : option (fin n) → option (fin n) → regular_expression α)

variables {α : Type u} {σ : Type v} {n : ℕ}

namespace regular_expression

theorem mem_sum (x : list α) (rs : list (regular_expression α)) :
  (list.foldl (λ a b, a + b) 0 rs).matches x ↔ (∃ (r : regular_expression α), r ∈ rs ∧ r.matches x) :=
begin
  split,
  { rw ← rs.reverse_reverse,
    induction rs.reverse,
    case nil {
      assume hx,
      cases hx,      
    },
    case cons : r rs ih {
      assume hx,
      simp at *,
      cases hx,
      case inl {
        rcases ih hx with ⟨r, mem, matches⟩,
        exact ⟨r, or.inl mem, matches⟩,
      },
      case inr {
        exact ⟨r, or.inr rfl, hx⟩,
      },
    },
  },
  { rw ← rs.reverse_reverse,
    induction rs.reverse,
    case nil {
      assume hx,
      simp at hx,
      contradiction,
    },
    case cons : r rs ih {
      assume hx,
      simp at *,
      rcases hx with ⟨r', hr', matches⟩,
      cases hr',
      case inl {
        left,
        exact ih r' hr' matches,
      },
      case inr {
        right,
        rw hr' at matches,
        exact matches,
      },
    },
  },
end

end regular_expression

namespace GNFA

inductive trace (M : GNFA α n) : list α → fin n → Prop
| start : ∀ {x q}, x ∈ (M.step none (some q)).matches → trace x q
| step : ∀ {x y z} p {q}, trace y p → z ∈ (M.step (some p) (some q)).matches → x = y ++ z → trace x q

inductive accepts (M : GNFA α n) : language α
| start : ∀ {x}, x ∈ (M.step none none).matches → accepts x
| step : ∀ {x y z} q, M.trace y q → z ∈ (M.step (some q) none).matches → x = y ++ z → accepts x

end GNFA

namespace NFA

def convert (M : NFA α σ) {τ} (equiv : σ ≃ τ) : NFA α τ :=
⟨
  (λ p a q, M.step (equiv.inv_fun p) a (equiv.inv_fun q)),
  (λ q, M.start (equiv.inv_fun q)),
  (λ q, M.accept (equiv.inv_fun q))
⟩

theorem convert_correct (M : NFA α σ) {τ} (equiv : σ ≃ τ) : M.accepts = (M.convert equiv).accepts :=
begin
  ext,
  split,
  { rintros ⟨q, accept, eval⟩,
    refine ⟨equiv.to_fun q, _, _⟩,
    { unfold convert,
      rw set.mem_def at *,
      simpa,
    },
    { clear accept,
      revert eval,
      rw ← x.reverse_reverse,
      induction x.reverse generalizing q,
      case nil {
        assume hx,
        unfold convert,
        rw set.mem_def at *,
        simpa,
      },
      case cons : a as ih {
        assume hx,
        simp at *,
        rw NFA.mem_step_set at *,
        rcases hx with ⟨p, mem, step⟩,
        refine ⟨equiv.to_fun p, ih p mem, _⟩,
        unfold convert,
        rw set.mem_def at *,
        simpa,
      },
    },        
  },
  { rintros ⟨q, accept, eval⟩,
    refine ⟨equiv.inv_fun q, accept, _⟩,
    clear accept,
    revert eval,
    rw ← x.reverse_reverse,
    induction x.reverse generalizing q,
    case nil {
      assume hx,
      exact hx,
    },
    case cons : a as ih {
      assume hx,
      simp at *,
      rw NFA.mem_step_set at *,
      rcases hx with ⟨p, mem, step⟩,
      exact ⟨equiv.inv_fun p, ih p mem, step⟩,
    },
  },
end

variables
  (M : NFA α (fin n))
  [dec_start : decidable_pred M.start]
  [dec_accept : decidable_pred M.accept]
  [dec_step : ∀ p a q, decidable (M.step p a q)]
  (as : list α)
  (univ : ∀ a, a ∈ as)

include dec_start dec_accept dec_step univ

def to_GNFA : GNFA α n :=
⟨
  λ p q,
  match (p, q) with
  | (none, none) := 0
  | (none, some q) := if M.start q then 1 else 0
  | (some p, none) := if M.accept p then 1 else 0
  | (some p, some q) :=
    list.foldl (λ a b, a + b) 0 $
      list.map (λ a, regular_expression.char a) $
        list.filter (λ a, M.step p a q) as
  end
⟩

theorem to_GNFA_correct : M.accepts = (M.to_GNFA as univ).accepts :=
begin
  ext,
  split,
  { rintros ⟨q, accept, eval⟩,
    refine GNFA.accepts.step q _ _ x.append_nil.symm,
    swap,
    { rw set.mem_def,
      unfold to_GNFA,
      simp,
      unfold to_GNFA._match_1,
      rw set.mem_def at accept,
      simp [accept],
      exact rfl,
    },
    clear accept,
    revert eval,
    rw ← x.reverse_reverse,
    induction x.reverse generalizing q,
    case nil {
      assume hx,
      simp,
      refine GNFA.trace.start _,
      unfold to_GNFA,
      simp,
      unfold to_GNFA._match_1,
      rw set.mem_def at hx,
      simp at hx,
      simp [hx],
    },
    case cons : a as ih {
      assume hx,
      simp at *,
      rw NFA.mem_step_set at hx,
      rcases hx with ⟨p, mem, step⟩,
      refine GNFA.trace.step p (ih p mem) _ rfl,
      rw set.mem_def,
      unfold to_GNFA,
      simp,
      unfold to_GNFA._match_1,
      rw regular_expression.mem_sum,      
      refine ⟨regular_expression.char a, _, rfl⟩,
      simpa [univ],
    },
  },
  { assume hx,
    cases hx with x step x y z q t step eq,
    case start { cases step,},
    unfold to_GNFA at step,
    rw set.mem_def at step,
    simp at step,
    unfold to_GNFA._match_1 at step,
    by_cases M.accept q,
    swap, simp [h] at step, cases step,
    simp [h] at step,
    cases step,
    refine ⟨q, h, _⟩,
    simp at eq, cases eq,
    clear h eq step,
    revert t,
    rw ← x.reverse_reverse,
    induction x.reverse generalizing q,
    case nil {
      assume hx,
      simp at *,
      cases hx,
      case start : x step {
        unfold to_GNFA at step,
        rw set.mem_def at step,
        simp at step,
        unfold to_GNFA._match_1 at step,
        by_cases M.start x,
        exact h,
        simp [h] at step,
        cases step,
      },
      case step : x y z p t step eq {
        simp at eq,
        rw eq.2 at *,
        unfold to_GNFA at step,
        rw set.mem_def at step,
        simp at step,
        unfold to_GNFA._match_1 at step,
        rw regular_expression.mem_sum at step,
        rcases step with ⟨r, mem, matches⟩,
        simp at mem,
        rcases mem with ⟨a, _, eq⟩,
        rw ← eq at matches,
        cases matches,
      },
    },
    case cons : a as ih {
      assume hx,
      simp at *,
      rw NFA.mem_step_set,
      cases hx,
      case start : q step {
        unfold to_GNFA at step,
        simp at step,
        rw set.mem_def at step,
        unfold to_GNFA._match_1 at step,
        by_cases M.start q,
        { simp [h] at step,
          by_cases as.reverse.append [a] = [],
          { have h : as.reverse ++ [a] = list.nil := h,
            rw ← list.reverse_cons a as at h,
            rw list.reverse_eq_nil at h,
            contradiction,
          },
          { rcases list.exists_cons_of_ne_nil h with ⟨a, as, h⟩,
            rw h at step,
            cases step,
          },
        },
        { simp [h] at step,
          cases step,
        },
      },
      case step : y z p q t step eq {
        unfold to_GNFA at step,
        rw set.mem_def at step,
        simp at step,
        unfold to_GNFA._match_1 at step,
        replace eq : as.reverse ++ [a] = y ++ z := eq,
        rw regular_expression.mem_sum at step,
        rcases step with ⟨r, mem, matches⟩,
        simp at mem,
        rcases mem with ⟨b, ⟨_, step⟩, eq⟩,
        rw ← eq at matches,
        cases matches,
        rw ← list.reverse_inj at eq,
        simp at eq,
        rw ← eq.1 at step,
        refine ⟨p, _, step⟩,
        rw ← y.reverse_reverse at t,
        rw ← eq.2 at t,
        exact ih p t,        
      },
    },
  },
end

end NFA

namespace GNFA

def rip (M : GNFA α n.succ) : GNFA α n :=
⟨
  λ p q,
  let p := p.map fin.cast_succ in
  let q := q.map fin.cast_succ in
  let n : option (fin n.succ) := some ⟨n, lt_add_one n⟩ in
  M.step p q + M.step p n * (M.step n n).star * M.step n q
⟩

lemma rip_trace_aux (M : GNFA α n.succ) {x q} (t : M.trace x q) :
  (∃ p, q = fin.cast_succ p ∧ M.rip.trace x p) ∨
  q = fin.last n ∧
    ( ∃ y z (xs : list (list α)) p,
      (option.map (λ p, M.rip.trace y p) p).get_or_else (y = []) ∧
      z ∈ (M.step (p.map fin.cast_succ) (some (fin.last n))).matches ∧
      (∀ x ∈ xs, x ∈ (M.step (some (fin.last n)) (some (fin.last n))).matches) ∧
      x = y ++ z ++ xs.join) :=
begin
  induction t,
  case start : x q matches {
    revert matches,
    refine fin.last_cases _ _ q,
    { assume matches,
      right,
      refine ⟨rfl, _⟩,
      refine ⟨[], x, [], none, by simp, matches, _, by simp⟩,
      assume x mem,
      cases mem,
    },
    { assume q matches,
      left,
      refine ⟨q, rfl, _⟩,
      exact trace.start (or.inl matches),
    },
  },
  case step : x y z p q t matches eq ih {
    rw eq, clear eq x,
    revert ih matches,
    refine fin.last_cases _ _ p; refine fin.last_cases _ _ q,
    { assume ih matches,
      right,
      refine ⟨rfl, _⟩,
      cases ih,
      case inl {
        rcases ih with ⟨p, eq, t⟩,
        exfalso,
        exact fin.cast_succ_ne_last eq.symm,
      },
      rcases ih with ⟨_, y, z', xs, p, t', matches', x_matches, eq⟩,
      rw eq, clear eq,
      refine ⟨y, z', xs ++ [z], p, t', matches', _, by simp⟩,
      { assume x mem,
        simp at mem,
        cases mem,
        case inl {
          exact x_matches x mem,
        },
        case inr {
          rw mem,
          exact matches,
        },
      },
    },
    { assume q ih matches,
      left,
      refine ⟨q, rfl, _⟩,
      cases ih,
      case inl {
        rcases ih with ⟨p, eq, t⟩,
        exfalso,
        exact fin.cast_succ_ne_last eq.symm,
      },
      rcases ih with ⟨_, y, z', xs, p, t', matches', x_matches, eq⟩,
      rw eq, clear eq,
      cases p,
      case none {
        simp at t',
        rw t', clear t' y,
        refine trace.start (or.inr _),
        simp,
        rw ← list.append_assoc,
        refine ⟨_, _, _, matches, rfl⟩,
        refine ⟨_, _, matches', _, rfl⟩,
        exact ⟨_, rfl, x_matches⟩,
      },
      case some {
        simp at t',
        rw list.append_assoc,
        rw list.append_assoc,
        refine trace.step _ t' _ rfl,
        right,
        rw ← list.append_assoc,
        refine ⟨_, _, _, matches, rfl⟩,
        refine ⟨_, _, matches', _, rfl⟩,
        exact ⟨_, rfl, x_matches⟩,
      },
    },
    { assume p ih matches,
      right,
      refine ⟨rfl, _⟩,
      cases ih,
      case inl {
        rcases ih with ⟨p', eq, t⟩,
        simp at eq, rw ← eq at t, clear eq p',
        refine ⟨y, z, [], some p, by simp [t], matches, _, by simp⟩,
        assume x mem,
        cases mem,
      },
      case inr {
        rcases ih with ⟨eq, _⟩,
        exfalso,
        exact fin.cast_succ_ne_last eq,
      },
    },
    { assume q p ih matches,
      cases ih,
      case inl {
        rcases ih with ⟨p', eq, t⟩,
        simp at eq, rw ← eq at t, clear eq p',
        left,
        refine ⟨q, rfl, _⟩,
        exact trace.step _ t (or.inl matches) rfl,
      },
      case inr {
        rcases ih with ⟨eq, _⟩,
        exfalso,
        exact fin.cast_succ_ne_last eq,
      },
    },
  },
end

lemma rip_trace_correct (M : GNFA α n.succ) {x} {q : fin n} : M.trace x (fin.cast_succ q) ↔ M.rip.trace x q :=
begin
  split,
  { assume t,
    cases M.rip_trace_aux t,
    case inl {
      rcases h with ⟨p, eq, t⟩,
      simp at eq,
      rw eq,
      exact t,
    },
    case inr {
      cases h with eq _,
      exfalso,
      exact fin.cast_succ_ne_last eq,
    },
  },
  { assume t,
    induction t,
    case start : x q matches { 
      cases matches,
      case inl {
        exact trace.start matches,
      },
      case inr {
        rcases matches with ⟨y, z, hy, hz, eq⟩,
        rw ← eq, clear eq x,
        refine trace.step ⟨n, lt_add_one n⟩ _ hz rfl,
        clear hz z,
        rcases hy with ⟨y, z, hy, hz, eq⟩,
        rw ← eq, clear eq,        
        rcases hz with ⟨xs, join, matches⟩,
        rw join, clear join,
        revert matches,
        rw ← xs.reverse_reverse,
        induction xs.reverse,
        case nil {
          simp,
          exact trace.start hy,
        },
        case cons : x xs ih {
          assume matches,
          simp at *,
          rw ← list.append_assoc,
          refine trace.step _ (ih _) (matches x (or.inr rfl)) rfl,
          assume y mem,
          exact matches y (or.inl mem),
        },
      },
    },
    case step : x y z p q t matches eq ih {
      cases matches,
      case inl {
        exact trace.step _ ih matches eq,
      },
      case inr {
        rw eq, clear eq x,
        rcases matches with ⟨w, x, hw, hx, eq⟩,
        rw ← eq, clear eq z,
        rw ← list.append_assoc,
        refine trace.step _ _ hx rfl,
        rcases hw with ⟨w, x, hw, hx, eq⟩,
        rw ← eq, clear eq,
        rw ← list.append_assoc,
        rcases hx with ⟨xs, join, matches⟩,
        rw join, clear join x,
        revert matches,
        rw ← xs.reverse_reverse,
        induction xs.reverse,
        case nil {
          assume matches,
          simp at *,
          exact trace.step _ ih hw rfl,
        },
        case cons : x xs ih {
          assume matches,
          simp at *,
          rw ← list.append_assoc,
          rw ← list.append_assoc,
          refine trace.step _ _ (matches x (or.inr rfl)) rfl,
          rw list.append_assoc,
          apply ih,
          assume y mem,
          exact matches y (or.inl mem),
        },
      },
    },
  },
end

theorem rip_correct (M : GNFA α n.succ) : M.rip.accepts = M.accepts :=
begin
  ext,
  split,
  { assume t,
    cases t,
    case start : x matches {
      cases matches,
      case inl {
        simp at matches,
        exact accepts.start matches,
      },
      case inr {
        rcases matches with ⟨y, z, y_matches, z_matches, eq⟩,
        rw ← eq,
        refine accepts.step _ _ z_matches rfl,
        rcases y_matches with ⟨y, z, y_matches, z_matches, eq⟩,
        rw ← eq, clear eq,
        rcases z_matches with ⟨xs, join, x_matches⟩,
        rw join, clear join,
        revert x_matches,
        rw ← xs.reverse_reverse,
        induction xs.reverse,
        case nil {
          assume x_matches,
          refine trace.start _,
          simpa,
        },
        case cons : x xs ih {
          assume x_matches,
          simp at *,
          rw ← list.append_assoc,
          refine trace.step _ _ (x_matches x (or.inr rfl)) rfl,
          apply ih,
          assume x mem,
          exact x_matches x (or.inl mem),
        },
      },
    },
    case step : x y z q t matches eq {
      rw eq, clear eq x,
      cases matches,
      case inl {
        refine accepts.step _ _ matches rfl,
        rw rip_trace_correct,
        exact t,
      },
      case inr {
        rcases matches with ⟨z, x, z_matches, x_matches, eq⟩,
        rw ← eq, clear eq,
        rw ← list.append_assoc,
        refine accepts.step _ _ x_matches rfl,
        clear x_matches x,
        rcases z_matches with ⟨z, x, z_matches, x_matches, eq⟩,
        rw ← eq, clear eq,
        rw ← list.append_assoc,
        rcases x_matches with ⟨xs, join, x_matches⟩,
        rw join, clear join,
        revert x_matches,
        rw ← xs.reverse_reverse,
        induction xs.reverse,
        case nil {
          assume matches,
          simp,
          refine trace.step _ _ z_matches rfl,
          rw rip_trace_correct,
          exact t,
        },
        case cons : x xs ih {
          assume matches,
          simp at *,
          rw ← list.append_assoc,
          rw ← list.append_assoc,
          refine trace.step _ _ (matches x (or.inr rfl)) rfl,
          rw list.append_assoc,
          apply ih,
          assume x mem,
          exact matches x (or.inl mem),
        },
      },
    },
  },
  { assume t,
    cases t,
    case start : x matches {
      refine accepts.start (or.inl matches),
    },
    case step : x y z q t matches eq {
      rw eq, clear eq x,
      cases M.rip_trace_aux t,
      case inl {
        rcases h with ⟨q, eq, t⟩,
        rw eq at matches, clear eq,
        exact accepts.step _ t (or.inl matches) rfl,
      },
      case inr {
        rcases h with ⟨eq, h⟩,
        rw eq at *, clear eq,
        rcases h with ⟨y, w, xs, p, t', w_matches, x_matches, eq⟩,
        rw eq, clear eq,
        cases p,
        case none {
          simp at *,
          rw t', clear t' y,
          simp,
          refine accepts.start _,
          rw ← list.append_assoc,
          right,
          refine ⟨_, _, _, matches, rfl⟩,
          refine ⟨_, _, w_matches, _, rfl⟩,
          exact ⟨xs, rfl, x_matches⟩,
        },
        case some {
          simp at *,
          refine accepts.step _ t' _ rfl,
          right,
          rw ← list.append_assoc,
          refine ⟨_, _, _, matches, rfl⟩,
          refine ⟨_, _, w_matches, _, rfl⟩,
          exact ⟨xs, rfl, x_matches⟩,
        },
      },
    },
  },
end

def to_regular_expression : Π {n}, GNFA α n → regular_expression α
| 0 M := M.step none none
| (nat.succ n) M := M.rip.to_regular_expression

theorem to_regular_expression_correct (M : GNFA α n) : M.accepts = M.to_regular_expression.matches :=
begin
  induction n,
  case zero {
    ext,
    split,
    { assume hx,
      cases hx,
      case start : x matches {
        exact matches,
      },
      case step : x y z q t matches eq {
        exact fin.elim0 q,        
      },
    },
    { assume matches,
      exact accepts.start matches,
    },
  },
  case succ : n ih {
    rw ← M.rip_correct,
    rw ih M.rip,
    refl,
  },
end

end GNFA

namespace NFA

theorem to_regular_expression (M : NFA α σ) [fintype α] [fintype σ] : ∃ (r : regular_expression α), M.accepts = r.matches :=
begin
  rcases fintype.exists_univ_list α with ⟨as, _, univ⟩,
  let M' := M.convert (fintype.equiv_fin σ),
  let M'' := @to_GNFA _ _ M' (classical.dec_pred _) (classical.dec_pred _) (λ p a q, classical.dec _) as univ,
  let r := M''.to_regular_expression,
  use r,
  rw ← GNFA.to_regular_expression_correct,
  rw ← to_GNFA_correct,
  rw ← convert_correct,
end

end NFA
