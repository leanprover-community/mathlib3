/-
Author: Russell Emerine
Based on: https://courses.engr.illinois.edu/cs373/sp2013/Lectures/lec07.pdf
TODO: write comments and TODOs, organize, etc.
-/
import computability.regular_expression_to_NFA.defs
import computability.regular_expression_to_NFA.star

universe u

variables {α : Type u} [dec : decidable_eq α]

namespace regular_expression

include dec

lemma zero_to_NFA_correct : (zero : regular_expression α).matches = zero.to_NFA.accepts :=
begin
  ext,
  split,
  { assume hx,
    cases hx,
  },
  { assume hx,
    cases hx with q _,
    cases q,
  },
end

lemma epsilon_to_NFA_correct : (epsilon : regular_expression α).matches = epsilon.to_NFA.accepts :=
begin
  ext,
  split,
  { assume hx,
    cases hx,
    repeat { fconstructor, }, -- yes really it's like 5 of them
  },
  { assume hx,
    rcases hx with ⟨q, accept, eval⟩,
    cases q,
    cases accept,
    revert eval,
    rw ← x.reverse_reverse,
    induction x.reverse,
    case nil {
      simp,
    },
    case cons : a as ih {
      assume hx,
      simp at hx,
      rw NFA.mem_step_set at hx,
      rcases hx with ⟨q, mem, step⟩,
      cases step,
    },
  },
end

theorem char_to_NFA_correct {a : α} : (char a).matches = (char a).to_NFA.accepts :=
begin
  ext,
  split,
  { assume hx,
    cases hx,
    refine ⟨tt, rfl, _⟩,
    unfold NFA.eval NFA.eval_from list.foldl,
    rw NFA.mem_step_set,
    repeat { fconstructor, },
  },
  { assume hx,
    rcases hx with ⟨q, accept, eval⟩,
    cases q,
    case ff {
      contradiction,
    },
    case tt {
      clear accept,
      revert eval,
      rw ← x.reverse_reverse,
      cases x.reverse,
      case nil {
        assume hx,
        contradiction,
      },
      case cons : c as {
        assume hx,
        unfold NFA.eval NFA.eval_from at hx,
        simp at *,
        rw NFA.mem_step_set at hx,
        rcases hx with ⟨p, mem, step⟩,
        cases p,
        case ff {
          revert mem,
          induction as,
          case nil {
            assume _,
            rcases step with ⟨_, eq, _⟩,
            rw eq,
            exact rfl,
          },
          case cons : b as {
            assume h,
            simp at *,
            rcases h with ⟨S, ⟨q, range⟩, mem⟩,
            rw ← range at mem,
            simp at mem,
            rcases mem with ⟨_, _, _, nope⟩,
            contradiction,
          },
        },
        case tt {
          cases step,
          contradiction,
        },
      },
    },
  },
end

lemma plus_to_NFA_correct
  {r₁ r₂ : regular_expression α}
  (hr₁ : r₁.matches = r₁.to_NFA.accepts)
  (hr₂ : r₂.matches = r₂.to_NFA.accepts)
  : (r₁.plus r₂).matches = (r₁.plus r₂).to_NFA.accepts :=
begin
  ext,
  split,
  { assume hx,
    cases hx,
    case inl {
      rw hr₁ at hx,
      clear hr₁ hr₂,
      rw set.mem_def at *,
      unfold NFA.accepts NFA.eval NFA.eval_from at *,
      simp at *,
      rcases hx with ⟨q, accept, eval⟩,
      refine ⟨sum.inl q, accept, _⟩,
      clear accept,
      revert eval,
      rw ← x.reverse_reverse,
      induction x.reverse generalizing q,
      case nil {
        exact id,
      },
      case cons : a as ih {
        assume mem,
        simp at *,
        rcases mem with ⟨S, ⟨p, range⟩, mem⟩,
        rw ← range at mem,
        simp at mem,
        rcases mem with ⟨mem, step⟩,
        rw NFA.mem_step_set,
        exact ⟨sum.inl p, ih p mem, step⟩,
      },
    },
    case inr {
      rw hr₂ at hx,
      clear hr₁ hr₂,
      rw set.mem_def at *,
      unfold NFA.accepts NFA.eval NFA.eval_from at *,
      simp at *,
      rcases hx with ⟨q, accept, eval⟩,
      refine ⟨sum.inr q, accept, _⟩,
      clear accept,
      revert eval,
      rw ← x.reverse_reverse,
      induction x.reverse generalizing q,
      case nil {
        exact id,
      },
      case cons : a as ih {
        assume mem,
        simp at *,
        rcases mem with ⟨S, ⟨p, range⟩, mem⟩,
        rw ← range at mem,
        simp at *,
        rcases mem with ⟨mem, step⟩,
        rw NFA.mem_step_set,
        exact ⟨sum.inr p, ih p mem, step⟩,
      },
    },
  },
  { assume hx,
    rcases hx with ⟨q, accept, eval⟩,
    cases q,
    case inl {
      left,
      rw hr₁,
      refine ⟨q, accept, _⟩,
      clear accept,
      revert eval,
      rw ← x.reverse_reverse,
      induction x.reverse generalizing q,
      case nil {
        exact id,
      },
      case cons : a as ih {
        assume h,
        unfold NFA.eval NFA.eval_from at *,
        simp at *,
        rcases h with ⟨S, ⟨p, range⟩, mem⟩,
        rw ← range at mem,
        simp at *,
        rcases mem with ⟨mem, step⟩,
        rw NFA.mem_step_set,
        cases p,
        case inl {
          exact ⟨p, ih p mem, step⟩,
        },
        case inr {
          cases step,
        },
      },
    },
    case inr {
      right,
      rw hr₂,
      refine ⟨q, accept, _⟩,
      clear accept,
      revert eval,
      rw ← x.reverse_reverse,
      induction x.reverse generalizing q,
      case nil {
        exact id,
      },
      case cons : a as ih {
        assume h,
        unfold NFA.eval NFA.eval_from at *,
        simp at *,
        rcases h with ⟨S, ⟨p, range⟩, mem⟩,
        rw ← range at mem,
        simp at *,
        rcases mem with ⟨mem, step⟩,
        rw NFA.mem_step_set,
        cases p,
        case inl {
          cases step,
        },
        case inr {
          exact ⟨p, ih p mem, step⟩,
        },
      },
    },
  },
end

lemma comp_to_NFA_eval₁ {r₁ r₂ : regular_expression α} {x : list α} (q : r₁.state) :
  q ∈ r₁.to_NFA.eval x ↔ sum.inl q ∈ (r₁.comp r₂).to_NFA.eval x :=
begin
  { rw ← x.reverse_reverse,
    induction x.reverse generalizing q,
    case nil {
      exact ⟨id, id⟩,
    },
    case cons : a as ih {
      split,
      { assume h,
        simp at *,
        rw NFA.mem_step_set at *,
        rcases h with ⟨p, eval, step⟩,
        rw ih p at eval,
        exact ⟨sum.inl p, eval, step⟩,
      },
      { assume h,
        simp at *,
        rw NFA.mem_step_set at *,
        rcases h with ⟨p, eval, step⟩,
        cases p,
        case inl {
          rw ← ih p at eval,
          exact ⟨p, eval, step⟩,
        },
        case inr {
          cases step,
        },
      },
    },
  },
end

lemma comp_to_NFA_eval₂ {r₁ r₂ : regular_expression α} {x y : list α} (q : r₂.state) :
  r₁.to_NFA.accepts x → q ∈ r₂.to_NFA.eval y → sum.inr q ∈ (r₁.comp r₂).to_NFA.eval_from ((r₁.comp r₂).to_NFA.eval x) y :=
begin
  assume accepts,
  rw ← y.reverse_reverse,
  induction y.reverse generalizing q,
  case nil {
    assume h,
    simp at *,
    rcases accepts with ⟨p, accept, eval⟩,
    rw @comp_to_NFA_eval₁ _ _ _ r₂ _ p at eval,
    revert eval,
    rw ← x.reverse_reverse at *,
    cases x.reverse,
    case nil {
      assume eval,
      exact ⟨h, p, accept, eval⟩,
    },
    case cons : a as {
      assume eval,
      simp at *,
      rw NFA.mem_step_set at *,
      rcases eval with ⟨r, mem, step⟩,
      refine ⟨r, mem, _⟩,
      cases r,
      case inl {
        exact ⟨h, p, accept, step⟩,
      },
      case inr {
        cases step,
      },
    },
  },
  case cons : b bs ih {
    assume h,
    simp at *,
    rw NFA.mem_step_set at *,
    rcases h with ⟨p, mem, step⟩,
    refine ⟨sum.inr p, ih p mem, step⟩,
  },
end

lemma comp_to_NFA_correct
  {r₁ r₂ : regular_expression α}
  (hr₁ : r₁.matches = r₁.to_NFA.accepts)
  (hr₂ : r₂.matches = r₂.to_NFA.accepts)
  : (r₁.comp r₂).matches = (r₁.comp r₂).to_NFA.accepts :=
begin
  ext,
  split,
  { assume hx,
    rcases hx with ⟨y, z, hy, hz, comp⟩,
    rw hr₁ at hy,
    rw hr₂ at hz,
    rw ← comp,
    clear hr₁ hr₂ comp x,
    rw set.mem_def at *,
    rw ← z.reverse_reverse at *,
    cases z.reverse with b bs,
    case nil {
      rcases hy with ⟨q, q_accept, q_eval⟩,
      rcases hz with ⟨p, p_accept, p_eval⟩,
      simp at *,
      rw comp_to_NFA_eval₁ q at q_eval,
      exact ⟨sum.inl q, ⟨q_accept, p, p_accept, p_eval⟩, q_eval⟩,
    },
    case cons {
      unfold NFA.accepts at hz ⊢,
      simp at *,
      rcases hz with ⟨q, accept, eval⟩,
      refine ⟨sum.inr q, accept, _⟩,
      rw ← list.append_assoc,
      rw NFA.eval_append_singleton,
      rw NFA.mem_step_set at *,
      rcases eval with ⟨p, mem, step⟩,
      refine ⟨sum.inr p, _, step⟩,
      unfold NFA.eval NFA.eval_from,
      simp,
      exact comp_to_NFA_eval₂ p hy mem,
    },
  },

  { assume hx,
    rcases hx with ⟨q, accept, eval⟩,
    cases q,
    case inl {
      use [x, list.nil],
      rcases accept with ⟨accept, nil⟩,
      refine ⟨_, _, by simp⟩,
      { rw hr₁,
        refine ⟨q, accept, _⟩,
        clear accept,
        revert eval,
        rw ← x.reverse_reverse,
        induction x.reverse generalizing q,
        case nil {
          exact id,
        },
        case cons : a as {
          assume h,
          unfold NFA.eval NFA.eval_from at *,
          simp at *,
          rw NFA.mem_step_set at *,
          rcases h with ⟨p, mem, step⟩,
          cases p,
          case inl {
            exact ⟨p, ih p mem, step⟩,
          },
          case inr {
            cases step,
          },
        },
      },
      { rw hr₂,
        rcases nil with ⟨q, accept, eval⟩,
        exact ⟨q, accept, eval⟩,
      },
    },
    case inr {
      suffices : ∀ x q,
        sum.inr q ∈ (r₁.comp r₂).to_NFA.eval x
        → ∃ y z,
            y ∈ r₁.to_NFA.accepts
          ∧ q ∈ r₂.to_NFA.eval z
          ∧ y ++ z = x,
      { specialize this x q eval,
        rcases this with ⟨y, z, y_accepts, z_eval, append⟩,
        use [y, z],
        split,
        rw hr₁,
        exact y_accepts,
        split,
        rw hr₂,
        exact ⟨q, accept, z_eval⟩,
        exact append,
      },
      clear accept eval q hr₁ hr₂,
      assume x q,
      rw ← x.reverse_reverse,
      induction x.reverse generalizing q,
      case nil {
        assume h,
        rcases h with ⟨start, nil⟩,
        refine ⟨[], [], _, start, by simp⟩,
        unfold NFA.accepts at *,
        simp at *,
        exact nil,
      },
      case cons : a as {
        assume h,
        unfold NFA.eval NFA.eval_from,
        simp at *,
        rw NFA.mem_step_set at *,
        rcases h with ⟨p, mem, step⟩,
        cases p,
        case inl {
          rcases step with ⟨start, r, accept, step⟩,
          refine ⟨(a :: as).reverse, _, [], start, by simp⟩,
          refine ⟨r, accept, _⟩,
          simp,
          rw NFA.mem_step_set,
          rw ← comp_to_NFA_eval₁ p at mem,
          exact ⟨p, mem, step⟩,
        },
        case inr {
          rcases ih p mem with ⟨y, accepts, z, eval, append⟩,
          refine ⟨y, accepts, z ++ [a], _, _⟩,
          { simp,
            rw NFA.mem_step_set,
            exact ⟨p, eval, step⟩,
          },
          { rw ← append,
            simp,
          },
        },
      },
    },
  },
end

lemma star_to_NFA_correct
  {r : regular_expression α}
  (hr : r.matches = r.to_NFA.accepts)
  : (star r).matches = (star r).to_NFA.accepts :=
begin
  ext,
  rw star_iff_pow,
  split,
  { rintros ⟨n, h⟩,
    cases n,
    case zero {
      cases h,
      refine ⟨none, trivial, trivial⟩,
    },
    case succ {
      rw r.pow_eval x n hr at h,
      rcases h with ⟨q, accept, t⟩,
      have := (r.star_eval x q).mpr ⟨n, t⟩,
      exact ⟨some q, accept, this⟩,
    },
  },
  { rintros ⟨q, accept, eval⟩,
    cases q,
    case none {
      use 0,
      rw ← x.reverse_reverse at *,
      cases x.reverse,
      case nil {
        exact rfl,
      },
      case cons : a as {
        simp at eval,
        rw NFA.mem_step_set at eval,
        rcases eval with ⟨q, mem, step⟩,
        cases q; cases step,
      },
    },
    case some {
      rcases (r.star_eval x q).mp eval with ⟨n, t⟩,
      refine ⟨n.succ, _⟩,
      exact (r.pow_eval x n hr).mpr ⟨q, accept, t⟩,
    },
  },
end

theorem to_NFA_correct (r : regular_expression α) : r.matches = r.to_NFA.accepts :=
begin
  induction r,
  case zero {
    exact zero_to_NFA_correct,
  },
  case epsilon {
    exact epsilon_to_NFA_correct,
  },
  case char : a {
    exact char_to_NFA_correct,
  },
  case plus : r₁ r₂ hr₁ hr₂ {
    exact plus_to_NFA_correct hr₁ hr₂,
  },
  case comp : r₁ r₂ hr₁ hr₂ {
    exact comp_to_NFA_correct hr₁ hr₂,
  },
  case star : r hr {
    exact star_to_NFA_correct hr,
  },
end

end regular_expression

