import data.real.basic
import algebra.category.Group.abelian
import group_theory.finiteness
import data.set.finite
import some_lemmas

open_locale classical
open finset

universe u

variable (A : Ab.{u})

structure height_function :=
(to_fun : A → ℝ)
(nonneg : ∀ P, 0 ≤ to_fun P)
(C1 : A → ℝ)
(height_add_le : ∀ (Q P : A), to_fun (P + Q) ≤ 2 * to_fun P + C1 Q)
(m : ℕ)
(C2 : ℝ)
(height_nsmul_ge : ∀ (P : A), ↑(m+2)^2 * to_fun P - C2 ≤ to_fun ((m+2) • P))
(finite : ∀ (C : ℝ), set.finite { P : A | to_fun P < C })

variables {A} {m : ℕ}

abbreviation M : add_subgroup A :=
{ carrier := { x | ∃ y, x = m • y },
  zero_mem' := ⟨0, by rw nsmul_zero⟩,
  add_mem' := λ x y ⟨x', hx⟩ ⟨y', hy⟩, ⟨x' + y', by rw [nsmul_add, ←hx, ←hy]⟩,
  neg_mem' := λ x ⟨x', hx⟩, ⟨-x', by rw [neg_nsmul, ←hx]⟩ }


local notation `A/m` := A⧸(@M A m)

theorem descent (f : height_function A)  [fin_quot : fintype (A/m)] :
  add_subgroup.fg (⊤ : add_subgroup A) :=
begin
  set Q := image (λ (q : A/m), Exists.some (add_mk_surjective A _ q))
    (fin_quot.elems) with Q_eq,
  have hQ : ∀ (a : A/m), ∃ (q : A), q ∈ Q ∧ quotient_add_group.mk q = a,
  { intro a,
    have mem1 : a ∈ fin_quot.elems := fintype.complete a,
    have mem2 : Exists.some (add_mk_surjective A _ a) ∈ Q,
      rw [Q_eq, mem_image], use a, refine ⟨mem1, rfl⟩,
    refine ⟨_, mem2, _⟩,
    exact Exists.some_spec (add_mk_surjective A _ a), },

end
