import set_theory.ordinal_arithmetic

universes u v

namespace ordinal

/-- Enumerator function for an unbounded set of ordinals. -/
noncomputable def enum_ord {S : set ordinal.{u}} (hS : ∀ α, ∃ β, S β ∧ α < β) :
  ordinal.{u} → ordinal.{u} :=
wf.fix (λ α f, omin _
--(λ β, S β ∧ (bsup.{u u} α f) < β) -- this can be inferred
(hS (bsup.{u u} α f)))

theorem enum_ord_def {S : set ordinal.{u}} (hS : ∀ α, ∃ β, S β ∧ α < β) (α) :
  enum_ord hS α = omin (λ β, S β ∧ bsup.{u u} α (λ γ _, enum_ord hS γ) < β) (hS _) :=
wf.fix_eq _ _

private theorem enum_ord_mem_aux {S : set ordinal.{u}} (hS : ∀ α, ∃ β, S β ∧ α < β) (α) :
  S (enum_ord hS α) ∧ bsup.{u u} α (λ γ _, enum_ord hS γ) < (enum_ord hS α) :=
by { rw enum_ord_def, exact omin_mem (λ _, _ ∧ _) _ }

theorem enum_ord_mem {S : set ordinal.{u}} (hS : ∀ α, ∃ β, S β ∧ α < β) (α) :
  enum_ord hS α ∈ S :=
(enum_ord_mem_aux hS α).left

theorem enum_ord_mem' {S : set ordinal.{u}} (hS : ∀ α, ∃ β, S β ∧ α < β) (α) :
  bsup.{u u} α (λ γ _, enum_ord hS γ) < enum_ord hS α :=
(enum_ord_mem_aux hS α).right

theorem enum_ord_inj {S : set ordinal.{u}} (hS : ∀ α : ordinal.{u}, ∃ β, S β ∧ α < β) :
strict_mono (enum_ord hS) :=
begin
  intros α β hαβ,
  nth_rewrite 1 enum_ord_def,
  by_contra h,
  push_neg at h,
  have := omin_le h,
end

end ordinal


/-- The subtype of fixed points of a function. -/
def fixed_points (f : ordinal.{u} → ordinal.{u}) : Type (u + 1) := {x // f x = x}

section
variable {f : ordinal.{u} → ordinal.{u}}

theorem le_of_strict_mono (hf : strict_mono f) : ∀ α, α ≤ f α :=
begin
  by_contra,
  push_neg at h,
  have h' := ordinal.omin_mem _ h,
  exact not_lt_of_ge (@ordinal.omin_le _ h (f _) (hf h')) h',
end

/-- An explicit fixed point for a normal function. Built as `sup {f^[n] α}`. -/
noncomputable def fixed_point (hf : ordinal.is_normal f) (α : ordinal.{u}) : fixed_points f :=
begin
  let g := λ n, f^[n] α,
  have H : ∀ {n}, g (n + 1) = (f ∘ g) n := λ n, function.iterate_succ_apply' f n α,
  have H' : ∀ {n}, g (n + 1) ≤ ordinal.sup.{0 u} (f ∘ g) := λ _, by {rw H, apply ordinal.le_sup},
  use ordinal.sup.{0 u} g,
  suffices : ordinal.sup.{0 u} (f ∘ g) = ordinal.sup.{0 u} g,
  { rwa @ordinal.is_normal.sup.{0 u u} f hf ℕ g (nonempty.intro 0) },
  apply has_le.le.antisymm;
  rw ordinal.sup_le;
  intro n,
  { rw ←H,
    exact ordinal.le_sup _ _ },
  cases n,
  { suffices : g 0 ≤ g 1,
    { exact le_trans this H' },
    change g 0 ≤ g 1 with (f^[0] α) ≤ (f^[1] α),
    rw [function.iterate_one f, function.iterate_zero_apply f α],
    exact le_of_strict_mono hf.strict_mono _ },
  exact H'
end

instance (hf : ordinal.is_normal f) : nonempty (fixed_points f) := ⟨fixed_point hf 0⟩

def fix_point_enum (hf : normal f) (α : ordinal.{u}) : fixed_points f := sorry
--ordinal.limit_rec_on α
