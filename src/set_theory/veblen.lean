import set_theory.ordinal_arithmetic

universes u v

namespace ordinal

/-- Enumerator function for an unbounded set of ordinals. -/
noncomputable def enum_ord {S : set ordinal.{u}} (hS : ∀ α : ordinal.{u}, ∃ β, S β ∧ α < β) :
  ordinal.{u} → ordinal.{u} :=
wf.fix (λ α f, omin
(λ β, S β ∧ (bsup.{u u} α f) < β) -- this can be inferred
(hS (bsup.{u u} α f)))

theorem enum_ord_def {S : set ordinal.{u}} (hS : ∀ α : ordinal.{u}, ∃ β, S β ∧ α < β)
(α : ordinal.{u}) :
  enum_ord hS α = omin _ enum_ord (hS (bsup.{u u} α f)))

theorem enum_ord_mem {S : set ordinal.{u}} (hS : ∀ α : ordinal.{u}, ∃ β, S β ∧ α ≤ β) (o : ordinal.{u}):
  enum_ord hS o ∈ S :=
begin
  have : enum_ord hS o = _ := wf.fix_eq _ o,
  rw this,
  exact (λ _ _ _ h, h (omin_mem _ _) : ∀ S T e, T ⊆ S → omin T e ∈ S) _ _ _ (λ _, and.left)
end

theorem enum_ord_inj {S : set ordinal.{u}} (hS : ∀ α : ordinal.{u}, ∃ β, S β ∧ α ≤ β) :
strict_mono (enum_ord hS) :=
begin
  intros a b hab,
  have : enum_ord hS b = _ := wf.fix_eq _ b,
  rw this,
  have := (λ _ _ _ h, h (omin_mem _ _) : ∀ S T e, T ⊆ S → omin T e ∈ S) _ _ _ (λ _, and.left),
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
