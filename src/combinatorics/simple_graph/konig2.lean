import data.fintype.basic
import data.set.finite
import data.finset.lattice
import tactic

open fintype
open function

universes u v

structure inv_system (α : Type u) :=
(ι : ℕ → finset α)
(f : α → α)
(fprop : ∀ (n : ℕ) (x : α), x ∈ ι n.succ → f x ∈ ι n)

variables {α : Type u}

instance : has_coe_to_fun (inv_system α) := ⟨_, inv_system.ι⟩

@[simp] lemma inv_system.eq_coe (S : inv_system α) : S.ι = S := rfl

/-- Type of all limits of the inverse system. -/
structure inv_system.limit {α : Type u} (ι : inv_system α) :=
(s : ℕ → α)
(s_mem : ∀ (n : ℕ), s n ∈ ι n)
(is_lim : ∀ (n : ℕ), ι.f (s n.succ) = s n)

variables (ι : inv_system α)

namespace inv_system

def iterate (n : ℕ) (x : α) : α := n.iterate ι.f x

lemma iterate_prop {n : ℕ} (k : ℕ) (x : α) (h : x ∈ ι (n + k)) :
  ι.iterate k x ∈ ι n :=
begin
  induction k generalizing x,
  { exact h, },
  { simp only [iterate, nat.iterate],
    apply k_ih,
    apply ι.fprop _ _ h, },
end

lemma app_iterate_eq_iterate_app (n : ℕ) (x : α) :
  ι.f (ι.iterate n x) = ι.iterate n (ι.f x) :=
begin
  induction n generalizing x,
  refl,
  simp only [iterate, nat.iterate] at ⊢ n_ih,
  rw n_ih,
end

lemma iterate_succ (n : ℕ) (x : α) :
  ι.iterate n.succ x = ι.f (ι.iterate n x) :=
begin
  simp [iterate, nat.iterate],
  exact (ι.app_iterate_eq_iterate_app _ _).symm,
end

lemma iterate_succ' (n : ℕ) (x : α) :
  ι.iterate n.succ x = (ι.iterate n (ι.f x)) := rfl

@[simp]
lemma iterate_iterate (n n' : ℕ) (x : α) :
  ι.iterate n (ι.iterate n' x) = ι.iterate (n + n') x :=
begin
  induction n' generalizing x,
  { refl },
  { rw [iterate_succ', n'_ih, iterate_succ'], },
end

/-- An element is *very extendable* if it is the iterated image of elements that are arbitarily
far along in the inverse system. -/
def very_extendable (n : ℕ) (a : α) : Prop :=
∀ k, ∃ b, b ∈ ι (n + k) ∧ a = ι.iterate k b

lemma very_extendable_mem (n : ℕ) (a : α) (hv : ι.very_extendable n a) :
  a ∈ ι n :=
begin
  rcases hv 0 with ⟨b, hb, rfl⟩,
  exact hb,
end

lemma very_extendable_of_image (n : ℕ) (a : α)
  (hv : ι.very_extendable n.succ a) : ι.very_extendable n (ι.f a) :=
begin
  intro k,
  rcases hv k with ⟨b, hbel, rfl⟩,
  use ι.f b,
  split,
  exact ι.fprop _ _ (by { convert hbel, omega }),
  induction k,
  refl,
  rw app_iterate_eq_iterate_app,
end

lemma very_extendable_lift (n : ℕ) (a : α) (hv : ι.very_extendable n a) :
  ∃ (a' : α), a = ι.f a' ∧ ι.very_extendable n.succ a' :=
begin
  by_contra h,
  simp only [very_extendable, not_exists, not_and, not_forall] at h,
  have h' : ∀ (a' : α), ∃ (k : ℕ), ∀ (x : α),
              a = ι.f a' → x ∈ ι (n.succ + k) → ¬ a' = ι.iterate k x,
  { intro a',
    by_cases he : a = ι.f a',
    swap, { use 0, simp only [he, forall_prop_of_false, not_false_iff, forall_true_iff], },
    rcases h a' he with ⟨k, h⟩,
    use k,
    intros x ha,
    exact h x, },
  choose f hf using h',
  let s : ℕ → finset α := λ k,
    by { classical, exact (ι (n.succ + k)).filter (λ a', a = ι.f (ι.iterate k a')) },
  have s_nonempty : ∀ k, (s k).nonempty,
  { intro k,
    rcases hv k.succ with ⟨b, hb, rfl⟩,
    use b,
    rw [finset.mem_filter, nat.succ_add],
    use hb,
    rw iterate_succ, },
  rcases finset.exists_max_image (s 0) f (s_nonempty 0) with ⟨xmax, xmax_el, hxmax⟩,
  rcases (s_nonempty (f xmax)) with ⟨x', hx'⟩,
  simp only [finset.mem_filter] at xmax_el hx' hxmax,
  let x₀ := ι.iterate (f xmax) x',
  have hx₀ : x₀ ∈ _ := ι.iterate_prop _ _ hx'.1,
  specialize hxmax x₀ ⟨hx₀, hx'.2⟩,
  have h : n.succ + f xmax = (n.succ + f x₀) + (f xmax - f x₀) := by omega,
  let x₁ := ι.iterate (f xmax - f x₀) x',
  rw h at hx',
  have hx₁ : x₁ ∈ _ := ι.iterate_prop (f xmax - f x₀) x' hx'.1,
  apply hf x₀ x₁ hx'.2 hx₁,
  simp only [iterate_iterate],
  convert_to _ = ι.iterate (f xmax) x',
  { congr,
    omega, },
  refl,
end


/-- Restrict an inverse system to the very extendable elements. Noncomputable since
it's not in general possible to know which elements are very extendable. -/
@[simps]
noncomputable
def restrict_very_extendable : inv_system α :=
{ ι := λ n, by { classical, exact (ι n).filter (ι.very_extendable n) },
  f := ι.f,
  fprop := λ n a, begin
    simp only [finset.mem_filter],
    rintro ⟨ha, hv⟩,
    exact ⟨ι.fprop _ _ ha, ι.very_extendable_of_image _ _ hv⟩,
  end }

lemma finset.nonempty_def {α : Type*} {s : finset α} :
  s.nonempty ↔ ∃ (x : α), x ∈ s := by refl

lemma restrict_nonempty (hne : ∀ n, (ι n).nonempty) (n : ℕ) :
  (ι.restrict_very_extendable n).nonempty :=
begin
  rw finset.nonempty_def,
  by_contra h,
  simp only [restrict_very_extendable, not_exists] at h,
  change ∀ (x : α), ¬ x ∈ finset.filter _ _ at h,
  simp only [very_extendable, not_exists, not_and, finset.mem_filter, not_forall] at h,
  have h' : ∀ (x : α), ∃ (k : ℕ), ∀ (x' : α),
              x ∈ ι n → x' ∈ ι (n + k) → ¬ x = ι.iterate k x',
  { intro x,
    by_cases hx : x ∈ ι n,
    swap, { use 0, simp [hx], },
    specialize h x hx,
    cases h with k h,
    use k,
    intros x' hx,
    exact h x', },
  choose f hf using h',
  rcases finset.exists_max_image (ι n) f (hne n) with ⟨xmax, xmax_el, hxmax⟩,
  rcases (hne (n + f xmax)) with ⟨x', hx'⟩,
  let x₀ := ι.iterate (f xmax) x',
  have hx₀ : x₀ ∈ _ := ι.iterate_prop _ _ hx',
  specialize hxmax x₀ hx₀,
  have h : n + f xmax = (n + f x₀) + (f xmax - f x₀) := by omega,
  let x₁ := ι.iterate (f xmax - f x₀) x',
  rw h at hx',
  have hx₁ : x₁ ∈ _ := ι.iterate_prop (f xmax - f x₀) x' hx',
  apply hf x₀ x₁ hx₀ hx₁,
  simp [x₁],
  convert_to _ = ι.iterate (f xmax) x',
  { congr,
    omega, },
  refl,
end

end inv_system

def mk_lim (f : ℕ → α → α)
  (hf : ∀ (n : ℕ) (a : α), a ∈ ι n → f n a ∈ ι n.succ ∧ a = ι.f (f n a))
  (a₀ : α) (h₀ : a₀ ∈ ι 0) : Π (n : ℕ), {a // a ∈ ι n}
| 0 := ⟨a₀, h₀⟩
| (n+1) := let v := mk_lim n in ⟨f n v.1, (hf n v.1 v.2).1⟩

/-- Konig's lemma for inverse systems -/
lemma inv_lim_exists_if_finite_and_nonempty (hne : ∀ n, (ι n).nonempty) :
  nonempty ι.limit :=
begin
  let ι' := ι.restrict_very_extendable,
  have key : ∀ (n : ℕ) (a : α), ∃ (a' : α),
     a ∈ ι' n → a' ∈ ι' n.succ ∧ a = ι'.f a',
  { intros n a,
    by_cases h : a ∈ ι' n,
    { simp only [inv_system.restrict_very_extendable_ι, finset.mem_filter] at h,
      rcases ι.very_extendable_lift n a h.2 with ⟨b, rfl, hb⟩,
      use b,
      intro,
      simp only [and_true, inv_system.restrict_very_extendable_f,
                 inv_system.restrict_very_extendable_ι, eq_self_iff_true,
                 finset.mem_filter],
      exact ⟨ι.very_extendable_mem _ _ hb, hb⟩, },
    { use a, } },
  choose f hf using key,
  rcases (ι.restrict_nonempty hne 0) with ⟨a₀, ha₀⟩,
  let f' := λ n, (mk_lim ι' f hf a₀ ha₀ n).1,
  have f'sub : ∀ n, f' n ∈ ι' n,
  { intro n,
    induction n,
    { exact ha₀, },
    { specialize hf _ _ n_ih,
      convert hf.1, }, },
  fsplit,
  fsplit,
  { exact f' },
  { intro n,
    have strong : ι' n ⊆ ι n,
    { simp only [finset.filter_subset, inv_system.restrict_very_extendable_ι], },
    apply strong,
    apply f'sub, },
  { intro n,
    dsimp [f'],
    simp [mk_lim],
    exact (hf _ _ (f'sub n)).2.symm, },
end
