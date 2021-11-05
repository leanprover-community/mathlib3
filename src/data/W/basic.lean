/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import data.equiv.list

/-!
# W types

Given `α : Type` and `β : α → Type`, the W type determined by this data, `W_type β`, is the
inductively defined type of trees where the nodes are labeled by elements of `α` and the children of
a node labeled `a` are indexed by elements of `β a`.

This file is currently a stub, awaiting a full development of the theory. Currently, the main result
is that if `α` is an encodable fintype and `β a` is encodable for every `a : α`, then `W_type β` is
encodable. This can be used to show the encodability of other inductive types, such as those that
are commonly used to formalize syntax, e.g. terms and expressions in a given language. The strategy
is illustrated in the example found in the file `prop_encodable` in the `archive/examples` folder of
mathlib.

## Implementation details

While the name `W_type` is somewhat verbose, it is preferable to putting a single character
identifier `W` in the root namespace.
-/

/--
Given `β : α → Type*`, `W_type β` is the type of finitely branching trees where nodes are labeled by
elements of `α` and the children of a node labeled `a` are indexed by elements of `β a`.
-/
inductive W_type {α : Type*} (β : α → Type*)
| mk (a : α) (f : β a → W_type) : W_type

instance : inhabited (W_type (λ (_ : unit), empty)) :=
⟨W_type.mk unit.star empty.elim⟩

namespace W_type

variables {α : Type*} {β : α → Type*}

/-- The canonical map to the corresponding sigma type, returning the label of a node as an
  element `a` of `α`, and the children of the node as a function `β a → W_type β`. -/
def to_sigma : W_type β → Σ a : α, β a → W_type β
| ⟨a, f⟩ := ⟨a, f⟩

/-- The canonical map from the sigma type into a `W_type`. Given a node `a : α`, and
  its children as a function `β a → W_type β`, return the corresponding tree. -/
def of_sigma : (Σ a : α, β a → W_type β) → W_type β
| ⟨a, f⟩ := W_type.mk a f

@[simp] lemma of_sigma_to_sigma : Π (w : W_type β),
  of_sigma (to_sigma w) = w
| ⟨a, f⟩ := rfl

@[simp] lemma to_sigma_of_sigma : Π (s : Σ a : α, β a → W_type β),
  to_sigma (of_sigma s) = s
| ⟨a, f⟩ := rfl

variable (β)

/-- The canonical bijection with the sigma type, showing that `W_type` is a fixed point of
  the polynomial `Σ a : α, β a → W_type β`.  -/
@[simps] def equiv_sigma : W_type β ≃ Σ a : α, β a → W_type β :=
{ to_fun := to_sigma,
  inv_fun := of_sigma,
  left_inv := of_sigma_to_sigma,
  right_inv := to_sigma_of_sigma }

variable {β}

/-- The canonical map from `W_type β` into any type `γ` given a map `(Σ a : α, β a → γ) → γ`. -/
def elim (γ : Type*) (fγ : (Σ a : α, β a → γ) → γ) : W_type β → γ
| ⟨a, f⟩ := fγ ⟨a, λ b, elim (f b)⟩

lemma elim_injective (γ : Type*) (fγ : (Σ a : α, β a → γ) → γ)
  (fγ_injective : function.injective fγ) :
  function.injective (elim γ fγ)
| ⟨a₁, f₁⟩ ⟨a₂, f₂⟩ h := begin
  obtain ⟨rfl, h⟩ := sigma.mk.inj (fγ_injective h),
  congr' with x,
  exact elim_injective (congr_fun (eq_of_heq h) x : _),
end

instance [hα : is_empty α] : is_empty (W_type β) :=
⟨λ w, W_type.rec_on w (is_empty.elim hα)⟩

lemma infinite_of_nonempty_of_is_empty (a b : α) [ha : nonempty (β a)]
  [he : is_empty (β b)] : infinite (W_type β) :=
⟨begin
  introsI hf,
  have hba : b ≠ a, from λ h, ha.elim (is_empty.elim' (show is_empty (β a), from h ▸ he)),
  refine not_injective_infinite_fintype
    (λ n : ℕ, show W_type β, from nat.rec_on n
      ⟨b, is_empty.elim' he⟩
      (λ n ih, ⟨a, λ _, ih⟩)) _,
  intros n m h,
  induction n with n ih generalizing m h,
  { cases m with m; simp * at * },
  { cases m with m,
    { simp * at * },
    { refine congr_arg nat.succ (ih _),
      simp [function.funext_iff, *] at * } }
end⟩

variables [Π a : α, fintype (β a)]

/-- The depth of a finitely branching tree. -/
def depth : W_type β → ℕ
| ⟨a, f⟩ := finset.sup finset.univ (λ n, depth (f n)) + 1

lemma depth_pos (t : W_type β) : 0 < t.depth :=
by { cases t, apply nat.succ_pos }

lemma depth_lt_depth_mk (a : α) (f : β a → W_type β) (i : β a) :
  depth (f i) < depth ⟨a, f⟩ :=
nat.lt_succ_of_le (finset.le_sup (finset.mem_univ i))

end W_type

/-
Show that W types are encodable when `α` is an encodable fintype and for every `a : α`, `β a` is
encodable.

We define an auxiliary type `W_type' β n` of trees of depth at most `n`, and then we show by
induction on `n` that these are all encodable. These auxiliary constructions are not interesting in
and of themselves, so we mark them as `private`.
-/

namespace encodable

@[reducible] private def W_type' {α : Type*} (β : α → Type*)
    [Π a : α, fintype (β a)] [Π a : α, encodable (β a)] (n : ℕ) :=
{ t : W_type β // t.depth ≤ n}

variables {α : Type*} {β : α → Type*} [Π a : α, fintype (β a)] [Π a : α, encodable (β a)]

private def encodable_zero : encodable (W_type' β 0) :=
let f    : W_type' β 0 → empty := λ ⟨x, h⟩, false.elim $ not_lt_of_ge h (W_type.depth_pos _),
    finv : empty → W_type' β 0 := by { intro x, cases x} in
have ∀ x, finv (f x) = x, from λ ⟨x, h⟩, false.elim $ not_lt_of_ge h (W_type.depth_pos _),
encodable.of_left_inverse f finv this

private def f (n : ℕ) : W_type' β (n + 1) → Σ a : α, β a → W_type' β n
| ⟨t, h⟩ :=
  begin
    cases t with a f,
    have h₀ : ∀ i : β a, W_type.depth (f i) ≤ n,
      from λ i, nat.le_of_lt_succ (lt_of_lt_of_le (W_type.depth_lt_depth_mk a f i) h),
    exact ⟨a, λ i : β a, ⟨f i, h₀ i⟩⟩
  end

private def finv (n : ℕ) :
  (Σ a : α, β a → W_type' β n) → W_type' β (n + 1)
| ⟨a, f⟩ :=
  let f' := λ i : β a, (f i).val in
  have W_type.depth ⟨a, f'⟩ ≤ n + 1,
    from add_le_add_right (finset.sup_le (λ b h, (f b).2)) 1,
  ⟨⟨a, f'⟩, this⟩

variables [encodable α]

private def encodable_succ (n : nat) (h : encodable (W_type' β n)) :
  encodable (W_type' β (n + 1)) :=
encodable.of_left_inverse (f n) (finv n) (by { rintro ⟨⟨_, _⟩, _⟩, refl })

/-- `W_type` is encodable when `α` is an encodable fintype and for every `a : α`, `β a` is
encodable. -/
instance : encodable (W_type β) :=
begin
  haveI h' : Π n, encodable (W_type' β n) :=
    λ n, nat.rec_on n encodable_zero encodable_succ,
  let f    : W_type β → Σ n, W_type' β n   := λ t, ⟨t.depth, ⟨t, le_refl _⟩⟩,
  let finv : (Σ n, W_type' β n) → W_type β := λ p, p.2.1,
  have : ∀ t, finv (f t) = t, from λ t, rfl,
  exact encodable.of_left_inverse f finv this
end

end encodable
