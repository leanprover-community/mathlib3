/-
Copyright (c) 2021 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Violeta Hernández Palacios
-/
import set_theory.ordinal_arithmetic
import tactic.by_contra

/-!
# Veblen's functions

In this file, we prove Veblen's fixed point lemma, and use it to build the two-argument Veblen
function.

## Main definitions

- `enum_ord.order_iso`: an order isomorphism between the ordinals and an unbounded subset
-/

universes u v

namespace ordinal
section

/-- Bounded least upper bound. -/
-- Todo(Vi): this should be moved into `ordinal_arithmetic.lean`. We could complement it with a
-- `lub` function.
noncomputable def blub (o : ordinal.{u}) (f : Π a < o, ordinal.{max u v}) : ordinal.{max u v} :=
bsup o (λ a ha, (f a ha).succ)

theorem blub_le_iff_lt {o f a} : blub.{u v} o f ≤ a ↔ ∀ i h, f i h < a :=
by { convert bsup_le, apply propext, simp [succ_le] }

theorem lt_blub {o} (f : Π a < o, ordinal) (i h) : f i h < blub o f :=
blub_le_iff_lt.1 (le_refl _) _ _

variables {S : set ordinal.{u}} (hS : ∀ α, ∃ β, S β ∧ α ≤ β)

/-- Enumerator function for an unbounded set of ordinals. For the subtype variant, see `enum_ord`.
-/
noncomputable def enum_ord' : ordinal.{u} → ordinal.{u} :=
wf.fix (λ α f, omin _ (hS (blub.{u u} α f)))

/-- The equation that characterizes `enum_ord'` definitionally. This isn't the nicest expression to
work with, consider using `enum_ord'_def` instead. -/
theorem enum_ord'_def' (α) :
  enum_ord' hS α = omin (λ β, S β ∧ blub.{u u} α (λ γ _, enum_ord' hS γ) ≤ β) (hS _) :=
wf.fix_eq _ _

private theorem enum_ord'_mem_aux (α) :
  S (enum_ord' hS α) ∧ blub.{u u} α (λ γ _, enum_ord' hS γ) ≤ (enum_ord' hS α) :=
by { rw enum_ord'_def', exact omin_mem (λ _, _ ∧ _) _ }

theorem enum_ord'_mem (α) : enum_ord' hS α ∈ S := (enum_ord'_mem_aux hS α).left

theorem blub_le_enum_ord' (α) : blub.{u u} α (λ γ _, enum_ord' hS γ) ≤ enum_ord' hS α :=
(enum_ord'_mem_aux hS α).right

theorem enum_ord'.strict_mono {hS : ∀ α, ∃ β, S β ∧ α ≤ β} : strict_mono (enum_ord' hS) :=
λ _ _ h, lt_of_lt_of_le (lt_blub.{u u} _ _ h) (blub_le_enum_ord' hS _)

private theorem aux (α) : ∃ (β : ordinal), S β ∧ ∀ (γ : ordinal), γ < α → enum_ord' hS γ < β :=
by { refine ⟨enum_ord' hS α ,enum_ord'_mem hS α, λ _, _⟩, apply enum_ord'.strict_mono }

-- Explicitly specifying hS' screws up simp_rw for whatever reason.
private theorem enum_ord'_def_aux (α) {hS'} :
  enum_ord' hS α = omin (λ β, S β ∧ ∀ γ, γ < α → enum_ord' hS γ < β) (hS') :=
begin
  suffices : (λ β, S β ∧ blub.{u u} α (λ γ _, enum_ord' hS γ) ≤ β) =
    (λ β, S β ∧ ∀ γ, γ < α → enum_ord' hS γ < β),
  { rw enum_ord'_def',
    simp_rw this },
  apply funext (λ β, propext _),
  exact ⟨ λ ⟨hl, hr⟩, ⟨hl, λ _ h, lt_of_lt_of_le (lt_blub.{u u} _ _ h) hr⟩,
    λ ⟨hl, hr⟩, ⟨hl, blub_le_iff_lt.2 hr⟩ ⟩,
end

/-- A more workable definition for `enum_ord'`. -/
theorem enum_ord'_def (α) :
  enum_ord' hS α = omin (λ β, S β ∧ ∀ γ, γ < α → enum_ord' hS γ < β) (aux hS α) :=
enum_ord'_def_aux hS α

private theorem enum_ord'_lt_aux (α) :
  S (enum_ord' hS α) ∧ ∀ γ, γ < α → enum_ord' hS γ < (enum_ord' hS α) :=
by { rw enum_ord'_def, exact omin_mem (λ _, _ ∧ _) _ }

theorem enum_ord'_lt (α) : ∀ γ, γ < α → enum_ord' hS γ < enum_ord' hS α :=
(enum_ord'_lt_aux hS α).right

/-- Enumerator function for an unbounded set of ordinals. -/
noncomputable def enum_ord : ordinal.{u} → S := λ α, ⟨_, enum_ord'_mem hS α⟩

theorem enum_ord.strict_mono {hS : ∀ α, ∃ β, S β ∧ α ≤ β} : strict_mono (enum_ord hS) :=
enum_ord'.strict_mono

theorem aux (α) : α ≤ enum_ord hS α := wf.self_le_of_strict_mono enum_ord'.strict_mono  _

theorem enum_ord.surjective {hS : ∀ α, ∃ β, S β ∧ α ≤ β} : function.surjective (enum_ord hS) :=
begin
  have Swf : well_founded ((<) : S → S → Prop) := inv_image.wf _ wf,
  by_contra' H,
  let α := Swf.min _ H,
  let γ : ordinal.{u} := omin (λ β, α ≤ enum_ord hS β) ⟨_, aux hS α⟩,
  suffices : enum_ord hS γ = α,
  { exact Swf.min_mem _ H γ this },
  apply subtype.eq,
  change (enum_ord hS γ).val with enum_ord' hS γ,
  rw enum_ord'_def,
  apply le_antisymm,
  { refine omin_le ⟨α.prop, λ β hβ, _⟩,
    by_contra' h,
    exact not_lt_of_le (omin_le h : γ ≤ β) hβ },
  rw le_omin,
  rintros β ⟨hβl, hβr⟩,
  by_contra' hαβ,
  suffices : ∀ δ, enum_ord hS δ ≠ ⟨β, hβl⟩,
  { exact Swf.not_lt_min _ H this hαβ },
  by_contra' h,
  cases h with δ hδβ,
  refine (ne_of_lt (hβr δ _)) (subtype.mk.inj hδβ),
  by_contra' h,
  apply not_le_of_lt hαβ,
  have := le_trans (omin_mem (λ _, α ≤ _) _ : α ≤ _) (enum_ord.strict_mono.monotone h),
  rwa hδβ at this,
end

noncomputable def enum_ord.order_iso : ordinal.{u} ≃o S :=
strict_mono.order_iso_of_surjective (enum_ord hS) enum_ord.strict_mono enum_ord.surjective

end
end ordinal

section
variable (f : ordinal.{u} → ordinal.{u})

/-- The subtype of fixed points of a function. -/
def fixed_points : Type (u + 1) := {x // f x = x}

noncomputable instance : preorder (fixed_points f) := subtype.preorder _

instance : partial_order (fixed_points f) := subtype.partial_order _

noncomputable instance : linear_order (fixed_points f) := subtype.linear_order _

end

section
variable {f : ordinal.{u} → ordinal.{u}}

/-- An explicit fixed point for a normal function. For the subtype variant, see `fix_point`. -/
noncomputable def fix_point' (hf : ordinal.is_normal f) (α : ordinal.{u}) : ordinal.{u} :=
ordinal.sup.{0 u} (λ n, f^[n] α)

/-- An explicit fixed point for a normal function. Built as `sup {f^[n] α}`. This is guaranteed to
be at least `α`. -/
noncomputable def fix_point (hf : ordinal.is_normal f) (α : ordinal.{u}) : fixed_points f :=
⟨ fix_point' hf α, begin
  let g := λ n, f^[n] α,
  have H : ∀ {n}, g (n + 1) = (f ∘ g) n := λ n, function.iterate_succ_apply' f n α,
  have H' : ∀ {n}, g (n + 1) ≤ ordinal.sup.{0 u} (f ∘ g) := λ _, by {rw H, apply ordinal.le_sup},
  suffices : ordinal.sup.{0 u} (f ∘ g) = ordinal.sup.{0 u} g,
  { unfold fix_point',
    rwa @ordinal.is_normal.sup.{0 u u} f hf ℕ g (nonempty.intro 0) },
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
    exact ordinal.wf.self_le_of_strict_mono hf.strict_mono _ },
  exact H'
end ⟩

variable (hf : ordinal.is_normal f)

theorem self_le_fix_point (α : ordinal.{u}) : α ≤ (fix_point hf α).val :=
ordinal.le_sup _ 0

/-- Veblen's fixed point lemma: every normal function has arbitrarily large fixed points. -/
theorem fix_point_lemma : ∀ α, ∃ β, f β = β ∧ α ≤ β :=
λ α, ⟨_, (fix_point hf α).prop, self_le_fix_point hf α⟩

theorem fix_point.nonempty : nonempty (fixed_points f) :=
⟨fix_point hf 0⟩

/-- The fixed point enumerator of a normal function. For the subtype variant, see `fix_point_enum`.
-/
noncomputable def fix_point_enum' : ordinal.{u} → ordinal.{u} :=
ordinal.enum_ord' (fix_point_lemma hf)

/-- The fixed point enumerator of a normal function. -/
noncomputable def fix_point_enum : ordinal.{u} → fixed_points f :=
ordinal.enum_ord (λ α, ⟨_, (fix_point hf α).prop, self_le_fix_point hf α⟩)

theorem fix_point_enum'.strict_mono {hf : ordinal.is_normal f} : strict_mono (fix_point_enum' hf) :=
ordinal.enum_ord.strict_mono

theorem fix_point_enum.strict_mono {hf : ordinal.is_normal f} : strict_mono (fix_point_enum hf) :=
ordinal.enum_ord.strict_mono

theorem fix_point_enum.surjective {hf : ordinal.is_normal f} :
  function.surjective (fix_point_enum hf) :=
ordinal.enum_ord.surjective

noncomputable def fix_point_enum.order_iso {hf : ordinal.is_normal f} :
  ordinal.{u} ≃o (fixed_points f) :=
fix_point_enum.strict_mono.order_iso_of_surjective (fix_point_enum hf) fix_point_enum.surjective

/-- The fixed point enumerator is normal. This is what allows us to build Veblen's function. -/
theorem fix_point_enum.is_normal : ordinal.is_normal (fix_point_enum' hf) :=
begin
  use λ α, fix_point_enum'.strict_mono (ordinal.lt_succ_self α),
  intros α hα β,
  use λ hαβ γ hγα, le_of_lt (lt_of_lt_of_le (fix_point_enum'.strict_mono hγα) hαβ),
  intros h,
  sorry
end

end
