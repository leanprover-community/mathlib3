/-
Copyright (c) 2021 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Violeta Hernández Palacios
-/
import set_theory.ordinal_arithmetic
import tactic.by_contra

/-!
# Veblen's lemma

In this file, we prove Veblen's fixed point lemma: every normal ordinal function has arbitrarily
large fixed points. This allows us to build an ordinal function that enumer ate

TODO: build the two-argument Veblen function.

## Main definitions

- `enum_ord.order_iso`: an order isomorphism between the ordinals and an unbounded subset of them.

## Main results

- `fix_point_enum'.is_normal`: the fixed point enumerator of a normal function is normal.
-/

universes u v

open function

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

variables {S : set ordinal.{u}} (hS : ∀ a, ∃ b, S b ∧ a ≤ b)

/-- Enumerator function for an unbounded set of ordinals. For the subtype variant, see `enum_ord`.
-/
noncomputable def enum_ord' : ordinal.{u} → ordinal.{u} :=
wf.fix (λ a f, omin _ (hS (blub.{u u} a f)))

/-- The equation that characterizes `enum_ord'` definitionally. This isn't the nicest expression to
work with, so consider using `enum_ord'_def` instead. -/
theorem enum_ord'_def' (o) :
  enum_ord' hS o = omin (λ b, S b ∧ blub.{u u} o (λ c _, enum_ord' hS c) ≤ b) (hS _) :=
wf.fix_eq _ _

private theorem enum_ord'_mem_aux (o) :
  S (enum_ord' hS o) ∧ blub.{u u} o (λ c _, enum_ord' hS c) ≤ (enum_ord' hS o) :=
by { rw enum_ord'_def', exact omin_mem (λ _, _ ∧ _) _ }

theorem enum_ord'_mem (o) : enum_ord' hS o ∈ S := (enum_ord'_mem_aux hS o).left

theorem blub_le_enum_ord' (a) : blub.{u u} a (λ c _, enum_ord' hS c) ≤ enum_ord' hS a :=
(enum_ord'_mem_aux hS a).right

theorem enum_ord'.strict_mono {hS : ∀ a, ∃ b, S b ∧ a ≤ b} : strict_mono (enum_ord' hS) :=
λ _ _ h, lt_of_lt_of_le (lt_blub.{u u} _ _ h) (blub_le_enum_ord' hS _)

-- Explicitly specifying hS' screws up `rw` for whatever reason.
private theorem enum_ord'_def_aux (a) {hS'} :
  enum_ord' hS a = omin (λ b, S b ∧ ∀ c, c < a → enum_ord' hS c < b) (hS') :=
begin
  suffices : (λ b, S b ∧ blub.{u u} a (λ c _, enum_ord' hS c) ≤ b) =
    (λ b, S b ∧ ∀ c, c < a → enum_ord' hS c < b),
  { rw enum_ord'_def',
    simp_rw this },
  apply funext (λ _, propext _),
  exact ⟨ λ ⟨hl, hr⟩, ⟨hl, λ _ h, lt_of_lt_of_le (lt_blub.{u u} _ _ h) hr⟩,
    λ ⟨hl, hr⟩, ⟨hl, blub_le_iff_lt.2 hr⟩ ⟩,
end

/-- A more workable definition for `enum_ord'`. -/
theorem enum_ord'_def (o) :
  enum_ord' hS o = omin (λ b, S b ∧ ∀ c, c < o → enum_ord' hS c < b)
  (⟨_, enum_ord'_mem hS o, λ _ b, enum_ord'.strict_mono b⟩) :=
enum_ord'_def_aux hS o

/-- Enumerator function for an unbounded set of ordinals. -/
noncomputable def enum_ord : ordinal.{u} → S := λ o, ⟨_, enum_ord'_mem hS o⟩

theorem enum_ord.strict_mono : strict_mono (enum_ord hS) :=
enum_ord'.strict_mono

-- rewrite in terms of enum_ord' hS
theorem enum_ord.surjective : function.surjective (enum_ord hS) :=
begin
  have Swf : well_founded ((<) : S → S → Prop) := inv_image.wf _ wf,
  by_contra' H,
  let a := Swf.min _ H,
  let c : ordinal.{u} := omin (λ b, a ≤ enum_ord hS b)
    ⟨_, well_founded.self_le_of_strict_mono (inv_image.wf _ wf) (enum_ord'.strict_mono) _⟩,
  suffices : enum_ord hS c = a,
  { exact Swf.min_mem _ H c this },
  apply subtype.eq,
  change (enum_ord hS c).val with enum_ord' hS c,
  rw enum_ord'_def,
  apply le_antisymm,
  { refine omin_le ⟨a.prop, λ b hb, _⟩,
    by_contra' h,
    exact not_lt_of_le (omin_le h : c ≤ b) hb },
  rw le_omin,
  rintros b ⟨hbl, hbr⟩,
  by_contra' hab,
  suffices : ∀ d, enum_ord hS d ≠ ⟨b, hbl⟩,
  { exact Swf.not_lt_min _ H this hab },
  by_contra' h,
  cases h with d hdb,
  refine (ne_of_lt (hbr d _)) (subtype.mk.inj hdb),
  by_contra' h,
  apply not_le_of_lt hab,
  have := le_trans (omin_mem (λ _, a ≤ _) _ : a ≤ _) ((enum_ord.strict_mono hS).monotone h),
  rwa hdb at this,
end

/-- An order isomorphism between an unbounded set of ordinals and the ordinals. -/
noncomputable def enum_ord.order_iso : ordinal.{u} ≃o S :=
strict_mono.order_iso_of_surjective (enum_ord hS) (enum_ord.strict_mono _) (enum_ord.surjective _)

end
end ordinal

section
variable {f : ordinal.{u} → ordinal.{u}}

/-- An explicit fixed point for a normal function. For the subtype variant, see `fix_point`. -/
noncomputable def fix_point' (hf : ordinal.is_normal f) (o) : ordinal.{u} :=
ordinal.sup.{0 u} (λ n, f^[n] o)

/-- An explicit fixed point for a normal function, built as `sup (λ n, f^[n] o)`. -/
noncomputable def fix_point (hf : ordinal.is_normal f) (o) : fixed_points f :=
⟨ fix_point' hf o, begin
  let g := λ n, f^[n] o,
  have H : ∀ n, g (n + 1) = (f ∘ g) n := λ n, function.iterate_succ_apply' f n o,
  have H' : ∀ n, g (n + 1) ≤ ordinal.sup.{0 u} (f ∘ g) := λ _, by {rw H, exact ordinal.le_sup _ _},
  suffices : ordinal.sup.{0 u} (f ∘ g) = ordinal.sup g,
  { change f (ordinal.sup.{0 u} _) = (ordinal.sup.{0 u} _),
    rwa ordinal.is_normal.sup.{0 u u} hf ⟨0⟩ },
  apply has_le.le.antisymm;
  rw ordinal.sup_le;
  intro n,
  { rw ←H,
    exact ordinal.le_sup _ _ },
  cases n,
  exact le_trans (function.well_founded.self_le_of_strict_mono ordinal.wf hf.strict_mono _) (H' 0),
  exact H' n,
end ⟩

variable (hf : ordinal.is_normal f)

theorem self_le_fix_point (o) : o ≤ fix_point' hf o := ordinal.le_sup _ 0

/-- Veblen's fixed point lemma: every normal function has arbitrarily large fixed points. -/
theorem fix_point_lemma : ∀ a, ∃ b, f b = b ∧ a ≤ b :=
λ a, ⟨_, (fix_point hf a).prop, self_le_fix_point hf a⟩

theorem fixed_points.nonempty : nonempty (fixed_points f) := ⟨fix_point hf 0⟩

/-- The fixed point enumerator of a normal function. For the subtype variant, see `fix_point_enum`.
-/
noncomputable def fix_point_enum' : ordinal.{u} → ordinal.{u} :=
ordinal.enum_ord' (fix_point_lemma hf)

/-- The fixed point enumerator of a normal function. -/
noncomputable def fix_point_enum : ordinal.{u} → fixed_points f :=
ordinal.enum_ord (λ a, ⟨_, (fix_point hf a).prop, self_le_fix_point hf a⟩)

theorem fix_point_enum'.strict_mono : strict_mono (fix_point_enum' hf) :=
ordinal.enum_ord.strict_mono _

theorem fix_point_enum.strict_mono : strict_mono (fix_point_enum hf) :=
ordinal.enum_ord.strict_mono _

theorem fix_point_enum.surjective : function.surjective (fix_point_enum hf) :=
ordinal.enum_ord.surjective _

noncomputable def fix_point_enum.order_iso {hf : ordinal.is_normal f} :
  ordinal.{u} ≃o (fixed_points f) :=
(fix_point_enum.strict_mono _).order_iso_of_surjective _ (fix_point_enum.surjective hf)

/-- The supremum of a set of fixed points is also a fixed point.-/
theorem fixed_point_bsup {a : ordinal.{u}} (ha : a ≠ 0) (hf : ordinal.is_normal f)
(g : Π b, b < a → fixed_points f) :
  f (ordinal.bsup.{u u} a (λ b hb, (g b hb).val)) = ordinal.bsup.{u u} a (λ b hb, (g b hb).val) :=
begin
  let g' := (λ b hb, (g b hb).val),
  rw ordinal.is_normal.bsup.{u u u} hf g' ha,
  have : ∀ b hb, f (g' b hb) = (g b hb).val := λ b hb, (g b hb).prop,
  simp_rw this
end

/-- The fixed point enumerator is normal. This is what allows us to build Veblen's function. -/
theorem fix_point_enum'.is_normal : ordinal.is_normal (fix_point_enum' hf) :=
begin
  refine ⟨λ a, fix_point_enum'.strict_mono hf (ordinal.lt_succ_self a), λ a ha b,
    ⟨λ hab c hca, le_of_lt (lt_of_lt_of_le (fix_point_enum'.strict_mono hf hca) hab), λ h, _⟩⟩,
  let c := ordinal.bsup.{u u} a (λ b hb, (fix_point_enum hf b).val),
  have hc := fixed_point_bsup ha.1 hf _,
  suffices : fix_point_enum' hf a ≤ c,
  { exact le_trans this (ordinal.bsup_le.2 h) },
  cases fix_point_enum.surjective hf ⟨c, hc⟩ with d hd,
  have hdc := subtype.mk.inj hd,
  rw ←hdc,
  apply (fix_point_enum'.strict_mono hf).monotone,
  by_contra' had,
  have : _ < c := lt_of_lt_of_le
    (fix_point_enum'.strict_mono hf (ordinal.lt_succ_self d))
    (ordinal.le_bsup.{u u} (λ b hb, (fix_point_enum hf b).val) d.succ (ha.2 d had)),
  rw ←hdc at this,
  exact (lt_irrefl _) this
end

end
