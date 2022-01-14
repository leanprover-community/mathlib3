/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import set_theory.ordinal_arithmetic

noncomputable theory

universes u v

namespace ordinal

/-! ### Fixed points of type-indexed families of ordinals -/

/-- Applies the functions specified by the indices of the list, in order, to a specified value. -/
def nfp_family_iterate {ι : Type u} (f : ι → ordinal.{max u v} → ordinal.{max u v})
  (a : ordinal.{max u v}) : list ι → ordinal.{max u v}
| []       := a
| (i :: l) := f i (nfp_family_iterate l)

theorem nfp_family_iterate_nil {ι} (f : ι → ordinal → ordinal) (a) :
  nfp_family_iterate f a [] = a :=
rfl

theorem nfp_family_iterate_append {ι} (f : ι → ordinal → ordinal) (i l a) :
  nfp_family_iterate f a (i :: l) = f i (nfp_family_iterate f a l) :=
rfl

theorem nfp_family_iterate_empty {ι} [is_empty ι] (f : ι → ordinal.{max u v} → ordinal.{max u v})
  (a : ordinal.{max u v}) : Π l : list ι, nfp_family_iterate f a l = a
| []       := rfl
| (i :: l) := is_empty_elim i

theorem nfp_family_iterate_fixed {ι} {f : ι → ordinal.{max u v} → ordinal.{max u v}}
  {a : ordinal.{max u v}} (ha : ∀ i, f i a = a) : Π l : list ι, nfp_family_iterate f a l = a
| []       := rfl
| (i :: l) := by { convert ha i, exact congr_arg (f i) (nfp_family_iterate_fixed l) }

/-- The next common fixed point above `a` for a family of normal functions. -/
-- Todo: prove it's actually the next
def nfp_family {ι} (f : ι → ordinal → ordinal) (a) : ordinal :=
sup (nfp_family_iterate f a)

theorem iterate_le_nfp_family {ι} (f : ι → ordinal → ordinal) (a l) :
  nfp_family_iterate f a l ≤ nfp_family f a :=
le_sup _ _

theorem le_nfp_family_self {ι} (f : ι → ordinal → ordinal) (a) : a ≤ nfp_family f a :=
le_sup _ []

theorem lt_nfp_family {ι} [hι : nonempty ι] {f : ι → ordinal → ordinal}
(Hf : ∀ i, is_normal (f i)) {a b} :
  (∀ i, f i b < nfp_family f a) ↔ b < nfp_family f a :=
begin
  unfold nfp_family,
  rw lt_sup,
  refine ⟨λ h, _, λ ⟨l, hl⟩ i, lt_sup.2 ⟨i :: l, (Hf i).strict_mono hl⟩⟩,
  unfreezingI { cases hι with i },
  have hi := h i,
  rw lt_sup at hi,
  cases hi with l hl,
  exact ⟨l, lt_of_le_of_lt ((Hf i).le_self b) hl⟩
end

theorem nfp_family_le {ι} [nonempty ι] {f : ι → ordinal → ordinal} (Hf : ∀ i, is_normal (f i))
  {a b} :
  (∃ i, nfp_family f a ≤ f i b) ↔ nfp_family f a ≤ b :=
by { rw ←not_iff_not, push_neg, exact lt_nfp_family Hf }

theorem nfp_family_le_fp {ι} {f : ι → ordinal → ordinal} (Hf : ∀ i, is_normal (f i)) {a b}
  (ab : a ≤ b) (h : ∀ i, f i b ≤ b) :
  nfp_family f a ≤ b :=
sup_le.2 $ λ i, begin
  by_cases hι : is_empty ι,
  { rwa @nfp_family_iterate_empty ι hι },
  haveI := not_is_empty_iff.1 hι,
  induction i with i l IH generalizing a, {exact ab},
  exact ((Hf i).strict_mono.monotone (IH ab)).trans (h i)
end

theorem nfp_family_fp {ι} {f : ι → ordinal → ordinal} (Hf : ∀ i, is_normal (f i)) (i a) :
  f i (nfp_family f a) = (nfp_family f a) :=
begin
  unfold nfp_family,
  rw (Hf i).sup ⟨[]⟩,
  apply le_antisymm;
  rw ordinal.sup_le,
  { exact λ l, le_sup _ (i :: l) },
  { exact λ l, ((Hf i).le_self _).trans (le_sup _ _) }
end

theorem le_nfp_family {ι} [hι : nonempty ι] {f : ι → ordinal → ordinal} (Hf : ∀ i, is_normal (f i))
  {a b} : (∀ i, f i b ≤ nfp_family f a) ↔ b ≤ nfp_family f a :=
begin
  refine ⟨λ h, _, λ h i, _⟩,
  { unfreezingI { cases hι with i },
    exact ((Hf i).le_self b).trans (h i) },
  rw ←nfp_family_fp Hf i,
  exact (Hf i).strict_mono.monotone h
end

theorem nfp_family_eq_self {ι} {f : ι → ordinal → ordinal} {a} (h : ∀ i, f i a = a) :
  nfp_family f a = a :=
le_antisymm (sup_le.2 (λ l, (by rw nfp_family_iterate_fixed h))) (le_nfp_family_self f a)

/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
has an unbounded set of common fixed points. -/
theorem nfp_family_unbounded {ι : Type u} {f : ι → ordinal.{max u v} → ordinal.{max u v}}
  (Hf : ∀ i, is_normal (f i)) :
  unbounded (<) (⋂ i, function.fixed_points (f i)) :=
λ a, ⟨_, begin
  rintros S ⟨i, hi⟩,
  rw ←hi,
  exact nfp_family_fp Hf i a
end, not_lt_of_ge (le_nfp_family_self f a)⟩

theorem nfp_family_is_normal {ι} {f : ι → ordinal.{max u v} → ordinal} (Hf : ∀ i, is_normal (f i)) :
  is_normal (enum_ord _ (nfp_family_unbounded Hf)) :=
begin
  rw ←is_normal_iff_strict_mono_limit,
  use enum_ord.strict_mono _,
  intros a ha c b,
  sorry,
end


/-! ### Fixed points of ordinal-indexed families of ordinals -/

/-- The next common fixed point above `a` for a family of normal functions indexed by ordinals. -/
def nfp_bfamily (o : ordinal.{u}) (f : Π b < o, ordinal.{max u v} → ordinal.{max u v}) :
  ordinal.{max u v} → ordinal.{max u v} :=
nfp_family (family_of_bfamily o f)

/-! ### Fixed points of a single function -/

/-- The next fixed point function, the least fixed point of the normal function `f` above `a`. -/
def nfp (f : ordinal.{u} → ordinal.{u}) : ordinal.{u} → ordinal.{u} :=
nfp_family (λ _ : unit, f)

theorem nfp_family_iterate_eq_iterate {ι : Type u} (f : ordinal.{max u v} → ordinal.{max u v})
  (a : ordinal.{max u v}) :
  Π l : list ι, nfp_family_iterate.{u v} (λ _ : ι, f) a l = (f^[l.length]) a
| []       := rfl
| (i :: l) :=
begin
  convert congr_arg f (nfp_family_iterate_eq_iterate l),
  exact function.iterate_succ_apply' f _ a
end

theorem nfp_eq_sup_nat (f : ordinal.{u} → ordinal.{u}) :
  nfp f = λ a, sup (λ n : ℕ, f^[n] a) :=
begin
  refine funext (λ a, le_antisymm (sup_le.2 (λ l, _)) _),
  { rw nfp_family_iterate_eq_iterate.{0 u} f a l,
    exact le_sup _ _ },
  rw sup_le,
  intro n,
  rw [←list.length_repeat unit.star n, ←nfp_family_iterate_eq_iterate.{0 u} f a],
  exact le_sup _ _
end

theorem iterate_le_nfp (f a n) : f^[n] a ≤ nfp f a :=
by { rw nfp_eq_sup_nat, exact le_sup _ n }

theorem le_nfp_self (f a) : a ≤ nfp f a :=
iterate_le_nfp f a 0

theorem is_normal.lt_nfp {f} (H : is_normal f) {a b} :
  f b < nfp f a ↔ b < nfp f a :=
begin
  unfold nfp,
  rw ←@lt_nfp_family unit _ (λ _, f) (λ _, H) a b,
  exact ⟨λ h _, h, λ h, h unit.star⟩
end

theorem is_normal.nfp_le {f} (H : is_normal f) {a b} :
  nfp f a ≤ f b ↔ nfp f a ≤ b :=
le_iff_le_iff_lt_iff_lt.2 H.lt_nfp

theorem is_normal.nfp_le_fp {f} (H : is_normal f) {a b}
  (ab : a ≤ b) (h : f b ≤ b) : nfp f a ≤ b :=
nfp_family_le_fp (λ _, H) ab (λ _, h)

theorem is_normal.nfp_fp {f} (H : is_normal f) : ∀ a, f (nfp f a) = nfp f a :=
nfp_family_fp (λ _, H) unit.star

theorem is_normal.le_nfp {f} (H : is_normal f) {a b} :
  f b ≤ nfp f a ↔ b ≤ nfp f a :=
⟨le_trans (H.le_self _), λ h,
  by simpa only [H.nfp_fp] using H.le_iff.2 h⟩

theorem nfp_eq_self {f : ordinal → ordinal} {a} (h : f a = a) : nfp f a = a :=
nfp_family_eq_self (λ _, h)

/-- The derivative of a normal function `f` is
  the sequence of fixed points of `f`. -/
def deriv (f : ordinal → ordinal) (o : ordinal) : ordinal :=
limit_rec_on o (nfp f 0)
  (λ a IH, nfp f (succ IH))
  (λ a l, bsup.{u u} a)

@[simp] theorem deriv_zero (f) : deriv f 0 = nfp f 0 := limit_rec_on_zero _ _ _

@[simp] theorem deriv_succ (f o) : deriv f (succ o) = nfp f (succ (deriv f o)) :=
limit_rec_on_succ _ _ _ _

theorem deriv_limit (f) {o} : is_limit o →
  deriv f o = bsup.{u u} o (λ a _, deriv f a) :=
limit_rec_on_limit _ _ _ _

theorem deriv_is_normal (f) : is_normal (deriv f) :=
⟨λ o, by rw [deriv_succ, ← succ_le]; apply le_nfp_self,
 λ o l a, by rw [deriv_limit _ l, bsup_le]⟩

theorem is_normal.deriv_fp {f} (H : is_normal f) (o) : f (deriv.{u} f o) = deriv f o :=
begin
  apply limit_rec_on o,
  { rw [deriv_zero, H.nfp_fp] },
  { intros o ih, rw [deriv_succ, H.nfp_fp] },
  intros o l IH,
  rw [deriv_limit _ l, is_normal.bsup.{u u u} H _ l.1],
  refine eq_of_forall_ge_iff (λ c, _),
  simp only [bsup_le, IH] {contextual:=tt}
end

theorem is_normal.fp_iff_deriv {f} (H : is_normal f)
  {a} : f a ≤ a ↔ ∃ o, a = deriv f o :=
⟨λ ha, begin
  suffices : ∀ o (_:a ≤ deriv f o), ∃ o, a = deriv f o,
  from this a ((deriv_is_normal _).le_self _),
  intro o, apply limit_rec_on o,
  { intros h₁,
    refine ⟨0, le_antisymm h₁ _⟩,
    rw deriv_zero,
    exact H.nfp_le_fp (ordinal.zero_le _) ha },
  { intros o IH h₁,
    cases le_or_lt a (deriv f o), {exact IH h},
    refine ⟨succ o, le_antisymm h₁ _⟩,
    rw deriv_succ,
    exact H.nfp_le_fp (succ_le.2 h) ha },
  { intros o l IH h₁,
    cases eq_or_lt_of_le h₁, {exact ⟨_, h⟩},
    rw [deriv_limit _ l, ← not_le, bsup_le, not_ball] at h,
    exact let ⟨o', h, hl⟩ := h in IH o' h (le_of_not_le hl) }
end, λ ⟨o, e⟩, e.symm ▸ le_of_eq (H.deriv_fp _)⟩

end ordinal
