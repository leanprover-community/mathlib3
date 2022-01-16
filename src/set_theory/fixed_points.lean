/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import set_theory.ordinal_arithmetic

/-!
# Fixed points of normal functions

We prove various statements about the fixed points of normal ordinal functions. We state them in
three forms: as statements about type-indexed families of normal functions, as statements about
ordinal-indexed families of normal functions, and as statements about a single normal function. For
the most part, the first case encompasses the others.

## Main definitions and results

* `nfp_family`, `nfp_bfamily`, `nfp`: the next fixed point of a (family of) normal function(s).
* `nfp_family_unbounded`, `nfp_bfamily_unbounded`, `nfp_unbounded`: the (common) fixed points of a
(family of) normal function(s) are unbounded in the ordinals.
-/

noncomputable theory

universes u v

namespace ordinal

/-! ### Fixed points of type-indexed families of ordinals -/

section
variable {ι : Type u}

/-- Applies the functions specified by the indices of a list, in order, to a specified value. -/
def nfp_family_iterate (f : ι → ordinal → ordinal) (a : ordinal) : list ι → ordinal
| []       := a
| (i :: l) := f i (nfp_family_iterate l)

theorem nfp_family_iterate_nil (f : ι → ordinal → ordinal) (a) : nfp_family_iterate f a [] = a :=
rfl

theorem nfp_family_iterate_append (f : ι → ordinal → ordinal) (i l a) :
  nfp_family_iterate f a (i :: l) = f i (nfp_family_iterate f a l) :=
rfl

theorem nfp_family_iterate_empty [is_empty ι] (f : ι → ordinal → ordinal) (a) :
  Π l : list ι, nfp_family_iterate f a l = a
| []       := rfl
| (i :: l) := is_empty_elim i

theorem nfp_family_iterate_fixed {f : ι → ordinal → ordinal} {a} (ha : ∀ i, f i a = a) :
  Π l : list ι, nfp_family_iterate f a l = a
| []       := rfl
| (i :: l) := by { convert ha i, exact congr_arg (f i) (nfp_family_iterate_fixed l) }

/-- The next common fixed point above `a` for a family of normal functions. -/
def nfp_family (f : ι → ordinal → ordinal) (a) : ordinal :=
sup (nfp_family_iterate f a)

theorem iterate_le_nfp_family (f : ι → ordinal → ordinal) (a l) :
  nfp_family_iterate f a l ≤ nfp_family f a :=
le_sup _ _

theorem le_nfp_family_self (f : ι → ordinal → ordinal) (a) : a ≤ nfp_family f a :=
le_sup _ []

theorem lt_nfp_family [hι : nonempty ι] {f : ι → ordinal → ordinal} (H : ∀ i, is_normal (f i))
  {a b} : (∀ i, f i b < nfp_family f a) ↔ b < nfp_family f a :=
begin
  unfold nfp_family,
  rw lt_sup,
  refine ⟨λ h, _, λ ⟨l, hl⟩ i, lt_sup.2 ⟨i :: l, (H i).strict_mono hl⟩⟩,
  unfreezingI { cases hι with i },
  have hi := h i,
  rw lt_sup at hi,
  cases hi with l hl,
  exact ⟨l, lt_of_le_of_lt ((H i).le_self b) hl⟩
end

theorem nfp_family_le [nonempty ι] {f : ι → ordinal → ordinal} (H : ∀ i, is_normal (f i)) {a b} :
  (∃ i, nfp_family f a ≤ f i b) ↔ nfp_family f a ≤ b :=
by { rw ←not_iff_not, push_neg, exact lt_nfp_family H }

theorem nfp_family_le_fp {f : ι → ordinal → ordinal} (H : ∀ i, is_normal (f i)) {a b} (ab : a ≤ b)
  (h : ∀ i, f i b ≤ b) : nfp_family f a ≤ b :=
sup_le.2 $ λ i, begin
  by_cases hι : is_empty ι,
  { rwa @nfp_family_iterate_empty ι hι },
  haveI := not_is_empty_iff.1 hι,
  induction i with i l IH generalizing a, {exact ab},
  exact ((H i).strict_mono.monotone (IH ab)).trans (h i)
end

theorem nfp_family_fp {f : ι → ordinal → ordinal} (H : ∀ i, is_normal (f i)) (i a) :
  f i (nfp_family f a) = nfp_family f a :=
begin
  unfold nfp_family,
  rw (H i).sup ⟨[]⟩,
  apply le_antisymm;
  rw ordinal.sup_le,
  { exact λ l, le_sup _ (i :: l) },
  { exact λ l, ((H i).le_self _).trans (le_sup _ _) }
end

theorem le_nfp_family [hι : nonempty ι] {f : ι → ordinal → ordinal} (H : ∀ i, is_normal (f i))
  {a b} : (∀ i, f i b ≤ nfp_family f a) ↔ b ≤ nfp_family f a :=
begin
  refine ⟨λ h, _, λ h i, _⟩,
  { unfreezingI { cases hι with i },
    exact ((H i).le_self b).trans (h i) },
  rw ←nfp_family_fp H i,
  exact (H i).strict_mono.monotone h
end

theorem nfp_family_eq_self {f : ι → ordinal → ordinal} {a} (h : ∀ i, f i a = a) :
  nfp_family f a = a :=
le_antisymm (sup_le.2 (λ l, (by rw nfp_family_iterate_fixed h))) (le_nfp_family_self f a)

/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
has an unbounded set of common fixed points. -/
theorem nfp_family_unbounded {f : ι → ordinal.{max u v} → ordinal.{max u v}}
  (H : ∀ i, is_normal (f i)) : unbounded (<) (⋂ i, function.fixed_points (f i)) :=
λ a, ⟨_, begin
  rintros S ⟨i, hi⟩,
  rw ←hi,
  exact nfp_family_fp H i a
end, not_lt_of_ge (le_nfp_family_self f a)⟩

/-- The derivative of a family of normal functions is the sequence of their common fixed points. -/
def deriv_family (f : ι → ordinal → ordinal) (o : ordinal) : ordinal :=
limit_rec_on o (nfp_family f 0)
  (λ a IH, nfp_family f (succ IH))
  (λ a l, bsup.{(max u v) u} a)

@[simp] theorem deriv_family_zero (f : ι → ordinal → ordinal) :
  deriv_family f 0 = nfp_family f 0 :=
limit_rec_on_zero _ _ _

@[simp] theorem deriv_family_succ (f : ι → ordinal → ordinal) (o) :
  deriv_family f (succ o) = nfp_family f (succ (deriv_family f o)) :=
limit_rec_on_succ _ _ _ _

theorem deriv_family_limit (f : ι → ordinal → ordinal) {o} : is_limit o →
  deriv_family f o = bsup.{(max u v) u} o (λ a _, deriv_family f a) :=
limit_rec_on_limit _ _ _ _

theorem deriv_family_is_normal (f : ι → ordinal → ordinal) : is_normal (deriv_family f) :=
⟨λ o, by rw [deriv_family_succ, ← succ_le]; apply le_nfp_family_self,
 λ o l a, by rw [deriv_family_limit _ l, bsup_le]⟩

theorem deriv_family_fp {f : ι → ordinal → ordinal} (H : ∀ i, is_normal (f i))
  (o : ordinal.{max u v}) (i) :
  f i (deriv_family f o) = deriv_family f o :=
begin
  apply limit_rec_on o,
  { rw [deriv_family_zero], exact nfp_family_fp H i 0 },
  { intros o ih, rw [deriv_family_succ], exact nfp_family_fp H i _ },
  intros o l IH,
  rw [deriv_family_limit _ l,
    is_normal.bsup.{(max u v) u (max u v)} (H i) (λ a _, deriv_family f a) l.1],
  refine eq_of_forall_ge_iff (λ c, _),
  simp only [bsup_le, IH] {contextual:=tt}
end

theorem le_iff_deriv_family {f : ι → ordinal → ordinal} (H : ∀ i, is_normal (f i)) {a} :
  (∀ i, f i a ≤ a) ↔ ∃ o, deriv_family f o = a :=
⟨λ ha, begin
  suffices : ∀ o (_ : a ≤ deriv_family f o), ∃ o, deriv_family f o = a,
  from this a ((deriv_family_is_normal _).le_self _),
  intro o, apply limit_rec_on o,
  { intros h₁,
    refine ⟨0, le_antisymm _ h₁⟩,
    rw deriv_family_zero,
    exact nfp_family_le_fp H (ordinal.zero_le _) ha },
  { intros o IH h₁,
    cases le_or_lt a (deriv_family f o), {exact IH h},
    refine ⟨succ o, le_antisymm _ h₁⟩,
    rw deriv_family_succ,
    exact nfp_family_le_fp H (succ_le.2 h) ha },
  { intros o l IH h₁,
    cases eq_or_lt_of_le h₁, {exact ⟨_, h.symm⟩},
    rw [deriv_family_limit _ l, ← not_le, bsup_le, not_ball] at h,
    exact let ⟨o', h, hl⟩ := h in IH o' h (le_of_not_le hl) }
end, λ ⟨o, e⟩ i, e ▸ le_of_eq (deriv_family_fp H _ i)⟩

theorem fp_iff_deriv_family {f : ι → ordinal → ordinal} (H : ∀ i, is_normal (f i)) {a} :
  (∀ i, f i a = a) ↔ ∃ o, deriv_family f o = a :=
begin
  rw ←le_iff_deriv_family H,
  refine ⟨λ h i, le_of_eq (h i), λ h i, _⟩,
  rw ←(H i).le_iff_eq,
  exact h i
end

theorem deriv_family_eq_enum_ord {f : ι → ordinal → ordinal} (H : ∀ i, is_normal (f i)) :
  deriv_family f = enum_ord _ (nfp_family_unbounded H) :=
begin
  rw ←eq_enum_ord,
  use (deriv_family_is_normal f).strict_mono,
  rw set.range_eq_iff,
  refine ⟨_, λ a ha, _⟩,
  { rintros a S ⟨i, hi⟩,
    rw ←hi,
    exact deriv_family_fp H a i },
  rw set.mem_Inter at ha,
  rwa ←fp_iff_deriv_family H
end

end

/-! ### Fixed points of ordinal-indexed families of ordinals -/

/-- The next common fixed point above `a` for a family of normal functions indexed by ordinals. -/
def nfp_bfamily (o : ordinal) (f : Π b < o, ordinal → ordinal) : ordinal → ordinal :=
nfp_family (family_of_bfamily o f)

theorem le_nfp_bfamily_self {o : ordinal} (f : Π b < o, ordinal → ordinal) (a) :
  a ≤ nfp_bfamily o f a :=
le_nfp_family_self _ _

theorem lt_nfp_bfamily {o : ordinal} (ho : o ≠ 0) {f : Π b < o, ordinal → ordinal}
  (H : ∀ i hi, is_normal (f i hi)) {a b} :
  (∀ i hi, f i hi b < nfp_bfamily o f a) ↔ b < nfp_bfamily o f a :=
begin
  unfold nfp_bfamily,
  rw ←@lt_nfp_family _ (out_nonempty_iff_ne_zero.2 ho) (family_of_bfamily o f) (λ i, H _ _),
  refine ⟨λ h i, h _ (typein_lt_self i), λ h i hio, _⟩,
  rw ←family_of_bfamily_enum o f,
  apply h
end

theorem nfp_bfamily_le {o : ordinal} (ho : o ≠ 0) {f : Π b < o, ordinal → ordinal}
  (H : ∀ i hi, is_normal (f i hi)) {a b} :
  (∃ i hi, nfp_bfamily o f a ≤ f i hi b) ↔ nfp_bfamily o f a ≤ b :=
by { rw ←not_iff_not, push_neg, convert lt_nfp_bfamily ho H, simp }

theorem nfp_bfamily_le_fp {o} {f : Π b < o, ordinal → ordinal}
  (H : ∀ i hi, is_normal (f i hi)) {a b} (ab : a ≤ b) (h : ∀ i hi, f i hi b ≤ b) :
  nfp_bfamily o f a ≤ b :=
nfp_family_le_fp (λ _, H _ _) ab (λ i, h _ _)

theorem nfp_bfamily_fp {o} {f : Π b < o, ordinal → ordinal}
  (H : ∀ i hi, is_normal (f i hi)) (i hi a) :
  f i hi (nfp_bfamily o f a) = nfp_bfamily o f a :=
by { rw ←family_of_bfamily_enum o f, exact nfp_family_fp (λ i, H _ _) _ _ }

theorem le_nfp_bfamily {o : ordinal} (ho : o ≠ 0) {f : Π b < o, ordinal → ordinal}
  (H : ∀ i hi, is_normal (f i hi)) {a b} :
  (∀ i hi, f i hi b ≤ nfp_bfamily o f a) ↔ b ≤ nfp_bfamily o f a :=
begin
  refine ⟨λ h, _, λ h i hi, _⟩,
  { have ho' : 0 < o := ordinal.pos_iff_ne_zero.2 ho,
    exact ((H 0 ho').le_self b).trans (h 0 ho') },
  rw ←nfp_bfamily_fp H i,
  exact (H i hi).strict_mono.monotone h
end

theorem nfp_bfamily_eq_self {o} {f : Π b < o, ordinal → ordinal} {a} (h : ∀ i hi, f i hi a = a) :
  nfp_bfamily o f a = a :=
nfp_family_eq_self (λ _, h _ _)

/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
has an unbounded set of common fixed points. -/
theorem nfp_bfamily_unbounded {o : ordinal.{u}} {f : Π b < o, ordinal.{max u v} → ordinal.{max u v}}
  (H : ∀ i hi, is_normal (f i hi)) : unbounded (<) (⋂ i hi, function.fixed_points (f i hi)) :=
λ a, ⟨_, by { rw set.mem_Inter_Inter, exact λ _ _, nfp_bfamily_fp H _ _ _ },
  not_lt_of_ge (le_nfp_bfamily_self f a)⟩

/-- The derivative of a family of normal functions is the sequence of their common fixed points. -/
def deriv_bfamily (o : ordinal) (f : Π b < o, ordinal → ordinal) : ordinal → ordinal :=
deriv_family (family_of_bfamily o f)

theorem deriv_bfamily_is_normal {o : ordinal} (f : Π b < o, ordinal → ordinal) :
  is_normal (deriv_bfamily o f) :=
deriv_family_is_normal _

theorem deriv_bfamily_fp {o : ordinal} {f : Π b < o, ordinal → ordinal}
  (H : ∀ i hi, is_normal (f i hi)) (a : ordinal.{max u v}) (i hi) :
  f i hi (deriv_bfamily o f a) = deriv_bfamily o f a :=
begin
  rw ←family_of_bfamily_enum o f,
  exact deriv_family_fp (λ _, H _ _) _ _
end

theorem le_iff_deriv_bfamily {o : ordinal} {f : Π b < o, ordinal → ordinal}
  (H : ∀ i hi, is_normal (f i hi)) {a} : (∀ i hi, f i hi a ≤ a) ↔ ∃ b, deriv_bfamily o f b = a :=
begin
  unfold deriv_bfamily,
  rw ←le_iff_deriv_family,
  { refine ⟨λ h i, h _ _, λ h i hi, _⟩,
    rw ←family_of_bfamily_enum o f,
    apply h },
  exact λ _, H _ _
end

theorem fp_iff_deriv_bfamily {o : ordinal} {f : Π b < o, ordinal → ordinal}
  (H : ∀ i hi, is_normal (f i hi)) {a} : (∀ i hi, f i hi a = a) ↔ ∃ b, deriv_bfamily o f b = a :=
begin
  rw ←le_iff_deriv_bfamily H,
  refine ⟨λ h i hi, le_of_eq (h i hi), λ h i hi, _⟩,
  rw ←(H i hi).le_iff_eq,
  exact h i hi
end

theorem deriv_bfamily_eq_enum_ord {o : ordinal} {f : Π b < o, ordinal → ordinal}
  (H : ∀ i hi, is_normal (f i hi)) : deriv_bfamily o f = enum_ord _ (nfp_bfamily_unbounded H) :=
begin
  rw ←eq_enum_ord,
  use (deriv_bfamily_is_normal f).strict_mono,
  rw set.range_eq_iff,
  refine ⟨_, λ a ha, _⟩,
  { intro a,
    rw fixed_points_mem,
    exact deriv_bfamily_fp H a },
  rw fixed_points_mem at ha,
  rwa ←fp_iff_deriv_bfamily H
end

/-! ### Fixed points of a single function -/

/-- The next fixed point function, the least fixed point of the normal function `f` above `a`. -/
def nfp (f : ordinal → ordinal) : ordinal → ordinal :=
nfp_family (λ _ : unit, f)

theorem nfp_family_iterate_eq_iterate {ι : Type u} (f : ordinal → ordinal) (a) :
  Π l, nfp_family_iterate (λ _ : ι, f) a l = (f^[l.length]) a
| []       := rfl
| (i :: l) := begin
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

/-- The derivative of a normal function `f` is the sequence of fixed points of `f`. -/
def deriv (f : ordinal → ordinal) : ordinal → ordinal :=
deriv_family (λ _ : unit, f)

@[simp] theorem deriv_zero (f) : deriv f 0 = nfp f 0 :=
deriv_family_zero _

@[simp] theorem deriv_succ (f o) : deriv f (succ o) = nfp f (succ (deriv f o)) :=
deriv_family_succ _ _

theorem deriv_limit (f) {o} : is_limit o → deriv f o = bsup.{u 0} o (λ a _, deriv f a) :=
deriv_family_limit _

theorem deriv_is_normal (f) : is_normal (deriv f) :=
deriv_family_is_normal _

theorem is_normal.deriv_fp {f} (H : is_normal f) (o) : f (deriv f o) = deriv f o :=
deriv_family_fp (λ _, H) _ unit.star

theorem is_normal.le_iff_deriv {f} (H : is_normal f) {a} : f a ≤ a ↔ ∃ o, deriv f o = a :=
begin
  unfold deriv,
  rw ←le_iff_deriv_family (λ _ : unit, H),
  exact ⟨λ h _, h, λ h, h unit.star⟩
end

theorem is_normal.eq_iff_deriv {f} (H : is_normal f) {a} : f a = a ↔ ∃ o, deriv f o = a :=
by rw [←H.le_iff_eq, H.le_iff_deriv]

end ordinal
