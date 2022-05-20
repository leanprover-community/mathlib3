/-
Copyright (c) 2018 Violeta Hernández Palacios, Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Mario Carneiro
-/

import set_theory.ordinal.arithmetic

/-!
# Fixed points of normal functions

We prove various statements about the fixed points of normal ordinal functions. We state them in
three forms: as statements about type-indexed families of normal functions, as statements about
ordinal-indexed families of normal functions, and as statements about a single normal function. For
the most part, the first case encompasses the others.

Moreover, we prove some lemmas about the fixed points of specific normal functions.

Finally, we define Veblen's two argument function `ordinal.veblen` starting from a given normal
function.

## Main definitions and results

* `ordinal.nfp_family`, `ordinal.nfp_bfamily`, `ordinal.nfp`: the next fixed point of a
  (family of) normal function(s).
* `ordinal.fp_family_unbounded`, `ordinal.fp_bfamily_unbounded`, `ordinal.fp_unbounded`: the
  (common) fixed points of a (family of) normal function(s) are unbounded in the ordinals.
* `ordinal.deriv_add_eq_mul_omega_add`: a characterization of the derivative of addition.
* `ordinal.deriv_mul_eq_opow_omega_mul`: a characterization of the derivative of multiplication.
-/

noncomputable theory

universes u v w

open function

namespace ordinal

/-! ### Fixed points of type-indexed families of ordinals -/

section
variables {ι : Type u} {ι' : Type w} {f : ι → ordinal.{max u v} → ordinal.{max u v}}

/-- The next common fixed point, at least `a`, for a family of normal functions.

`ordinal.nfp_family_fp` shows this is a fixed point, `ordinal.le_nfp_family` shows it's at
least `a`, and `ordinal.nfp_family_le_fp` shows this is the least ordinal with these properties. -/
def nfp_family (f : ι → ordinal → ordinal) (a) : ordinal :=
sup (list.foldr f a)

theorem nfp_family_eq_sup (f : ι → ordinal → ordinal) (a) :
  nfp_family f a = sup (list.foldr f a) :=
rfl

theorem foldr_le_nfp_family (f : ι → ordinal → ordinal) (a l) :
  list.foldr f a l ≤ nfp_family f a :=
le_sup _ _

theorem le_nfp_family (f : ι → ordinal → ordinal) (a) : a ≤ nfp_family f a :=
le_sup _ []

theorem lt_nfp_family {a b} : a < nfp_family f b ↔ ∃ l, a < list.foldr f b l :=
lt_sup

theorem nfp_family_le_iff {a b} : nfp_family f a ≤ b ↔ ∀ l, list.foldr f a l ≤ b :=
sup_le_iff

theorem nfp_family_le {a b} : (∀ l, list.foldr f a l ≤ b) → nfp_family f a ≤ b :=
sup_le

@[simp] theorem nfp_family_empty [is_empty ι] (f : ι → ordinal → ordinal) : nfp_family f = id :=
funext $ λ a, le_antisymm (nfp_family_le begin
  rintro (_ | i),
  { refl },
  { exact is_empty_elim i }
end) (le_nfp_family f a)

theorem nfp_family_monotone (hf : ∀ i, monotone (f i)) : monotone (nfp_family f) :=
λ a b h, sup_le $ λ l, (list.foldr_monotone hf l h).trans (le_sup _ l)

theorem apply_lt_nfp_family (H : ∀ i, is_normal (f i)) {a b} (hb : b < nfp_family f a) (i) :
  f i b < nfp_family f a :=
let ⟨l, hl⟩ := lt_nfp_family.1 hb in lt_sup.2 ⟨i :: l, (H i).strict_mono hl⟩

theorem apply_lt_nfp_family_iff [nonempty ι] (H : ∀ i, is_normal (f i)) {a b} :
  (∀ i, f i b < nfp_family f a) ↔ b < nfp_family f a :=
⟨λ h, lt_nfp_family.2 $ let ⟨l, hl⟩ := lt_sup.1 (h (classical.arbitrary ι)) in
  ⟨l, ((H _).self_le b).trans_lt hl⟩, apply_lt_nfp_family H⟩

theorem nfp_family_le_apply [nonempty ι] (H : ∀ i, is_normal (f i)) {a b} :
  (∃ i, nfp_family f a ≤ f i b) ↔ nfp_family f a ≤ b :=
by { rw ←not_iff_not, push_neg, exact apply_lt_nfp_family_iff H }

theorem nfp_family_le_of_range_subset {ι : Type u} {ι' : Type v} {f : ι → ordinal → ordinal}
  {g : ι' → ordinal → ordinal} (hfg : set.range f ⊆ set.range g) (a) :
  nfp_family.{u (max v w)} f a ≤ nfp_family.{v (max u w)} g a :=
sup_le_of_range_subset (list.foldr_range_subset_of_range_subset hfg a)

theorem nfp_family_eq_of_range_eq {ι : Type u} {ι' : Type v} {f : ι → ordinal → ordinal}
  {g : ι' → ordinal → ordinal} (hfg : set.range f = set.range g) :
  nfp_family.{u (max v w)} f = nfp_family.{v (max u w)} g :=
funext (λ a, sup_eq_of_range_eq (list.foldr_range_eq_of_range_eq hfg a))

theorem nfp_family_le_fp (H : ∀ i, monotone (f i)) {a b} (ab : a ≤ b) (h : ∀ i, f i b ≤ b) :
  nfp_family f a ≤ b :=
sup_le $ λ l, begin
  by_cases hι : is_empty ι,
  { rwa @unique.eq_default _ (@list.unique_of_is_empty ι hι) l },
  { haveI := not_is_empty_iff.1 hι,
    induction l with i l IH generalizing a, {exact ab},
    exact (H i (IH ab)).trans (h i) }
end

theorem nfp_family_fp {i} (H : is_normal (f i)) (a) : f i (nfp_family f a) = nfp_family f a :=
begin
  unfold nfp_family,
  rw @is_normal.sup _ H _ _ ⟨[]⟩,
  apply le_antisymm;
  refine ordinal.sup_le (λ l, _),
  { exact le_sup _ (i :: l) },
  { exact (H.self_le _).trans (le_sup _ _) }
end

theorem apply_le_nfp_family [hι : nonempty ι] {f : ι → ordinal → ordinal} (H : ∀ i, is_normal (f i))
  {a b} : (∀ i, f i b ≤ nfp_family f a) ↔ b ≤ nfp_family f a :=
begin
  refine ⟨λ h, _, λ h i, _⟩,
  { unfreezingI { cases hι with i },
    exact ((H i).self_le b).trans (h i) },
  rw ←nfp_family_fp (H i),
  exact (H i).monotone h
end

theorem nfp_family_eq_self {f : ι → ordinal → ordinal} {a} (h : ∀ i, f i a = a) :
  nfp_family f a = a :=
le_antisymm (sup_le (λ l, (by rw list.foldr_fixed' h l))) (le_nfp_family f a)

/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
theorem fp_family_unbounded (H : ∀ i, is_normal (f i)) :
  (⋂ i, function.fixed_points (f i)).unbounded (<) :=
λ a, ⟨_, λ s ⟨i, hi⟩, begin
  rw ←hi,
  exact nfp_family_fp (H i) a
end, (le_nfp_family f a).not_lt⟩

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
⟨λ o, by rw [deriv_family_succ, ← succ_le]; apply le_nfp_family,
 λ o l a, by rw [deriv_family_limit _ l, bsup_le_iff]⟩

theorem self_le_deriv_family (f : ι → ordinal → ordinal) : ∀ o, o ≤ deriv_family f o :=
(deriv_family_is_normal f).self_le

theorem deriv_family_fp {i} (H : is_normal (f i)) (o : ordinal.{max u v}) :
  f i (deriv_family f o) = deriv_family f o :=
begin
  refine limit_rec_on o _ (λ o IH, _) _,
  { rw [deriv_family_zero], exact nfp_family_fp H 0 },
  { rw [deriv_family_succ], exact nfp_family_fp H _ },
  { intros o l IH,
    rw [deriv_family_limit _ l,
      is_normal.bsup.{(max u v) u (max u v)} H (λ a _, deriv_family f a) l.1],
    refine eq_of_forall_ge_iff (λ c, _),
    simp only [bsup_le_iff, IH] {contextual:=tt} }
end

theorem le_iff_deriv_family (H : ∀ i, is_normal (f i)) {a} :
  (∀ i, f i a ≤ a) ↔ ∃ o, deriv_family f o = a :=
⟨λ ha, begin
  suffices : ∀ o (_ : a ≤ deriv_family f o), ∃ o, deriv_family f o = a,
  from this a ((deriv_family_is_normal _).self_le _),
  refine λ o, limit_rec_on o (λ h₁, ⟨0, le_antisymm _ h₁⟩) (λ o IH h₁, _) (λ o l IH h₁, _),
  { rw deriv_family_zero,
    exact nfp_family_le_fp (λ i, (H i).monotone) (ordinal.zero_le _) ha },
  { cases le_or_lt a (deriv_family f o), {exact IH h},
    refine ⟨succ o, le_antisymm _ h₁⟩,
    rw deriv_family_succ,
    exact nfp_family_le_fp (λ i, (H i).monotone) (succ_le.2 h) ha },
  { cases eq_or_lt_of_le h₁, {exact ⟨_, h.symm⟩},
    rw [deriv_family_limit _ l, ← not_le, bsup_le_iff, not_ball] at h,
    exact let ⟨o', h, hl⟩ := h in IH o' h (le_of_not_le hl) }
end, λ ⟨o, e⟩ i, e ▸ le_of_eq (deriv_family_fp (H i) _)⟩

theorem fp_iff_deriv_family (H : ∀ i, is_normal (f i)) {a} :
  (∀ i, f i a = a) ↔ ∃ o, deriv_family f o = a :=
iff.trans ⟨λ h i, le_of_eq (h i), λ h i, (H i).le_iff_eq.1 (h i)⟩ (le_iff_deriv_family H)

theorem deriv_family_eq_enum_ord (H : ∀ i, is_normal (f i)) :
  deriv_family f = enum_ord (⋂ i, function.fixed_points (f i)) :=
begin
  rw ←eq_enum_ord _ (fp_family_unbounded H),
  use (deriv_family_is_normal f).strict_mono,
  rw set.range_eq_iff,
  refine ⟨_, λ a ha, _⟩,
  { rintros a S ⟨i, hi⟩,
    rw ←hi,
    exact deriv_family_fp (H i) a },
  rw set.mem_Inter at ha,
  rwa ←fp_iff_deriv_family H
end

theorem deriv_family_le_of_range_subset {f : ι → ordinal → ordinal}
  {g : ι' → ordinal → ordinal.{max u v w}} (hf : ∀ i, monotone (f i))
  (hfg : set.range f ⊆ set.range g) (a) : deriv_family f a ≤ deriv_family.{w (max u v w)} g a :=
begin
  apply limit_rec_on a,
  { simp only [deriv_family_zero],
    exact nfp_family_le_of_range_subset.{u w v} hfg 0 },
  { simp only [deriv_family_succ],
    exact λ b H, (nfp_family_monotone hf (succ_le_succ.2 H)).trans
      (nfp_family_le_of_range_subset.{u w v} hfg _) },
  { intros b hb H,
    rw [deriv_family_limit f hb, deriv_family_limit.{w (max u v w)} g hb, bsup_le_iff],
    exact λ c hc, (H c hc).trans (le_bsup _ c hc) }
end

theorem deriv_family_eq_of_range_eq {f : ι → ordinal → ordinal}
  {g : ι' → ordinal → ordinal.{max u v w}} (hfg : set.range f = set.range g) :
  deriv_family f = deriv_family.{w (max u v w)} g :=
funext (λ a, begin
  apply limit_rec_on a,
  { simp only [deriv_family_zero],
    rw nfp_family_eq_of_range_eq.{u w v} hfg,
    refl },
  { simp only [deriv_family_succ],
    intros b H,
    rw [H, nfp_family_eq_of_range_eq.{u w v} hfg],
    refl },
  { intros b hb H,
    rw [deriv_family_limit f hb, deriv_family_limit.{w (max u v w)} g hb],
    apply bsup_eq_of_brange_eq.{(max u v w) (max u v w) (max u v w)},
    congr,
    ext c hc,
    exact H c hc }
end)

theorem deriv_family_le_of_fp_subset {f : ι → ordinal → ordinal}
  {g : ι' → ordinal → ordinal} (hf : ∀ i, is_normal (f i)) (hg : ∀ i', is_normal (g i'))
  (H : ∀ o, (∀ i, f i o = o) → (∀ i', g i' o = o)) (a) :
  deriv_family.{w max u v w} g a ≤ deriv_family.{u max u v w} f a :=
begin
  rw [deriv_family_eq_enum_ord.{u max u v w} hf, deriv_family_eq_enum_ord hg],
  apply enum_ord_le_of_subset (fp_family_unbounded.{u max u v w} hf),
  intros a ha,
  rw set.mem_Inter at *,
  exact H a ha
end

theorem deriv_family_eq_of_fp_eq {f : ι → ordinal → ordinal}
  {g : ι' → ordinal → ordinal} (hf : ∀ i, is_normal (f i)) (hg : ∀ i', is_normal (g i'))
  (H : ∀ o, (∀ i, f i o = o) ↔ (∀ i', g i' o = o)) :
  deriv_family.{u max u v w} f = deriv_family.{w max u v w} g :=
funext (λ a, le_antisymm
  (deriv_family_le_of_fp_subset.{w v u} hg hf (λ o, (H o).2) a)
  (deriv_family_le_of_fp_subset.{u v w} hf hg (λ o, (H o).1) a))

end

/-! ### Fixed points of ordinal-indexed families of ordinals -/

section
variables {o : ordinal.{u}} {o' : ordinal.{w}} {f : Π b < o, ordinal.{max u v} → ordinal.{max u v}}

/-- The next common fixed point, at least `a`, for a family of normal functions indexed by ordinals.
-/
def nfp_bfamily (o : ordinal) (f : Π b < o, ordinal → ordinal) : ordinal → ordinal :=
nfp_family (family_of_bfamily o f)

theorem nfp_bfamily_eq_nfp_family {o : ordinal} (f : Π b < o, ordinal → ordinal) :
  nfp_bfamily o f = nfp_family (family_of_bfamily o f) :=
rfl

theorem foldr_le_nfp_bfamily {o : ordinal} (f : Π b < o, ordinal → ordinal) (a l) :
  list.foldr (family_of_bfamily o f) a l ≤ nfp_bfamily o f a :=
le_sup _ _

theorem le_nfp_bfamily {o : ordinal} (f : Π b < o, ordinal → ordinal) (a) :
  a ≤ nfp_bfamily o f a :=
le_sup _ []

theorem lt_nfp_bfamily {a b} :
  a < nfp_bfamily o f b ↔ ∃ l, a < list.foldr (family_of_bfamily o f) b l :=
lt_sup

theorem nfp_bfamily_le_iff {o : ordinal} {f : Π b < o, ordinal → ordinal} {a b} :
  nfp_bfamily o f a ≤ b ↔ ∀ l, list.foldr (family_of_bfamily o f) a l ≤ b :=
sup_le_iff

theorem nfp_bfamily_le {o : ordinal} {f : Π b < o, ordinal → ordinal} {a b} :
  (∀ l, list.foldr (family_of_bfamily o f) a l ≤ b) → nfp_bfamily o f a ≤ b :=
sup_le

theorem nfp_bfamily_monotone (hf : ∀ i hi, monotone (f i hi)) : monotone (nfp_bfamily o f) :=
nfp_family_monotone (λ i, hf _ _)

theorem apply_lt_nfp_bfamily (ho : o ≠ 0) (H : ∀ i hi, is_normal (f i hi)) {a b} :
  (∀ i hi, f i hi b < nfp_bfamily o f a) ↔ b < nfp_bfamily o f a :=
begin
  unfold nfp_bfamily,
  rw ←@apply_lt_nfp_family_iff _ (family_of_bfamily o f) (out_nonempty_iff_ne_zero.2 ho)
    (λ i, H _ _),
  refine ⟨λ h i, h _ (typein_lt_self i), λ h i hio, _⟩,
  rw ←family_of_bfamily_enum o f,
  apply h
end

theorem nfp_bfamily_le_apply (ho : o ≠ 0) (H : ∀ i hi, is_normal (f i hi)) {a b} :
  (∃ i hi, nfp_bfamily o f a ≤ f i hi b) ↔ nfp_bfamily o f a ≤ b :=
by { rw ←not_iff_not, push_neg, convert apply_lt_nfp_bfamily ho H, simp only [not_le] }

theorem nfp_bfamily_le_fp (H : ∀ i hi, monotone (f i hi)) {a b} (ab : a ≤ b)
  (h : ∀ i hi, f i hi b ≤ b) : nfp_bfamily o f a ≤ b :=
nfp_family_le_fp (λ _, H _ _) ab (λ i, h _ _)

theorem nfp_bfamily_fp {i hi} (H : is_normal (f i hi)) (a) :
  f i hi (nfp_bfamily o f a) = nfp_bfamily o f a :=
by { rw ←family_of_bfamily_enum o f, apply nfp_family_fp, rw family_of_bfamily_enum, exact H }

theorem apply_le_nfp_bfamily (ho : o ≠ 0) (H : ∀ i hi, is_normal (f i hi)) {a b} :
  (∀ i hi, f i hi b ≤ nfp_bfamily o f a) ↔ b ≤ nfp_bfamily o f a :=
begin
  refine ⟨λ h, _, λ h i hi, _⟩,
  { have ho' : 0 < o := ordinal.pos_iff_ne_zero.2 ho,
    exact ((H 0 ho').self_le b).trans (h 0 ho') },
  rw ←nfp_bfamily_fp (H i hi),
  exact (H i hi).monotone h
end

theorem nfp_bfamily_eq_self {a} (h : ∀ i hi, f i hi a = a) : nfp_bfamily o f a = a :=
nfp_family_eq_self (λ _, h _ _)

/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
theorem fp_bfamily_unbounded (H : ∀ i hi, is_normal (f i hi)) :
  (⋂ i hi, function.fixed_points (f i hi)).unbounded (<) :=
λ a, ⟨_, by { rw set.mem_Inter₂, exact λ i hi, nfp_bfamily_fp (H i hi) _ },
  (le_nfp_bfamily f a).not_lt⟩

/-- The derivative of a family of normal functions is the sequence of their common fixed points. -/
def deriv_bfamily (o : ordinal) (f : Π b < o, ordinal → ordinal) : ordinal → ordinal :=
deriv_family (family_of_bfamily o f)

theorem deriv_bfamily_eq_deriv_family {o : ordinal} (f : Π b < o, ordinal → ordinal) :
  deriv_bfamily o f = deriv_family (family_of_bfamily o f) :=
rfl

theorem deriv_bfamily_is_normal {o : ordinal} (f : Π b < o, ordinal → ordinal) :
  is_normal (deriv_bfamily o f) :=
deriv_family_is_normal _

theorem self_le_deriv_bfamily {o : ordinal} (f : Π b < o, ordinal → ordinal) :
  ∀ a, a ≤ deriv_bfamily o f a :=
(deriv_bfamily_is_normal f).self_le

theorem deriv_bfamily_fp {i hi} (H : is_normal (f i hi)) (a : ordinal) :
  f i hi (deriv_bfamily o f a) = deriv_bfamily o f a :=
by { rw ←family_of_bfamily_enum o f, apply deriv_family_fp, rw family_of_bfamily_enum, exact H }

theorem le_iff_deriv_bfamily (H : ∀ i hi, is_normal (f i hi)) {a} :
  (∀ i hi, f i hi a ≤ a) ↔ ∃ b, deriv_bfamily o f b = a :=
begin
  unfold deriv_bfamily,
  rw ←le_iff_deriv_family,
  { refine ⟨λ h i, h _ _, λ h i hi, _⟩,
    rw ←family_of_bfamily_enum o f,
    apply h },
  exact λ _, H _ _
end

theorem fp_iff_deriv_bfamily (H : ∀ i hi, is_normal (f i hi)) {a} :
  (∀ i hi, f i hi a = a) ↔ ∃ b, deriv_bfamily o f b = a :=
begin
  rw ←le_iff_deriv_bfamily H,
  refine ⟨λ h i hi, le_of_eq (h i hi), λ h i hi, _⟩,
  rw ←(H i hi).le_iff_eq,
  exact h i hi
end

theorem deriv_bfamily_eq_enum_ord (H : ∀ i hi, is_normal (f i hi)) :
  deriv_bfamily o f = enum_ord (⋂ i hi, function.fixed_points (f i hi)) :=
begin
  rw ←eq_enum_ord _ (fp_bfamily_unbounded H),
  use (deriv_bfamily_is_normal f).strict_mono,
  rw set.range_eq_iff,
  refine ⟨λ a, set.mem_Inter₂.2 (λ i hi, deriv_bfamily_fp (H i hi) a), λ a ha, _⟩,
  rw set.mem_Inter₂ at ha,
  rwa ←fp_iff_deriv_bfamily H
end

theorem deriv_bfamily_le_of_range_subset {f : Π b < o, ordinal → ordinal}
  {g : Π b < o', ordinal → ordinal.{max u v w}} (hf : ∀ i hi, monotone (f i hi))
  (hfg : brange o f ⊆ brange o' g) (a) :
  deriv_bfamily o f a ≤ deriv_bfamily.{w (max u v w)} o' g a :=
begin
  apply deriv_family_le_of_range_subset,
  { exact (λ i, hf _ _) },
  { simpa [range_family_of_bfamily] using hfg }
end

theorem deriv_bfamily_eq_of_range_eq {f : Π b < o, ordinal → ordinal}
  {g : Π b < o', ordinal → ordinal.{max u v w}} (hfg : brange o f = brange o' g) :
  deriv_bfamily o f = deriv_bfamily.{w (max u v w)} o' g :=
funext (λ a, begin
  unfold deriv_bfamily,
  rw deriv_family_eq_of_range_eq,
  simpa [range_family_of_bfamily] using hfg
end)

theorem deriv_bfamily_le_of_fp_subset {f : Π a < o, ordinal → ordinal}
  {g : Π a < o', ordinal → ordinal} (hf : ∀ i hi, is_normal (f i hi))
  (hg : ∀ i' hi', is_normal (g i' hi'))
  (H : ∀ o, (∀ i hi, f i hi o = o) → (∀ i' hi', g i' hi' o = o)) (a) :
  deriv_bfamily.{w max u v w} o' g a ≤ deriv_bfamily.{u max u v w} o f a :=
begin
  refine deriv_family_le_of_fp_subset (λ i, hf _ _) (λ i, hg _ _) (λ a h i', H _ (λ i hi, _) _ _) a,
  rw ←type_lt o at hi,
  have := h (enum (<) i hi),
  rwa family_of_bfamily_enum at this
end

-- another PR
theorem deriv_bfamily_eq_of_fp_eq {f : Π a < o, ordinal → ordinal}
  {g : Π a < o', ordinal → ordinal} (hf : ∀ i hi, is_normal (f i hi))
  (hg : ∀ i' hi', is_normal (g i' hi'))
  (H : ∀ o, (∀ i hi, f i hi o = o) ↔ (∀ i' hi', g i' hi' o = o)) :
  deriv_bfamily.{u max u v w} o f = deriv_bfamily.{w max u v w} o' g :=
funext (λ a, le_antisymm
  (deriv_bfamily_le_of_fp_subset.{w v u} hg hf (λ o, (H o).2) a)
  (deriv_bfamily_le_of_fp_subset.{u v w} hf hg (λ o, (H o).1) a))

end

/-! ### Fixed points of a single function -/

section
variable {f : ordinal.{u} → ordinal.{u}}

/-- The next fixed point function, the least fixed point of the normal function `f`, at least `a`.
-/
def nfp (f : ordinal → ordinal) : ordinal → ordinal :=
nfp_family (λ _ : unit, f)

@[simp] theorem nfp_family_eq_nfp (ι : Type u) [nonempty ι]
  (f : ordinal.{max u v} → ordinal.{max u v}) : nfp_family.{u v} (λ _ : ι, f) = nfp f :=
nfp_family_eq_of_range_eq.{u 0} (by simp)

@[simp] theorem sup_iterate_eq_nfp (f : ordinal.{u} → ordinal.{u}) :
  (λ a, sup (λ n : ℕ, f^[n] a)) = nfp f :=
begin
  refine funext (λ a, le_antisymm _ (sup_le (λ l, _))),
  { rw sup_le_iff,
    intro n,
    rw [←list.length_repeat unit.star n, ←list.foldr_const f a],
    apply le_sup },
  { rw list.foldr_const f a l,
    exact le_sup _ _ },
end

theorem iterate_le_nfp (f a n) : f^[n] a ≤ nfp f a :=
by { rw ←sup_iterate_eq_nfp, exact le_sup _ n }

theorem le_nfp (f a) : a ≤ nfp f a :=
iterate_le_nfp f a 0

theorem lt_nfp {a b} : a < nfp f b ↔ ∃ n, a < (f^[n]) b :=
by { rw ←sup_iterate_eq_nfp, exact lt_sup }

theorem nfp_le_iff {a b} : nfp f a ≤ b ↔ ∀ n, (f^[n]) a ≤ b :=
by { rw ←sup_iterate_eq_nfp, exact sup_le_iff }

theorem nfp_le {a b} : (∀ n, (f^[n]) a ≤ b) → nfp f a ≤ b :=
nfp_le_iff.2

@[simp] theorem nfp_id : nfp id = id :=
funext (λ a, begin
  simp_rw [←sup_iterate_eq_nfp, iterate_id],
  exact sup_const a
end)

theorem nfp_monotone (hf : monotone f) : monotone (nfp f) :=
nfp_family_monotone (λ i, hf)

theorem is_normal.apply_lt_nfp {f} (H : is_normal f) {a b} :
  f b < nfp f a ↔ b < nfp f a :=
begin
  unfold nfp,
  rw ←@apply_lt_nfp_family_iff unit (λ _, f) _ (λ _, H) a b,
  exact ⟨λ h _, h, λ h, h unit.star⟩
end

theorem is_normal.nfp_le_apply {f} (H : is_normal f) {a b} : nfp f a ≤ f b ↔ nfp f a ≤ b :=
le_iff_le_iff_lt_iff_lt.2 H.apply_lt_nfp

theorem nfp_le_fp {f} (H : monotone f) {a b} (ab : a ≤ b) (h : f b ≤ b) : nfp f a ≤ b :=
nfp_family_le_fp (λ _, H) ab (λ _, h)

theorem is_normal.nfp_fp {f} (H : is_normal f) : ∀ a, f (nfp f a) = nfp f a :=
@nfp_family_fp unit (λ _, f) unit.star H

theorem is_normal.apply_le_nfp {f} (H : is_normal f) {a b} :
  f b ≤ nfp f a ↔ b ≤ nfp f a :=
⟨le_trans (H.self_le _), λ h, by simpa only [H.nfp_fp] using H.le_iff.2 h⟩

theorem nfp_eq_self {f : ordinal → ordinal} {a} (h : f a = a) : nfp f a = a :=
nfp_family_eq_self (λ _, h)

/-- The fixed point lemma for normal functions: any normal function has an unbounded set of
fixed points. -/
theorem fp_unbounded (H : is_normal f) : (function.fixed_points f).unbounded (<) :=
by { convert fp_family_unbounded (λ _ : unit, H), exact (set.Inter_const _).symm }

/-- The derivative of a normal function `f` is the sequence of fixed points of `f`. -/
def deriv (f : ordinal → ordinal) : ordinal → ordinal :=
deriv_family (λ _ : unit, f)

@[simp] theorem deriv_family_eq_deriv (ι : Type u) [nonempty ι] (f : ordinal → ordinal) :
  deriv_family.{u max u v} (λ _ : ι, f) = deriv f :=
deriv_family_eq_of_range_eq.{u v 0} (by simp)

theorem deriv_bfamily_eq_deriv (f : ordinal → ordinal) : deriv_bfamily 1 (λ a _, f) = deriv f :=
@deriv_family_eq_deriv _ (out_nonempty_iff_ne_zero.2 ordinal.one_ne_zero) f

theorem deriv_bfamily_eq_deriv' {o : ordinal} (ho : o ≠ 0) (f : ordinal → ordinal) :
  deriv_bfamily.{u (max u v)} o (λ a _, f) = deriv f :=
deriv_family_eq_of_range_eq.{u v 0} $
  by rwa [set.range_const, range_family_of_bfamily, brange_const]

@[simp] theorem deriv_zero (f) : deriv f 0 = nfp f 0 :=
deriv_family_zero _

@[simp] theorem deriv_succ (f o) : deriv f (succ o) = nfp f (succ (deriv f o)) :=
deriv_family_succ _ _

theorem deriv_limit (f) {o} : is_limit o → deriv f o = bsup.{u 0} o (λ a _, deriv f a) :=
deriv_family_limit _

theorem deriv_is_normal (f) : is_normal (deriv f) :=
deriv_family_is_normal _

theorem self_le_deriv (f) : ∀ o, o ≤ deriv f o :=
(deriv_is_normal f).self_le

theorem deriv_id_of_nfp_id {f : ordinal → ordinal} (h : nfp f = id) : deriv f = id :=
((deriv_is_normal _).eq_iff_zero_and_succ is_normal.refl).2 (by simp [h, succ_inj])

@[simp] theorem deriv_id : deriv id = id := deriv_id_of_nfp_id nfp_id

theorem is_normal.deriv_fp {f} (H : is_normal f) : ∀ o, f (deriv f o) = deriv f o :=
@deriv_family_fp unit (λ _, f) unit.star H

theorem is_normal.le_iff_deriv {f} (H : is_normal f) {a} : f a ≤ a ↔ ∃ o, deriv f o = a :=
begin
  unfold deriv,
  rw ←le_iff_deriv_family (λ _ : unit, H),
  exact ⟨λ h _, h, λ h, h unit.star⟩
end

theorem is_normal.fp_iff_deriv {f} (H : is_normal f) {a} : f a = a ↔ ∃ o, deriv f o = a :=
by rw [←H.le_iff_eq, H.le_iff_deriv]

theorem deriv_eq_enum_ord (H : is_normal f) : deriv f = enum_ord (function.fixed_points f) :=
by { convert deriv_family_eq_enum_ord (λ _ : unit, H), exact (set.Inter_const _).symm }

theorem apply_le_deriv {f : ordinal → ordinal} (hf : is_normal f) (o) : f o ≤ deriv f o :=
begin
  rw deriv_eq_enum_ord hf,
  nth_rewrite 0 ←enum_ord_range hf.strict_mono,
  exact enum_ord_le_of_subset (fp_unbounded hf) fixed_points_subset_range _
end

theorem deriv_eq_id_of_nfp_eq_id {f : ordinal → ordinal} (h : nfp f = id) : deriv f = id :=
(is_normal.eq_iff_zero_and_succ (deriv_is_normal _) is_normal.refl).2 (by simp [h, succ_inj])

theorem deriv_le_of_fp_subset {f g : ordinal → ordinal} (hf : is_normal f) (hg : is_normal g)
  (H : ∀ o, f o = o → g o = o) (a) : deriv g a ≤ deriv f a :=
deriv_family_le_of_fp_subset (λ _, hf) (λ _, hg) (λ o hf' _, H o (hf' unit.star)) a

theorem deriv_eq_of_fp_eq {f g : ordinal → ordinal} (hf : is_normal f) (hg : is_normal g)
  (H : ∀ o, f o = o ↔ g o = o) : deriv f = deriv g :=
funext (λ a, le_antisymm
  (deriv_le_of_fp_subset hg hf (λ o, (H o).2) a)
  (deriv_le_of_fp_subset hf hg (λ o, (H o).1) a))

end

/-! ### Fixed points of addition -/

@[simp] theorem nfp_add_zero (a) : nfp ((+) a) 0 = a * omega :=
begin
  simp_rw [←sup_iterate_eq_nfp, ←sup_mul_nat],
  congr, funext,
  induction n with n hn,
  { rw [nat.cast_zero, mul_zero, iterate_zero_apply] },
  { nth_rewrite 1 nat.succ_eq_one_add,
    rw [nat.cast_add, nat.cast_one, mul_one_add, iterate_succ_apply', hn] }
end

theorem nfp_add_eq_mul_omega {a b} (hba : b ≤ a * omega) :
  nfp ((+) a) b = a * omega :=
begin
  apply le_antisymm (nfp_le_fp (add_is_normal a).monotone hba _),
  { rw ←nfp_add_zero,
    exact nfp_monotone (add_is_normal a).monotone (ordinal.zero_le b) },
  { rw [←mul_one_add, one_add_omega] }
end

theorem add_eq_right_iff_mul_omega_le {a b : ordinal} : a + b = b ↔ a * omega ≤ b :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw [←nfp_add_zero a, ←deriv_zero],
    cases (add_is_normal a).fp_iff_deriv.1 h with c hc,
    rw ←hc,
    exact (deriv_is_normal _).monotone (ordinal.zero_le _) },
  { have := ordinal.add_sub_cancel_of_le h,
    nth_rewrite 0 ←this,
    rwa [←add_assoc, ←mul_one_add, one_add_omega] }
end

theorem add_le_right_iff_mul_omega_le {a b : ordinal} : a + b ≤ b ↔ a * omega ≤ b :=
by { rw ←add_eq_right_iff_mul_omega_le, exact (add_is_normal a).le_iff_eq }

theorem deriv_add_eq_mul_omega_add (a b : ordinal.{u}) : deriv ((+) a) b = a * omega + b :=
begin
  revert b,
  rw [←funext_iff, is_normal.eq_iff_zero_and_succ (deriv_is_normal _) (add_is_normal _)],
  refine ⟨_, λ a h, _⟩,
  { rw [deriv_zero, add_zero],
    exact nfp_add_zero a },
  { rw [deriv_succ, h, add_succ],
    exact nfp_eq_self (add_eq_right_iff_mul_omega_le.2 ((le_add_right _ _).trans
      (lt_succ_self _).le)) }
end

/-! ### Fixed points of multiplication -/

local infixr ^ := @pow ordinal ordinal ordinal.has_pow
@[simp] theorem nfp_mul_one {a : ordinal} (ha : 0 < a) : nfp ((*) a) 1 = a ^ omega :=
begin
  rw [←sup_iterate_eq_nfp, ←sup_opow_nat],
  { dsimp, congr, funext,
    induction n with n hn,
    { rw [nat.cast_zero, opow_zero, iterate_zero_apply] },
    nth_rewrite 1 nat.succ_eq_one_add,
    rw [nat.cast_add, nat.cast_one, opow_add, opow_one, iterate_succ_apply', hn] },
  { exact ha }
end

@[simp] theorem nfp_mul_zero (a : ordinal) : nfp ((*) a) 0 = 0 :=
begin
  rw [←ordinal.le_zero, nfp_le_iff],
  intro n,
  induction n with n hn, { refl },
  rwa [iterate_succ_apply, mul_zero]
end

@[simp] theorem nfp_zero_mul : nfp ((*) 0) = id :=
begin
  rw ←sup_iterate_eq_nfp,
  refine funext (λ a, (sup_le (λ n, _)).antisymm (le_sup (λ n, ((*) 0)^[n] a) 0)),
  induction n with n hn, { refl },
  rw function.iterate_succ',
  change 0 * _ ≤ a,
  rw zero_mul,
  exact ordinal.zero_le a
end

@[simp] theorem deriv_mul_zero : deriv ((*) 0) = id :=
deriv_eq_id_of_nfp_eq_id nfp_zero_mul

theorem nfp_mul_eq_opow_omega {a b : ordinal} (hb : 0 < b) (hba : b ≤ a ^ omega) :
  nfp ((*) a) b = a ^ omega.{u} :=
begin
  cases eq_zero_or_pos a with ha ha,
  { rw [ha, zero_opow omega_ne_zero] at *,
    rw [ordinal.le_zero.1 hba, nfp_zero_mul],
    refl },
  apply le_antisymm,
  { apply nfp_le_fp (mul_is_normal ha).monotone hba,
    rw [←opow_one_add, one_add_omega] },
  rw ←nfp_mul_one ha,
  exact nfp_monotone (mul_is_normal ha).monotone (one_le_iff_pos.2 hb)
end

theorem eq_zero_or_opow_omega_le_of_mul_eq_right {a b : ordinal} (hab : a * b = b) :
  b = 0 ∨ a ^ omega.{u} ≤ b :=
begin
  cases eq_zero_or_pos a with ha ha,
  { rw [ha, zero_opow omega_ne_zero],
    exact or.inr (ordinal.zero_le b) },
  rw or_iff_not_imp_left,
  intro hb,
  change b ≠ 0 at hb,
  rw ←nfp_mul_one ha,
  rw ←one_le_iff_ne_zero at hb,
  exact nfp_le_fp (mul_is_normal ha).monotone hb (le_of_eq hab)
end

theorem mul_eq_right_iff_opow_omega_dvd {a b : ordinal} : a * b = b ↔ a ^ omega ∣ b :=
begin
  cases eq_zero_or_pos a with ha ha,
  { rw [ha, zero_mul, zero_opow omega_ne_zero, zero_dvd],
    exact eq_comm },
  refine ⟨λ hab, _, λ h, _⟩,
  { rw dvd_iff_mod_eq_zero,
    rw [←div_add_mod b (a ^ omega), mul_add, ←mul_assoc, ←opow_one_add, one_add_omega,
      add_left_cancel] at hab,
    cases eq_zero_or_opow_omega_le_of_mul_eq_right hab with hab hab,
    { exact hab },
    refine (not_lt_of_le hab (mod_lt b (opow_ne_zero omega _))).elim,
    rwa ←ordinal.pos_iff_ne_zero },
  cases h with c hc,
  rw [hc, ←mul_assoc, ←opow_one_add, one_add_omega]
end

theorem mul_le_right_iff_opow_omega_dvd {a b : ordinal} (ha : 0 < a) : a * b ≤ b ↔ a ^ omega ∣ b :=
by { rw ←mul_eq_right_iff_opow_omega_dvd, exact (mul_is_normal ha).le_iff_eq }

theorem nfp_mul_opow_omega_add {a c : ordinal} (b) (ha : 0 < a) (hc : 0 < c) (hca : c ≤ a ^ omega) :
  nfp ((*) a) (a ^ omega * b + c) = a ^ omega.{u} * b.succ :=
begin
  apply le_antisymm,
  { apply nfp_le_fp (mul_is_normal ha).monotone,
    { rw mul_succ,
      apply add_le_add_left hca },
    { rw [←mul_assoc, ←opow_one_add, one_add_omega] } },
  { cases mul_eq_right_iff_opow_omega_dvd.1 ((mul_is_normal ha).nfp_fp (a ^ omega * b + c))
      with d hd,
    rw hd,
    apply mul_le_mul_left',
    have := le_nfp (has_mul.mul a) (a ^ omega * b + c),
    rw hd at this,
    have := (add_lt_add_left hc (a ^ omega * b)).trans_le this,
    rw [add_zero, mul_lt_mul_iff_left (opow_pos omega ha)] at this,
    rwa succ_le }
end

theorem deriv_mul_eq_opow_omega_mul {a : ordinal.{u}} (ha : 0 < a) (b) :
  deriv ((*) a) b = a ^ omega * b :=
begin
  revert b,
  rw [←funext_iff,
    is_normal.eq_iff_zero_and_succ (deriv_is_normal _) (mul_is_normal (opow_pos omega ha))],
  refine ⟨_, λ c h, _⟩,
  { rw [deriv_zero, nfp_mul_zero, mul_zero] },
  { rw [deriv_succ, h],
    exact nfp_mul_opow_omega_add c ha zero_lt_one (one_le_iff_pos.2 (opow_pos _ ha)) },
end

/-! # Veblen's function -/

/-- The Veblen hierarchy from a normal function. `veblen f 0` equals the original function, and for
    any `o > 0`, `veblen f o` enumerates the common fixed points of all `veblen f a` for `a < o`. -/
def veblen (f : ordinal → ordinal) : ordinal → ordinal → ordinal :=
wf.fix (λ o φ, if o = 0 then f else deriv_bfamily.{u u} o φ)

private theorem veblen_def (f : ordinal → ordinal) (o) :
  veblen f o = if o = 0 then f else deriv_bfamily.{u u} o (λ a _, veblen f a) :=
wf.fix_eq _ o

theorem veblen_zero (f : ordinal → ordinal) : veblen f 0 = f :=
by { rw veblen_def, exact if_pos rfl }

theorem veblen_pos (f : ordinal → ordinal) {o : ordinal} (ho : o ≠ 0) :
  veblen f o = deriv_bfamily.{u u} o (λ a _, veblen f a) :=
by { rw veblen_def, exact if_neg ho }

theorem veblen_is_normal' (f : ordinal → ordinal) {o : ordinal.{u}} (ho : o ≠ 0) :
  is_normal (veblen f o) :=
by { rw veblen_pos f ho, apply deriv_bfamily_is_normal }

theorem veblen_is_normal {f : ordinal → ordinal} (hf : is_normal f) (o : ordinal.{u}) :
  is_normal (veblen f o) :=
begin
  rcases eq_or_ne o 0 with rfl | ho,
  { rwa veblen_zero },
  { exact veblen_is_normal' f ho }
end

theorem veblen_id (o : ordinal.{u}) : veblen id o = id :=
begin
  apply wf.induction o,
  intros a H,
  rcases eq_or_ne a 0 with rfl | ho,
  { rw veblen_zero },
  { rw veblen_pos id ho,
  suffices : (λ (i : a.out.α), veblen id (typein (<) i)) = λ i, id,
  { change deriv_family (λ (i : a.out.α), _) = _,
    simp_rw this,
    haveI : nonempty a.out.α, rwa out_nonempty_iff_ne_zero,
    rw [deriv_family_eq_deriv.{u u} a.out.α, deriv_id] },
  funext,
  rw H _ (typein_lt_self i) }
end

variables {f : ordinal.{u} → ordinal.{u}} (hf : is_normal f)
include hf

theorem veblen_veblen {o o' : ordinal.{u}} (ho : o < o') (a) :
  veblen f o (veblen f o' a) = veblen f o' a :=
begin
  rw veblen_pos f ((ordinal.zero_le o).trans_lt ho).ne',
  apply @deriv_bfamily_fp.{u u} _ _ _ ho (veblen_is_normal hf o)
end

theorem veblen_fp_lt_of_fp {o o' a : ordinal.{u}} (ho : veblen f o a = a) (ho' : o' ≤ o) :
  veblen f o' a = a :=
begin
  rcases lt_or_eq_of_le ho' with ho' | rfl,
  { rw ←ho,
    exact veblen_veblen hf ho' a },
  { exact ho }
end

theorem veblen_zero_le_of_fp {o a : ordinal} (ho : o ≠ 0) (H : ∀ o' < o, veblen f o' a = a) :
  veblen f o 0 ≤ a :=
begin
  rw [veblen_pos f ho, deriv_bfamily_eq_enum_ord, enum_ord_zero],
  { apply cInf_le', simpa only [set.mem_Inter] using H },
  { exact λ i hi, veblen_is_normal hf i }
end

theorem veblen_succ (o : ordinal.{u}) : veblen f o.succ = deriv (veblen f o) :=
begin
  rw veblen_pos f (@succ_ne_zero o),
  refine deriv_family_eq_of_fp_eq.{u 0 0}
    (λ i, veblen_is_normal hf _)
    (λ _, veblen_is_normal hf o)
    (λ a, ⟨λ H _, _, λ H i, veblen_fp_lt_of_fp hf (H unit.star) (lt_succ.1 (typein_lt_self i))⟩),
  have := H (enum (<) o (by { rw type_lt, exact lt_succ_self o })),
  rwa family_of_bfamily_enum at this
end

theorem veblen_monotone (o) : monotone (λ a, veblen.{u} f a o) :=
λ b c hbc, begin
  dsimp,
  rcases eq_zero_or_pos b with rfl | hb,
  { rcases lt_or_eq_of_le hbc with hc | rfl,
    { rw [veblen_zero, veblen_pos f hc.ne'],
      apply (apply_le_deriv hf _).trans,
      rw ←deriv_bfamily_eq_deriv.{0 u} f,
      refine deriv_bfamily_le_of_fp_subset.{u 0 0} (λ a _, veblen_is_normal hf _) (λ _ _, hf)
        (λ a H _ _, _) o,
      rw ←veblen_zero f,
      exact H 0 hc },
    { refl } },
  { rw [veblen_pos f hb.ne', veblen_pos f (hb.trans_le hbc).ne'],
    exact deriv_bfamily_le_of_fp_subset.{u u u} (λ a _, veblen_is_normal hf a)
      (λ a _, veblen_is_normal hf a) (λ a H i hib, H i (hib.trans_le hbc)) o }
end

theorem veblen_zero_is_normal (hf₀ : f 0 ≠ 0) : is_normal (λ a, veblen.{u} f a 0) :=
begin
  refine is_normal_iff_lt_succ_and_bsup_eq.{u u}.2 ⟨λ o₁, _, λ o ho, le_antisymm
    (bsup_le (λ i hi, veblen_monotone hf 0 hi.le))
    (veblen_zero_le_of_fp hf ho.1 (λ o₁ ho₁, _))⟩;
  have H := veblen_is_normal hf o₁,
  { rw [veblen_succ hf, deriv_zero, ←H.nfp_fp],
    apply H.strict_mono ((ordinal.pos_iff_ne_zero.2 (λ h, hf₀ _)).trans_le (iterate_le_nfp _ 0 1)),
    rw ←veblen_zero f,
    exact veblen_fp_lt_of_fp hf h (ordinal.zero_le _) },
  { rw is_normal.bsup.{u u u} H _ ho.1,
    refine le_antisymm (bsup_le (λ o₂ ho₂, (H.strict_mono.monotone
      (veblen_monotone hf _ ((le_max_right o₁ o₂).trans (lt_succ_self _).le))).trans _))
      (bsup_le (λ o₂ ho₂, (H.self_le _).trans (le_bsup.{u u} _ _ ho₂))),
    rw veblen_veblen hf,
    { exact le_bsup.{u u} _ _ (ho.2 _ (max_lt ho₁ ho₂)) },
    { exact lt_succ.2 (le_max_left _ _) } }
end

end ordinal
