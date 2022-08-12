/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.finsupp.lex

/-!
#  Witnesses, linear orders and covariant classes in  in finsupps
-/

variables {α N : Type*}

lemma ne_or_ne_of_ne {a b : α} (c : α) (h : a ≠ b) :
  a ≠ c ∨ b ≠ c :=
not_and_distrib.1 $ mt (and_imp.2 eq.substr) h.symm

namespace finsupp
section decidables
variables [decidable_eq α] [decidable_eq N]

section diff

section N_has_zero
variables [has_zero N] {f g : α →₀ N}

/--  `f.diff g` is the `finset` where `f` and `g` differ. -/
def diff (f g : α →₀ N) : finset α :=
(f.support ∪ g.support).filter (λ x, f x ≠ g x)

lemma diff_comm : f.diff g = g.diff f :=
by simp_rw [diff, finset.union_comm, ne_comm]

@[simp] lemma diff_eq_empty : f.diff g = ∅ ↔ f = g :=
filter_ne_eq_empty_iff

@[simp] lemma nonempty_diff_iff : (f.diff g).nonempty ↔ f ≠ g :=
finset.nonempty_iff_ne_empty.trans diff_eq_empty.not

@[simp]
lemma diff_zero_right : f.diff 0 = f.support :=
by simp only [diff, coe_zero, pi.zero_apply, support_zero, finset.union_empty,
    finset.filter_true_of_mem, mem_support_iff, imp_self, implies_true_iff]

@[simp]
lemma diff_zero_left : (0 : α →₀ N).diff f = f.support :=
diff_comm.trans diff_zero_right

@[simp]
lemma mem_diff {a : α} : a ∈ f.diff g ↔ f a ≠ g a :=
by simpa only [diff, finset.mem_filter, finset.mem_union, mem_support_iff, and_iff_right_iff_imp]
    using ne_or_ne_of_ne _

end N_has_zero

lemma add_diff_add_eq_left [add_left_cancel_monoid N] {f g h : α →₀ N} :
  (f + g).diff (f + h) = g.diff h  :=
begin
  ext,
  simp only [diff, ne.def, add_right_inj, finset.mem_filter, finset.mem_union, mem_support_iff,
    coe_add, pi.add_apply, and.congr_left_iff],
  exact λ bc, ⟨λ h, ne_or_ne_of_ne 0 bc, λ h, ne_or_ne_of_ne _ ((add_right_inj _).not.mpr bc)⟩,
end

--  can this proof by replaced by the previous one interlaced with `Nᵃᵒᵖ`?
lemma add_diff_add_eq_right [add_right_cancel_monoid N] {f g h : α →₀ N} :
  (f + h).diff (g + h) = f.diff g  :=
begin
  ext,
  simp only [diff, ne.def, add_left_inj, finset.mem_filter, finset.mem_union, mem_support_iff,
    coe_add, pi.add_apply, and.congr_left_iff],
  exact λ bc, ⟨λ h, ne_or_ne_of_ne 0 bc, λ h, ne_or_ne_of_ne _ ((add_left_inj _).not.mpr bc)⟩,
end
end diff

section wit
variables [nonempty α] [linear_order α]

/--  `wit f g` is an element of `α`.  It is `default` if and only if `f = g`.  Otherwise, it is
`a` if `a : α` is the smallest value for which `f a ≠ g a`. -/
noncomputable def wit [has_zero N] (f g : α →₀ N) : α :=
dite (f.diff g).nonempty (λ h, (f.diff g).min' h) (λ _, nonempty.some ‹_›)

lemma wit_comm [has_zero N] (f g : α →₀ N) : f.wit g = g.wit f :=
by simp only [wit, eq_comm, diff_comm]

lemma min'_eq_wit_of_ne [has_zero N] {f g : α →₀ N} (fg : f ≠ g) :
  (f.diff g).min' (nonempty_diff_iff.mpr fg) = f.wit g :=
(dif_pos _).symm

lemma wit_eq_wit_iff [has_zero N] {f g : α →₀ N} :
  f (f.wit g) = g (f.wit g) ↔ f = g :=
begin
  refine ⟨λ h, _, λ h, congr_fun h _⟩,
  rcases (f.diff g).eq_empty_or_nonempty with hfg | hfg,
  { exact diff_eq_empty.mp hfg },
  { refine (not_ne_iff.mpr h _).elim,
    unfold wit,
    refine mem_diff.mp _,
    split_ifs,
    apply finset.min'_mem }
end

lemma wit_le [has_zero N] {f g : α →₀ N} {x : α} (hx : f x ≠ g x) :
  (f.wit g) ≤ x :=
begin
  unfold wit,
  split_ifs,
  { exact (f.diff g).min'_le x (mem_diff.mpr hx) },
  { exact (hx (congr_fun ((not_not.mp (nonempty_diff_iff.not.mp h))) x)).elim }
end

lemma wit_add_left [add_left_cancel_monoid N] {f g h : α →₀ N} :
  (f + g).wit (f + h) = g.wit h :=
begin
  unfold wit,
  rw add_diff_add_eq_left,
end

lemma wit_add_right [add_right_cancel_monoid N] {f g h : α →₀ N} :
  (f + h).wit (g + h) = f.wit g :=
begin
  unfold wit,
  rw add_diff_add_eq_right,
end

end wit

/--  This is a technical result.  Likely, you will need one of the consequences of this lemma.  -/
lemma apply_min'_lt_apply_min'_of_le [linear_order α] [linear_order N] [has_zero N]
  {f g : α →₀ N} (h : (f.diff g).nonempty) (ab : to_lex f ≤ to_lex g) :
  f ((f.diff g).min' h) < g ((f.diff g).min' h) :=
begin
  rcases ab with ab | ⟨x, ltx, abx⟩,
  { exact (not_ne_iff.mpr (fun_like.coe_fn_eq.mp ab) (nonempty_diff_iff.mp h)).elim },
  convert abx,
  repeat { refine le_antisymm (finset.min'_le _ _ _) _,
    { simp only [diff, ne.def, finset.mem_filter, finset.mem_union, mem_support_iff],
      exact ⟨ne_or_ne_of_ne 0 abx.ne, abx.ne⟩ },
    { refine finset.le_min' _ _ _ (λ y hy, _),
      contrapose! hy,
      simpa only [mem_diff, ne.def, not_not] using ltx _ hy } }
end

/--  This is a technical result.  Likely, you will need one of the consequences of this lemma.  -/
lemma apply_min'_lt_apply_min'_iff [linear_order α] [linear_order N] [has_zero N] {f g : α →₀ N} :
  to_lex f ≤ to_lex g ↔ dite (f.diff g).nonempty
    (λ h, f ((f.diff g).min' h) < g ((f.diff g).min' h)) (λ _, true) :=
begin
  split_ifs with h h,
  { refine ⟨apply_min'_lt_apply_min'_of_le _, λ h', _⟩,
    refine le_of_lt ⟨((f.diff g).min' h), λ j hj, _, h'⟩,
    refine not_ne_iff.mp (mem_diff.not.mp _),
    contrapose! hj,
    exact finset.min'_le _ _ hj },
  { rw [nonempty_diff_iff, not_not] at h,
    simp [h] }
end

lemma apply_to_lex_lt_iff_apply_wit_lt [nonempty α] [linear_order α] [linear_order N] [has_zero N]
  {f g : (α →₀ N)} :
  to_lex f < to_lex g ↔ f (f.wit g) < g (f.wit g) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw ← min'_eq_wit_of_ne (id h.ne : f ≠ g),
    exact apply_min'_lt_apply_min'_of_le (nonempty_diff_iff.mpr h.ne) h.le },
  { refine lt_of_le_of_ne (apply_min'_lt_apply_min'_iff.mpr _) _,
    rwa [dif_pos, min'_eq_wit_of_ne],
    repeat { refine coe_fn_inj.not.mp (function.ne_iff.mpr ⟨_, h.ne⟩) } }
end

lemma to_lex_le_iff_apply_wit_le [nonempty α] [linear_order α] [linear_order N] [has_zero N]
  {f g : (α →₀ N)} :
  to_lex f ≤ to_lex g ↔ f (f.wit g) ≤ g (f.wit g) :=
not_iff_not.mp (by simp only [not_le, apply_to_lex_lt_iff_apply_wit_lt, wit_comm])

lemma le_iff_of_lex_apply_wit_le [nonempty α] [linear_order α] [linear_order N] [has_zero N]
  {f g : lex (α →₀ N)} :
  f ≤ g ↔ of_lex f (f.wit g) ≤ of_lex g (f.wit g) :=
by simp [of_lex, to_lex, ← to_lex_le_iff_apply_wit_le]

lemma apply_eq_of_lt_wit [nonempty α] [linear_order α] [linear_order N] [has_zero N]
  {f g : (α →₀ N)} {x : α} (hx : x < f.wit g) :
  f x = g x :=
begin
  refine le_antisymm _ _;
  contrapose! hx;
  refine wit_le _,
  exacts [hx.ne', hx.ne],
end

end decidables

variables [linear_order α] [linear_order N] [add_left_cancel_monoid N] [covariant_class N N (+) (≤)]

instance : covariant_class (to_lex (α →₀ N)) (to_lex (α →₀ N))
  ((+) : (α →₀ N) → (α →₀ N) → (α →₀ N))
  (@has_le.le (to_lex (α →₀ N)) (by { haveI : linear_order (to_lex (α →₀ N)) := lex.linear_order,
                                      apply_instance })) :=
{ elim := λ f g h gh, begin
    by_cases iα : nonempty α,
    { resetI,
      refine le_iff_of_lex_apply_wit_le.mpr _,
      simpa only [wit_add_left, equiv.coe_refl, id.def, coe_add, pi.add_apply] using
        add_le_add_left (le_iff_of_lex_apply_wit_le.mp gh) _ },
    { rw subsingleton_iff.mp ⟨λ f g, ext (λ (x : α), (iα ⟨x⟩).elim)⟩ h g }
  end }

end finsupp
