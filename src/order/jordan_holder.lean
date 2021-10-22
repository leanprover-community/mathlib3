/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import order.lattice
import data.list.sort
import data.equiv.fin
import data.equiv.functor
/-!
# Jordan-Hölder Theorem

This file proves the Jordan Hölder theorem for a `jordan_holder_lattice`, a class also defined in
this file. Examples of `jordan_holder_lattice` include `subgroup G` if `G` is a group, and
`submodule R M` if `M` is an `R`-module. Using this approach the theorem need not be proved
seperately for both groups and modules, the proof in this file can be applied to both.

## Main definitions
The main definitions in this file are `jordan_holder_lattice` and `composition_series`,
and the relation `equivalent` on `composition_series`

A `jordan_holder_lattice` is the class for which the Jordan Hölder theorem is proved. A
Jordan Hölder lattice is a lattice equipped with a notion of maximality, `is_maximal`, and a notion
of isomorphism of pairs `iso`. In the example of subgroups of a group, `is_maximal H K` means that
`H` is a maximal normal subgroup of `K`, and `iso (H₁, K₁) (H₂, K₂)` means that the quotient
`H₁ / K₁` is isomorphic to the quotient `H₂ / K₂`. `iso` must be symmetric and transitive and must
satisfy the second isomorphism theorem `iso (H, H ⊔ K) (H ⊓ K, K)`.

A `composition_series X` is a finite nonempty series of elements of the lattice `X` such that
each element is maximal inside the next. The length of a `composition_series X` is
one less than the number of elements in the series. Note that there is no stipulation
that a series start from the bottom of the lattice and finish at the top.
For a composition series `s`, `s.top` is the largest element of the series,
and `s.bot` is the least element.

Two `composition_series X`, `s₁` and `s₂` are equivalent if there is a bijection
`e : fin s₁.length ≃ fin s₂.length` such that for any `i`,
`iso (s₁ i, s₁ i.succ) (s₂ (e i), s₂ (e i.succ))`

## Main theorems

The main theorem is `composition_series.jordan_holder`, which says that if two composition
series have the same least element and the same largest element,
then they are `equivalent`.

## TODO

Provide instances of `jordan_holder_lattice` for both submodules and subgroups, and potentially
for modular lattices.

It is not entirely clear how this should be done. Possibly there should be no global instances
of `jordan_holder_lattice`, and the instances should only be defined locally in order to prove
the Jordan-Hölder theorem for modules/groups and the API should be transferred because many of the
theorems in this file will have stronger versions for modules. There will also need to be an API for
mapping composition series across homomorphisms. It is also probably possible to
provide an instance of `jordan_holder_lattice` for any `modular_lattice`, and in this case the
Jordan-Hölder theorem will say that there is a well defined notion of length of a modular lattice.
However an instance of `jordan_holder_lattice` for a modular lattice will not be able to contain
the correct notion of isomorphism for modules, so a separate instance for modules will still be
required and this will clash with the instance for modular lattices, and so at least one of these
instances should not be a global instance.
-/

universe u

open set

/--
A `jordan_holder_lattice` is the class for which the Jordan Hölder theorem is proved. A
Jordan Hölder lattice is a lattice equipped with a notion of maximality, `is_maximal`, and a notion
of isomorphism of pairs `iso`. In the example of subgroups of a group, `is_maximal H K` means that
`H` is a maximal normal subgroup of `K`, and `iso (H₁, K₁) (H₂, K₂)` means that the quotient
`H₁ / K₁` is isomorphic to the quotient `H₂ / K₂`. `iso` must be symmetric and transitive and must
satisfy the second isomorphism theorem `iso (H, H ⊔ K) (H ⊓ K, K)`.
Examples include `subgroup G` if `G` is a group, and `submodule R M` if `M` is an `R`-module.
-/
class jordan_holder_lattice (X : Type u) [lattice X] :=
(is_maximal : X → X → Prop)
(lt_of_is_maximal : ∀ {x y}, is_maximal x y → x < y)
(sup_eq_of_is_maximal : ∀ {x y z}, is_maximal x z → is_maximal y z →
  x ≠ y → x ⊔ y = z)
(is_maximal_inf_left_of_is_maximal_sup : ∀ {x y}, is_maximal x (x ⊔ y) → is_maximal y (x ⊔ y) →
  is_maximal (x ⊓ y) x)
(iso : (X × X) → (X × X) → Prop)
(iso_symm : ∀ {x y}, iso x y → iso y x)
(iso_trans : ∀ {x y z}, iso x y → iso y z → iso x z)
(second_iso : ∀ {x y}, is_maximal x (x ⊔ y) → iso (x, x ⊔ y) (x ⊓ y, y))

namespace jordan_holder_lattice

variables {X : Type u} [lattice X] [jordan_holder_lattice X]

lemma is_maximal_inf_right_of_is_maximal_sup {x y : X}
  (hxz : is_maximal x (x ⊔ y)) (hyz : is_maximal y (x ⊔ y)) :
  is_maximal (x ⊓ y) y :=
begin
  rw [inf_comm],
  rw [sup_comm] at hxz hyz,
  exact is_maximal_inf_left_of_is_maximal_sup hyz hxz
end

lemma is_maximal_of_eq_inf (x b : X) {a y : X}
  (ha : x ⊓ y = a) (hxy : x ≠ y) (hxb : is_maximal x b) (hyb : is_maximal y b) :
  is_maximal a y :=
begin
  have hb : x ⊔ y = b,
    from sup_eq_of_is_maximal hxb hyb hxy,
  substs a b,
  exact is_maximal_inf_right_of_is_maximal_sup hxb hyb
end

lemma second_iso_of_eq {x y a b : X} (hm : is_maximal x a) (ha : x ⊔ y = a) (hb : x ⊓ y = b) :
  iso (x, a) (b, y) :=
by substs a b; exact second_iso hm

lemma is_maximal.iso_refl {x y : X} (h : is_maximal x y) : iso (x, y) (x, y) :=
second_iso_of_eq h
  (sup_eq_right.2 (le_of_lt (lt_of_is_maximal h)))
  (inf_eq_left.2 (le_of_lt (lt_of_is_maximal h)))

end jordan_holder_lattice

open jordan_holder_lattice

attribute [symm] iso_symm
attribute [trans] iso_trans

/--
A `composition_series X` is a finite nonempty series of elements of a
`jordan_holder_lattice` such that each element is maximal inside the next. The length of a
`composition_series X` is one less than the number of elements in the series.
Note that there is no stipulation that a series start from the bottom of the lattice and finish at
the top. For a composition series `s`, `s.top` is the largest element of the series,
and `s.bot` is the least element.
-/
structure composition_series (X : Type u) [lattice X] [jordan_holder_lattice X] : Type u :=
(length : ℕ)
(series : fin (length + 1) → X)
(step' : ∀ i : fin length, is_maximal (series i.cast_succ) (series i.succ))

namespace composition_series

variables {X : Type u} [lattice X] [jordan_holder_lattice X]

instance : has_coe_to_fun (composition_series X) (λ x, fin (x.length + 1) → X) :=
{ coe := composition_series.series }

instance [inhabited X] : inhabited (composition_series X) :=
⟨{ length := 0,
   series := λ _, default X,
   step' := λ x, x.elim0 }⟩

variables {X}

lemma step (s : composition_series X) : ∀ i : fin s.length,
  is_maximal (s i.cast_succ) (s i.succ) := s.step'

@[simp] lemma coe_fn_mk (length : ℕ) (series step) :
  (@composition_series.mk X _ _ length series step : fin length.succ → X) = series := rfl

theorem lt_succ (s : composition_series X) (i : fin s.length) :
  s i.cast_succ < s i.succ :=
lt_of_is_maximal (s.step _)

protected theorem strict_mono (s : composition_series X) : strict_mono s :=
fin.strict_mono_iff_lt_succ.2 (λ i h, s.lt_succ ⟨i, nat.lt_of_succ_lt_succ h⟩)

protected theorem injective (s : composition_series X) : function.injective s :=
s.strict_mono.injective

@[simp] protected theorem inj (s : composition_series X) {i j : fin s.length.succ} :
  s i = s j ↔ i = j :=
s.injective.eq_iff

instance : has_mem X (composition_series X) :=
⟨λ x s, x ∈ set.range s⟩

lemma mem_def {x : X} {s : composition_series X} : x ∈ s ↔ x ∈ set.range s := iff.rfl

lemma total {s : composition_series X} {x y : X} (hx : x ∈ s) (hy : y ∈ s) : x ≤ y ∨ y ≤ x :=
begin
  rcases set.mem_range.1 hx with ⟨i, rfl⟩,
  rcases set.mem_range.1 hy with ⟨j, rfl⟩,
  rw [s.strict_mono.le_iff_le, s.strict_mono.le_iff_le],
  exact le_total i j
end

/-- The ordered `list X` of elements of a `composition_series X`. -/
def to_list (s : composition_series X) : list X := list.of_fn s

/-- Two `composition_series` are equal if they are the same length and
have the same `i`th element for every `i` -/
lemma ext_fun {s₁ s₂ : composition_series X}
  (hl : s₁.length = s₂.length)
  (h : ∀ i, s₁ i = s₂ (fin.cast (congr_arg nat.succ hl) i)) :
  s₁ = s₂ :=
begin
  cases s₁, cases s₂,
  dsimp at *,
  subst hl,
  simpa [function.funext_iff] using h
end

@[simp] lemma length_to_list (s : composition_series X) : s.to_list.length = s.length + 1 :=
by rw [to_list, list.length_of_fn]

lemma to_list_ne_nil (s : composition_series X) : s.to_list ≠ [] :=
by rw [← list.length_pos_iff_ne_nil, length_to_list]; exact nat.succ_pos _

lemma to_list_injective : function.injective (@composition_series.to_list X _ _) :=
λ s₁ s₂ (h : list.of_fn s₁ = list.of_fn s₂),
have h₁ : s₁.length = s₂.length,
  from nat.succ_injective
    ((list.length_of_fn s₁).symm.trans $
      (congr_arg list.length h).trans $
      list.length_of_fn s₂),
have h₂ : ∀ i : fin s₁.length.succ, (s₁ i) = s₂ (fin.cast (congr_arg nat.succ h₁) i),
  begin
    assume i,
    rw [← list.nth_le_of_fn s₁ i, ← list.nth_le_of_fn s₂],
    simp [h]
  end,
begin
  cases s₁, cases s₂,
  dsimp at *,
  subst h₁,
  simp only [heq_iff_eq, eq_self_iff_true, true_and],
  simp only [fin.cast_refl] at h₂,
  exact funext h₂
end

lemma chain'_to_list (s : composition_series X) :
  list.chain' is_maximal s.to_list :=
list.chain'_iff_nth_le.2
  begin
    assume i hi,
    simp only [to_list, list.nth_le_of_fn'],
    rw [length_to_list] at hi,
    exact s.step ⟨i, hi⟩
  end

lemma to_list_sorted (s : composition_series X) : s.to_list.sorted (<) :=
list.pairwise_iff_nth_le.2 (λ i j hi hij,
  begin
    dsimp [to_list],
    rw [list.nth_le_of_fn', list.nth_le_of_fn'],
    exact s.strict_mono hij
  end)

lemma to_list_nodup (s : composition_series X) : s.to_list.nodup :=
list.nodup_iff_nth_le_inj.2
  (λ i j hi hj,
    begin
      delta to_list,
      rw [list.nth_le_of_fn', list.nth_le_of_fn', s.injective.eq_iff, fin.ext_iff,
        fin.coe_mk, fin.coe_mk],
      exact id
    end)

@[simp] lemma mem_to_list {s : composition_series X} {x : X} : x ∈ s.to_list ↔ x ∈ s :=
by rw [to_list, list.mem_of_fn, mem_def]

/-- Make a `composition_series X` from the ordered list of its elements. -/
def of_list (l : list X) (hl : l ≠ []) (hc : list.chain' is_maximal l) :
  composition_series X :=
{ length := l.length - 1,
  series := λ i, l.nth_le i begin
      conv_rhs { rw ← nat.sub_add_cancel (list.length_pos_of_ne_nil hl) },
      exact i.2
    end,
  step' := λ ⟨i, hi⟩, list.chain'_iff_nth_le.1 hc i hi }

lemma length_of_list (l : list X) (hl : l ≠ []) (hc : list.chain' is_maximal l) :
  (of_list l hl hc).length = l.length - 1 := rfl

lemma of_list_to_list (s : composition_series X) :
  of_list s.to_list s.to_list_ne_nil s.chain'_to_list = s :=
begin
  refine ext_fun _ _,
  { rw [length_of_list, length_to_list, nat.succ_sub_one] },
  { rintros ⟨i, hi⟩,
    dsimp [of_list, to_list],
    rw [list.nth_le_of_fn'] }
end

@[simp] lemma of_list_to_list' (s : composition_series X) :
  of_list s.to_list s.to_list_ne_nil s.chain'_to_list = s :=
of_list_to_list s

@[simp] lemma to_list_of_list (l : list X) (hl : l ≠ []) (hc : list.chain' is_maximal l)  :
  to_list (of_list l hl hc) = l :=
begin
  refine list.ext_le _ _,
  { rw [length_to_list, length_of_list, nat.sub_add_cancel
      (list.length_pos_of_ne_nil hl)] },
  { assume i hi hi',
    dsimp [of_list, to_list],
    rw [list.nth_le_of_fn'],
    refl }
end

/-- Two `composition_series` are equal if they have the same elements. See also `ext_fun`. -/
@[ext] lemma ext {s₁ s₂ : composition_series X} (h : ∀ x, x ∈ s₁ ↔ x ∈ s₂) : s₁ = s₂ :=
to_list_injective $ list.eq_of_perm_of_sorted
  (by classical; exact list.perm_of_nodup_nodup_to_finset_eq
    s₁.to_list_nodup
    s₂.to_list_nodup
    (finset.ext $ by simp *))
  s₁.to_list_sorted s₂.to_list_sorted

/-- The largest element of a `composition_series` -/
def top (s : composition_series X) : X := s (fin.last _)

lemma top_mem (s : composition_series X) : s.top ∈ s :=
mem_def.2 (set.mem_range.2 ⟨fin.last _, rfl⟩)

@[simp] lemma le_top {s : composition_series X} (i : fin (s.length + 1)) : s i ≤ s.top :=
s.strict_mono.monotone (fin.le_last _)

lemma le_top_of_mem {s : composition_series X} {x : X} (hx : x ∈ s) : x ≤ s.top :=
let ⟨i, hi⟩ := set.mem_range.2 hx in hi ▸ le_top _

/-- The smallest element of a `composition_series` -/
def bot (s : composition_series X) : X := s 0

lemma bot_mem (s : composition_series X) : s.bot ∈ s :=
mem_def.2 (set.mem_range.2 ⟨0, rfl⟩)

@[simp] lemma bot_le {s : composition_series X} (i : fin (s.length + 1)) : s.bot ≤ s i :=
s.strict_mono.monotone (fin.zero_le _)

lemma bot_le_of_mem {s : composition_series X} {x : X} (hx : x ∈ s) : s.bot ≤ x :=
let ⟨i, hi⟩ := set.mem_range.2 hx in hi ▸ bot_le _

lemma length_pos_of_mem_ne {s : composition_series X}
  {x y : X} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
  0 < s.length :=
let ⟨i, hi⟩ := hx, ⟨j, hj⟩ := hy in
have hij : i ≠ j, from mt s.inj.2 $ λ h, hxy (hi ▸ hj ▸ h),
hij.lt_or_lt.elim
  (λ hij, (lt_of_le_of_lt (zero_le i)
    (lt_of_lt_of_le hij (nat.le_of_lt_succ j.2))))
  (λ hji, (lt_of_le_of_lt (zero_le j)
    (lt_of_lt_of_le hji (nat.le_of_lt_succ i.2))))

lemma forall_mem_eq_of_length_eq_zero {s : composition_series X}
  (hs : s.length = 0) {x y} (hx : x ∈ s) (hy : y ∈ s) : x = y :=
by_contradiction (λ hxy, pos_iff_ne_zero.1 (length_pos_of_mem_ne hx hy hxy) hs)

/-- Remove the largest element from a `composition_series`. If the series `s`
has length zero, then `s.erase_top = s` -/
@[simps] def erase_top (s : composition_series X) : composition_series X :=
{ length := s.length - 1,
  series := λ i, s ⟨i, lt_of_lt_of_le i.2 (nat.succ_le_succ tsub_le_self)⟩,
  step' := λ i, begin
    have := s.step ⟨i, lt_of_lt_of_le i.2 tsub_le_self⟩,
    cases i,
    exact this
  end }

lemma top_erase_top (s : composition_series X) :
  s.erase_top.top = s ⟨s.length - 1, lt_of_le_of_lt tsub_le_self (nat.lt_succ_self _)⟩ :=
show s _ = s _, from congr_arg s
begin
  ext,
  simp only [erase_top_length, fin.coe_last, fin.coe_cast_succ, fin.coe_of_nat_eq_mod,
    fin.coe_mk, coe_coe]
end

lemma erase_top_top_le (s : composition_series X) : s.erase_top.top ≤ s.top :=
by simp [erase_top, top, s.strict_mono.le_iff_le, fin.le_iff_coe_le_coe, tsub_le_self]

@[simp] lemma bot_erase_top (s : composition_series X) : s.erase_top.bot = s.bot := rfl

lemma mem_erase_top_of_ne_of_mem {s : composition_series X} {x : X}
  (hx : x ≠ s.top) (hxs : x ∈ s) : x ∈ s.erase_top :=
begin
  { rcases hxs with ⟨i, rfl⟩,
    have hi : (i : ℕ) < (s.length - 1).succ,
    { conv_rhs { rw [← nat.succ_sub (length_pos_of_mem_ne ⟨i, rfl⟩ s.top_mem hx),
        nat.succ_sub_one] },
      exact lt_of_le_of_ne
        (nat.le_of_lt_succ i.2)
        (by simpa [top, s.inj, fin.ext_iff] using hx) },
    refine ⟨i.cast_succ, _⟩,
    simp [fin.ext_iff, nat.mod_eq_of_lt hi] }
end

lemma mem_erase_top {s : composition_series X} {x : X}
  (h : 0 < s.length) : x ∈ s.erase_top ↔ x ≠ s.top ∧ x ∈ s :=
begin
  simp only [mem_def],
  dsimp only [erase_top, coe_fn_mk],
  split,
  { rintros ⟨i, rfl⟩,
    have hi : (i : ℕ) < s.length,
    { conv_rhs { rw [← nat.succ_sub_one s.length, nat.succ_sub h] },
      exact i.2 },
    simp [top, fin.ext_iff, (ne_of_lt hi)] },
  { intro h,
    exact mem_erase_top_of_ne_of_mem h.1 h.2 }
end

lemma lt_top_of_mem_erase_top {s : composition_series X} {x : X} (h : 0 < s.length)
  (hx : x ∈ s.erase_top) : x < s.top :=
lt_of_le_of_ne
  (le_top_of_mem ((mem_erase_top h).1 hx).2)
  ((mem_erase_top h).1 hx).1

lemma is_maximal_erase_top_top {s : composition_series X} (h : 0 < s.length) :
  is_maximal s.erase_top.top s.top :=
have s.length - 1 + 1 = s.length,
  by conv_rhs { rw [← nat.succ_sub_one s.length] }; rw nat.succ_sub h,
begin
  rw [top_erase_top, top],
  convert s.step ⟨s.length - 1, nat.sub_lt h zero_lt_one⟩;
  ext; simp [this]
end

lemma append_cast_add_aux
  {s₁ s₂ : composition_series X}
  (i : fin s₁.length) :
  fin.append (nat.add_succ _ _).symm (s₁ ∘ fin.cast_succ) s₂
  (fin.cast_add s₂.length i).cast_succ = s₁ i.cast_succ :=
by { cases i, simp [fin.append, *] }

lemma append_succ_cast_add_aux
  {s₁ s₂ : composition_series X}
  (i : fin s₁.length)
  (h : s₁ (fin.last _) = s₂ 0) :
  fin.append (nat.add_succ _ _).symm (s₁ ∘ fin.cast_succ) s₂
  (fin.cast_add s₂.length i).succ = s₁ i.succ :=
begin
  cases i with i hi,
  simp only [fin.append, hi, fin.succ_mk, function.comp_app, fin.cast_succ_mk,
    fin.coe_mk, fin.cast_add_mk],
  split_ifs,
  { refl },
  { have : i + 1 = s₁.length, from le_antisymm hi (le_of_not_gt h_1),
    calc s₂ ⟨i + 1 - s₁.length, by simp [this]⟩
        = s₂ 0 : congr_arg s₂ (by simp [fin.ext_iff, this])
    ... = s₁ (fin.last _) : h.symm
    ... = _ : congr_arg s₁ (by simp [fin.ext_iff, this]) }
end

lemma append_nat_add_aux
  {s₁ s₂ : composition_series X}
  (i : fin s₂.length) :
  fin.append (nat.add_succ _ _).symm (s₁ ∘ fin.cast_succ) s₂
  (fin.nat_add s₁.length i).cast_succ = s₂ i.cast_succ :=
begin
  cases i,
  simp only [fin.append, nat.not_lt_zero, fin.nat_add_mk, add_lt_iff_neg_left,
    nat.add_sub_cancel_left, dif_neg, fin.cast_succ_mk, not_false_iff, fin.coe_mk]
end

lemma append_succ_nat_add_aux
  {s₁ s₂ : composition_series X}
  (i : fin s₂.length) :
  fin.append (nat.add_succ _ _).symm (s₁ ∘ fin.cast_succ) s₂
  (fin.nat_add s₁.length i).succ = s₂ i.succ :=
begin
  cases i with i hi,
  simp only [fin.append, add_assoc, nat.not_lt_zero, fin.nat_add_mk, add_lt_iff_neg_left,
    nat.add_sub_cancel_left, fin.succ_mk, dif_neg, not_false_iff, fin.coe_mk]
end

/-- Append two composition series `s₁` and `s₂` such that
the least element of `s₁` is the maximum element of `s₂`. -/
@[simps length] def append (s₁ s₂ : composition_series X)
  (h : s₁.top = s₂.bot) : composition_series X :=
{ length := s₁.length + s₂.length,
  series := fin.append (nat.add_succ _ _).symm (s₁ ∘ fin.cast_succ) s₂,
  step' := λ i, begin
    refine fin.add_cases  _ _ i,
    { intro i,
      rw [append_succ_cast_add_aux _ h, append_cast_add_aux],
      exact s₁.step i },
    { intro i,
      rw [append_nat_add_aux, append_succ_nat_add_aux],
      exact s₂.step i }
  end }

@[simp] lemma append_cast_add {s₁ s₂ : composition_series X}
  (h : s₁.top = s₂.bot) (i : fin s₁.length) :
  append s₁ s₂ h (fin.cast_add s₂.length i).cast_succ = s₁ i.cast_succ :=
append_cast_add_aux i

@[simp] lemma append_succ_cast_add {s₁ s₂ : composition_series X}
  (h : s₁.top = s₂.bot) (i : fin s₁.length) :
  append s₁ s₂ h (fin.cast_add s₂.length i).succ = s₁ i.succ :=
append_succ_cast_add_aux i h

@[simp] lemma append_nat_add {s₁ s₂ : composition_series X}
  (h : s₁.top = s₂.bot) (i : fin s₂.length) :
  append s₁ s₂ h (fin.nat_add s₁.length i).cast_succ = s₂ i.cast_succ :=
append_nat_add_aux i

@[simp] lemma append_succ_nat_add {s₁ s₂ : composition_series X}
  (h : s₁.top = s₂.bot) (i : fin s₂.length) :
  append s₁ s₂ h (fin.nat_add s₁.length i).succ = s₂ i.succ :=
append_succ_nat_add_aux i

/-- Add an element to the top of a `composition_series` -/
@[simps length] def snoc (s : composition_series X) (x : X)
  (hsat : is_maximal s.top x) : composition_series X :=
{ length := s.length + 1,
  series := fin.snoc s x,
  step' := λ i, begin
    refine fin.last_cases _ _ i,
    { rwa [fin.snoc_cast_succ, fin.succ_last, fin.snoc_last, ← top] },
    { intro i,
      rw [fin.snoc_cast_succ, ← fin.cast_succ_fin_succ, fin.snoc_cast_succ],
      exact s.step _ }
  end }

@[simp] lemma top_snoc (s : composition_series X) (x : X)
  (hsat : is_maximal s.top x) : (snoc s x hsat).top = x :=
fin.snoc_last _ _

@[simp] lemma snoc_last (s : composition_series X) (x : X) (hsat : is_maximal s.top x) :
  snoc s x hsat (fin.last (s.length + 1)) = x :=
fin.snoc_last _ _

@[simp] lemma snoc_cast_succ (s : composition_series X) (x : X) (hsat : is_maximal s.top x)
  (i : fin (s.length + 1)) : snoc s x hsat (i.cast_succ) = s i :=
fin.snoc_cast_succ _ _ _

@[simp] lemma bot_snoc (s : composition_series X) (x : X) (hsat : is_maximal s.top x) :
  (snoc s x hsat).bot = s.bot :=
by rw [bot, bot, ← fin.cast_succ_zero, snoc_cast_succ]

lemma mem_snoc {s : composition_series X} {x y: X}
  {hsat : is_maximal s.top x} : y ∈ snoc s x hsat ↔ y ∈ s ∨ y = x :=
begin
  simp only [snoc, mem_def],
  split,
  { rintros ⟨i, rfl⟩,
    refine fin.last_cases _ (λ i, _) i,
    { right, simp },
    { left, simp } },
  { intro h,
    rcases h with ⟨i, rfl⟩ | rfl,
    { use i.cast_succ, simp },
    { use (fin.last _), simp } }
end

lemma eq_snoc_erase_top {s : composition_series X} (h : 0 < s.length) :
  s = snoc (erase_top s) s.top (is_maximal_erase_top_top h) :=
begin
  ext x,
  simp [mem_snoc, mem_erase_top h],
  by_cases h : x = s.top; simp [*, s.top_mem]
end

@[simp] lemma snoc_erase_top_top {s : composition_series X}
  (h : is_maximal s.erase_top.top s.top) : s.erase_top.snoc s.top h = s :=
have h : 0 < s.length,
  from nat.pos_of_ne_zero begin
    assume hs,
    refine ne_of_gt (lt_of_is_maximal h) _,
    simp [top, fin.ext_iff, hs]
  end,
(eq_snoc_erase_top h).symm

/-- Two `composition_series X`, `s₁` and `s₂` are equivalent if there is a bijection
`e : fin s₁.length ≃ fin s₂.length` such that for any `i`,
`iso (s₁ i) (s₁ i.succ) (s₂ (e i), s₂ (e i.succ))` -/
def equivalent (s₁ s₂ : composition_series X) : Prop :=
∃ f : fin s₁.length ≃ fin s₂.length,
  ∀ i : fin s₁.length,
    iso (s₁ i.cast_succ, s₁ i.succ)
    (s₂ (f i).cast_succ, s₂ (f i).succ)

namespace equivalent

@[refl] lemma refl (s : composition_series X) : equivalent s s :=
⟨equiv.refl _, λ _, (s.step _).iso_refl⟩

@[symm] lemma symm {s₁ s₂ : composition_series X} (h : equivalent s₁ s₂) :
  equivalent s₂ s₁ :=
⟨h.some.symm, λ i, iso_symm (by simpa using h.some_spec (h.some.symm i))⟩

@[trans] lemma trans {s₁ s₂ s₃ : composition_series X}
  (h₁ : equivalent s₁ s₂)
  (h₂ : equivalent s₂ s₃) :
  equivalent s₁ s₃ :=
⟨h₁.some.trans h₂.some, λ i, iso_trans (h₁.some_spec i) (h₂.some_spec (h₁.some i))⟩

lemma append
  {s₁ s₂ t₁ t₂ : composition_series X}
  (hs : s₁.top = s₂.bot)
  (ht : t₁.top = t₂.bot)
  (h₁ : equivalent s₁ t₁)
  (h₂ : equivalent s₂ t₂) :
  equivalent (append s₁ s₂ hs) (append t₁ t₂ ht) :=
let e : fin (s₁.length + s₂.length) ≃ fin (t₁.length + t₂.length) :=
  calc fin (s₁.length + s₂.length) ≃ fin s₁.length ⊕ fin s₂.length : fin_sum_fin_equiv.symm
  ... ≃ fin t₁.length ⊕ fin t₂.length : equiv.sum_congr h₁.some h₂.some
  ... ≃ fin (t₁.length + t₂.length) : fin_sum_fin_equiv in
⟨e, begin
  assume i,
  refine fin.add_cases _ _ i,
  { assume i,
    simpa [top, bot] using h₁.some_spec i },
  { assume i,
    simpa [top, bot] using h₂.some_spec i }
end⟩

protected lemma snoc
  {s₁ s₂ : composition_series X}
  {x₁ x₂ : X}
  {hsat₁ : is_maximal s₁.top x₁}
  {hsat₂ : is_maximal s₂.top x₂}
  (hequiv : equivalent s₁ s₂)
  (htop : iso (s₁.top, x₁) (s₂.top, x₂)) :
  equivalent (s₁.snoc x₁ hsat₁) (s₂.snoc x₂ hsat₂) :=
let e : fin s₁.length.succ ≃ fin s₂.length.succ :=
  calc fin (s₁.length + 1) ≃ option (fin s₁.length) : fin_succ_equiv_last
  ... ≃ option (fin s₂.length) : functor.map_equiv option hequiv.some
  ... ≃ fin (s₂.length + 1) : fin_succ_equiv_last.symm in
⟨e,  λ i, begin
  refine fin.last_cases _ _ i,
  { simpa [top] using htop },
  { assume i,
    simpa [fin.succ_cast_succ] using hequiv.some_spec i }
end⟩

lemma length_eq {s₁ s₂ : composition_series X} (h : equivalent s₁ s₂) : s₁.length = s₂.length :=
by simpa using fintype.card_congr h.some

lemma snoc_snoc_swap
  {s : composition_series X}
  {x₁ x₂ y₁ y₂ : X}
  {hsat₁ : is_maximal s.top x₁}
  {hsat₂ : is_maximal s.top x₂}
  {hsaty₁ : is_maximal (snoc s x₁ hsat₁).top y₁}
  {hsaty₂ : is_maximal (snoc s x₂ hsat₂).top y₂}
  (hr₁ : iso (s.top, x₁) (x₂, y₂))
  (hr₂ : iso (x₁, y₁) (s.top, x₂)) :
  equivalent
    (snoc (snoc s x₁ hsat₁) y₁ hsaty₁)
    (snoc (snoc s x₂ hsat₂) y₂ hsaty₂) :=
let e : fin (s.length + 1 + 1) ≃ fin (s.length + 1 + 1) :=
equiv.swap (fin.last _) (fin.cast_succ (fin.last _)) in
have h1 : ∀ {i : fin s.length},
  i.cast_succ.cast_succ ≠ (fin.last _).cast_succ,
  from λ _, ne_of_lt (by simp [fin.cast_succ_lt_last]),
have h2 : ∀ {i : fin s.length},
  i.cast_succ.cast_succ ≠ (fin.last _),
  from λ _, ne_of_lt (by simp [fin.cast_succ_lt_last]),
⟨e, begin
  intro i,
  dsimp only [e],
  refine fin.last_cases _ (λ i, _) i,
  { erw [equiv.swap_apply_left, snoc_cast_succ, snoc_last, fin.succ_last, snoc_last,
      snoc_cast_succ, snoc_cast_succ, fin.succ_cast_succ, snoc_cast_succ,
      fin.succ_last, snoc_last],
    exact hr₂ },
  { refine fin.last_cases _ (λ i, _) i,
    { erw [equiv.swap_apply_right, snoc_cast_succ, snoc_cast_succ,
        snoc_cast_succ, fin.succ_cast_succ, snoc_cast_succ,
        fin.succ_last, snoc_last, snoc_last, fin.succ_last, snoc_last],
      exact hr₁ },
    { erw [equiv.swap_apply_of_ne_of_ne h2 h1, snoc_cast_succ, snoc_cast_succ,
        snoc_cast_succ, snoc_cast_succ, fin.succ_cast_succ, snoc_cast_succ,
        fin.succ_cast_succ, snoc_cast_succ, snoc_cast_succ, snoc_cast_succ],
      exact (s.step i).iso_refl } }
end⟩

end equivalent

lemma length_eq_zero_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero
  {s₁ s₂ : composition_series X}
  (hb : s₁.bot = s₂.bot) (ht : s₁.top = s₂.top)
  (hs₁ : s₁.length = 0) : s₂.length = 0 :=
begin
  have : s₁.bot = s₁.top,
    from congr_arg s₁ (fin.ext (by simp [hs₁])),
  have : (fin.last s₂.length) = (0 : fin s₂.length.succ),
    from s₂.injective (hb.symm.trans (this.trans ht)).symm,
  simpa [fin.ext_iff]
end

lemma length_pos_of_bot_eq_bot_of_top_eq_top_of_length_pos
  {s₁ s₂ : composition_series X}
  (hb : s₁.bot = s₂.bot) (ht : s₁.top = s₂.top) :
  0 < s₁.length → 0 < s₂.length :=
not_imp_not.1 begin
  simp only [pos_iff_ne_zero, ne.def, not_iff_not, not_not],
  exact length_eq_zero_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero hb.symm ht.symm
end

lemma eq_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero
  {s₁ s₂ : composition_series X}
  (hb : s₁.bot = s₂.bot) (ht : s₁.top = s₂.top)
  (hs₁0 : s₁.length = 0) :
  s₁ = s₂ :=
have ∀ x, x ∈ s₁ ↔ x = s₁.top,
  from λ x, ⟨λ hx, forall_mem_eq_of_length_eq_zero hs₁0 hx s₁.top_mem, λ hx, hx.symm ▸ s₁.top_mem⟩,
have ∀ x, x ∈ s₂ ↔ x = s₂.top,
  from λ x, ⟨λ hx, forall_mem_eq_of_length_eq_zero
      (length_eq_zero_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero hb ht hs₁0)
    hx s₂.top_mem, λ hx, hx.symm ▸ s₂.top_mem⟩,
by { ext, simp * }

/-- Given a `composition_series`, `s`, and an element `x`
such that `x` is maximal inside `s.top` there is a series, `t`,
such that `t.top = x`, `t.bot = s.bot`
and `snoc t s.top _` is equivalent to `s`. -/
lemma exists_top_eq_snoc_equivalant (s : composition_series X) (x : X)
  (hm : is_maximal x s.top) (hb : s.bot ≤ x) :
  ∃ t : composition_series X, t.bot = s.bot ∧ t.length + 1 = s.length ∧
    ∃ htx : t.top = x, equivalent s (snoc t s.top (htx.symm ▸ hm)) :=
begin
  induction hn : s.length with n ih generalizing s x,
  { exact (ne_of_gt (lt_of_le_of_lt hb (lt_of_is_maximal hm))
      (forall_mem_eq_of_length_eq_zero hn s.top_mem s.bot_mem)).elim },
  { have h0s : 0 < s.length, from hn.symm ▸ nat.succ_pos _,
    by_cases hetx : s.erase_top.top = x,
    { use s.erase_top,
      simp [← hetx, hn] },
    { have imxs : is_maximal (x ⊓ s.erase_top.top) s.erase_top.top,
        from is_maximal_of_eq_inf x s.top rfl (ne.symm hetx) hm
          (is_maximal_erase_top_top h0s),
      have := ih _ _ imxs (le_inf (by simpa) (le_top_of_mem s.erase_top.bot_mem)) (by simp [hn]),
      rcases this with ⟨t, htb, htl, htt, hteqv⟩,
      have hmtx : is_maximal t.top x,
        from is_maximal_of_eq_inf s.erase_top.top s.top
          (by rw [inf_comm, htt]) hetx
          (is_maximal_erase_top_top h0s) hm,
      use snoc t x hmtx,
      refine ⟨by simp [htb], by simp [htl], by simp, _⟩,
      have : s.equivalent ((snoc t s.erase_top.top (htt.symm ▸ imxs)).snoc s.top
        (by simpa using is_maximal_erase_top_top h0s)),
      { conv_lhs { rw eq_snoc_erase_top h0s },
        exact equivalent.snoc hteqv
          (by simpa using (is_maximal_erase_top_top h0s).iso_refl) },
      refine this.trans _,
      refine equivalent.snoc_snoc_swap _ _,
      { exact iso_symm (second_iso_of_eq hm
          (sup_eq_of_is_maximal hm
            (is_maximal_erase_top_top h0s)
            (ne.symm hetx))
          htt.symm) },
      { exact second_iso_of_eq (is_maximal_erase_top_top h0s)
          (sup_eq_of_is_maximal
            (is_maximal_erase_top_top h0s)
            hm hetx)
          (by rw [inf_comm, htt]) } } }
end

/-- The **Jordan-Hölder** theorem, stated for any `jordan_holder_lattice`.
If two composition series start and finish at the same place, they are equivalent. -/
theorem jordan_holder (s₁ s₂ : composition_series X)
  (hb : s₁.bot = s₂.bot) (ht : s₁.top = s₂.top) :
  equivalent s₁ s₂ :=
begin
  induction hle : s₁.length with n ih generalizing s₁ s₂,
  { rw [eq_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero hb ht hle] },
  { have h0s₂ : 0 < s₂.length,
      from length_pos_of_bot_eq_bot_of_top_eq_top_of_length_pos hb ht (hle.symm ▸ nat.succ_pos _),
    rcases exists_top_eq_snoc_equivalant s₁ s₂.erase_top.top
      (ht.symm ▸ is_maximal_erase_top_top h0s₂)
      (hb.symm ▸ s₂.bot_erase_top ▸ bot_le_of_mem (top_mem _)) with ⟨t, htb, htl, htt, hteq⟩,
    have := ih t s₂.erase_top (by simp [htb, ← hb]) htt (nat.succ_inj'.1 (htl.trans hle)),
    refine hteq.trans _,
    conv_rhs { rw [eq_snoc_erase_top h0s₂] },
    simp only [ht],
    exact equivalent.snoc this
      (by simp [htt, (is_maximal_erase_top_top h0s₂).iso_refl]) }
end

end composition_series
