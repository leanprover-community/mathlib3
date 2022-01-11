/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek
-/
import tactic.apply_fun
import data.nat.cast
import order.rel_iso
import tactic.localized

/-!
# The finite type with `n` elements

`fin n` is the type whose elements are natural numbers smaller than `n`.
This file expands on the development in the core library.

## Main definitions

### Induction principles

* `fin_zero_elim` : Elimination principle for the empty set `fin 0`, generalizes `fin.elim0`.
* `fin.succ_rec` : Define `C n i` by induction on  `i : fin n` interpreted
  as `(0 : fin (n - i)).succ.succ…`. This function has two arguments: `H0 n` defines
  `0`-th element `C (n+1) 0` of an `(n+1)`-tuple, and `Hs n i` defines `(i+1)`-st element
  of `(n+1)`-tuple based on `n`, `i`, and `i`-th element of `n`-tuple.
* `fin.succ_rec_on` : same as `fin.succ_rec` but `i : fin n` is the first argument;
* `fin.induction` : Define `C i` by induction on `i : fin (n + 1)`, separating into the
  `nat`-like base cases of `C 0` and `C (i.succ)`.
* `fin.induction_on` : same as `fin.induction` but with `i : fin (n + 1)` as the first argument.
* `fin.cases` : define `f : Π i : fin n.succ, C i` by separately handling the cases `i = 0` and
  `i = fin.succ j`, `j : fin n`, defined using `fin.induction`.
* `fin.reverse_induction`: reverse induction on `i : fin (n + 1)`; given `C (fin.last n)` and
  `∀ i : fin n, C (fin.succ i) → C (fin.cast_succ i)`, constructs all values `C i` by going down;
* `fin.last_cases`: define `f : Π i, fin (n + 1), C i` by separately handling the cases
  `i = fin.last n` and `i = fin.cast_succ j`, a special case of `fin.reverse_induction`;
* `fin.add_cases`: define a function on `fin (m + n)` by separately handling the cases
  `fin.cast_add n i` and `fin.nat_add m i`;
* `fin.succ_above_cases`: given `i : fin (n + 1)`, define a function on `fin (n + 1)` by separately
  handling the cases `j = i` and `j = fin.succ_above i k`, same as `fin.insert_nth` but marked
  as eliminator and works for `Sort*`.

### Order embeddings and an order isomorphism

* `fin.coe_embedding` : coercion to natural numbers as an `order_embedding`;
* `fin.succ_embedding` : `fin.succ` as an `order_embedding`;
* `fin.cast_le h` : embed `fin n` into `fin m`, `h : n ≤ m`;
* `fin.cast eq` : order isomorphism between `fin n` and fin m` provided that `n = m`,
  see also `equiv.fin_congr`;
* `fin.cast_add m` : embed `fin n` into `fin (n+m)`;
* `fin.cast_succ` : embed `fin n` into `fin (n+1)`;
* `fin.succ_above p` : embed `fin n` into `fin (n + 1)` with a hole around `p`;
* `fin.add_nat m i` : add `m` on `i` on the right, generalizes `fin.succ`;
* `fin.nat_add n i` adds `n` on `i` on the left;

### Other casts

* `fin.of_nat'`: given a positive number `n` (deduced from `[fact (0 < n)]`), `fin.of_nat' i` is
  `i % n` interpreted as an element of `fin n`;
* `fin.cast_lt i h` : embed `i` into a `fin` where `h` proves it belongs into;
* `fin.pred_above (p : fin n) i` : embed `i : fin (n+1)` into `fin n` by subtracting one if `p < i`;
* `fin.cast_pred` : embed `fin (n + 2)` into `fin (n + 1)` by mapping `fin.last (n + 1)` to
  `fin.last n`;
* `fin.sub_nat i h` : subtract `m` from `i ≥ m`, generalizes `fin.pred`;
* `fin.clamp n m` : `min n m` as an element of `fin (m + 1)`;
* `fin.div_nat i` : divides `i : fin (m * n)` by `n`;
* `fin.mod_nat i` : takes the mod of `i : fin (m * n)` by `n`;

### Misc definitions

* `fin.last n` : The greatest value of `fin (n+1)`.

-/

universes u v
open fin nat function

/-- Elimination principle for the empty set `fin 0`, dependent version. -/
def fin_zero_elim {α : fin 0 → Sort u} (x : fin 0) : α x := x.elim0

lemma fact.succ.pos {n} : fact (0 < succ n) := ⟨zero_lt_succ _⟩

lemma fact.bit0.pos {n} [h : fact (0 < n)] : fact (0 < bit0 n) :=
⟨nat.zero_lt_bit0 $ ne_of_gt h.1⟩

lemma fact.bit1.pos {n} : fact (0 < bit1 n) :=
⟨nat.zero_lt_bit1 _⟩

lemma fact.pow.pos {p n : ℕ} [h : fact $ 0 < p] : fact (0 < p ^ n) :=
⟨pow_pos h.1 _⟩

localized "attribute [instance] fact.succ.pos" in fin_fact
localized "attribute [instance] fact.bit0.pos" in fin_fact
localized "attribute [instance] fact.bit1.pos" in fin_fact
localized "attribute [instance] fact.pow.pos" in fin_fact

namespace fin
variables {n m : ℕ} {a b : fin n}

instance fin_to_nat (n : ℕ) : has_coe (fin n) nat := ⟨subtype.val⟩

lemma pos_iff_nonempty {n : ℕ} : 0 < n ↔ nonempty (fin n) :=
⟨λ h, ⟨⟨0, h⟩⟩, λ ⟨i⟩, lt_of_le_of_lt (nat.zero_le _) i.2⟩

section coe

/-!
### coercions and constructions
-/

@[simp] protected lemma eta (a : fin n) (h : (a : ℕ) < n) : (⟨(a : ℕ), h⟩ : fin n) = a :=
by cases a; refl

@[ext]
lemma ext {a b : fin n} (h : (a : ℕ) = b) : a = b := eq_of_veq h

lemma ext_iff (a b : fin n) : a = b ↔ (a : ℕ) = b :=
iff.intro (congr_arg _) fin.eq_of_veq

lemma coe_injective {n : ℕ} : injective (coe : fin n → ℕ) := subtype.coe_injective

lemma eq_iff_veq (a b : fin n) : a = b ↔ a.1 = b.1 :=
⟨veq_of_eq, eq_of_veq⟩

lemma ne_iff_vne (a b : fin n) : a ≠ b ↔ a.1 ≠ b.1 :=
⟨vne_of_ne, ne_of_vne⟩

@[simp] lemma mk_eq_subtype_mk (a : ℕ) (h : a < n) : mk a h = ⟨a, h⟩ := rfl

protected lemma mk.inj_iff {n a b : ℕ} {ha : a < n} {hb : b < n} :
  (⟨a, ha⟩ : fin n) = ⟨b, hb⟩ ↔ a = b :=
subtype.mk_eq_mk

lemma mk_val {m n : ℕ} (h : m < n) : (⟨m, h⟩ : fin n).val = m := rfl

lemma eq_mk_iff_coe_eq {k : ℕ} {hk : k < n} : a = ⟨k, hk⟩ ↔ (a : ℕ) = k :=
fin.eq_iff_veq a ⟨k, hk⟩

@[simp, norm_cast] lemma coe_mk {m n : ℕ} (h : m < n) : ((⟨m, h⟩ : fin n) : ℕ) = m := rfl

lemma mk_coe (i : fin n) : (⟨i, i.property⟩ : fin n) = i :=
fin.eta _ _

lemma coe_eq_val (a : fin n) : (a : ℕ) = a.val := rfl

@[simp] lemma val_eq_coe (a : fin n) : a.val = a := rfl

/-- Assume `k = l`. If two functions defined on `fin k` and `fin l` are equal on each element,
then they coincide (in the heq sense). -/
protected lemma heq_fun_iff {α : Sort*} {k l : ℕ} (h : k = l) {f : fin k → α} {g : fin l → α} :
  f == g ↔ (∀ (i : fin k), f i = g ⟨(i : ℕ), h ▸ i.2⟩) :=
by { induction h, simp [heq_iff_eq, function.funext_iff] }

protected lemma heq_ext_iff {k l : ℕ} (h : k = l) {i : fin k} {j : fin l} :
  i == j ↔ (i : ℕ) = (j : ℕ) :=
by { induction h, simp [ext_iff] }

lemma exists_iff {p : fin n → Prop} : (∃ i, p i) ↔ ∃ i h, p ⟨i, h⟩ :=
⟨λ h, exists.elim h (λ ⟨i, hi⟩ hpi, ⟨i, hi, hpi⟩),
  λ h, exists.elim h (λ i hi, ⟨⟨i, hi.fst⟩, hi.snd⟩)⟩

lemma forall_iff {p : fin n → Prop} : (∀ i, p i) ↔ ∀ i h, p ⟨i, h⟩ :=
⟨λ h i hi, h ⟨i, hi⟩, λ h ⟨i, hi⟩, h i hi⟩

end coe

section order

/-!
### order
-/

lemma is_lt (i : fin n) : (i : ℕ) < n := i.2

lemma is_le (i : fin (n + 1)) : (i : ℕ) ≤ n := le_of_lt_succ i.is_lt

lemma lt_iff_coe_lt_coe : a < b ↔ (a : ℕ) < b := iff.rfl

lemma le_iff_coe_le_coe : a ≤ b ↔ (a : ℕ) ≤ b := iff.rfl

lemma mk_lt_of_lt_coe {a : ℕ} (h : a < b) : (⟨a, h.trans b.is_lt⟩ : fin n) < b := h

lemma mk_le_of_le_coe {a : ℕ} (h : a ≤ b) : (⟨a, h.trans_lt b.is_lt⟩ : fin n) ≤ b := h

/-- `a < b` as natural numbers if and only if `a < b` in `fin n`. -/
@[norm_cast, simp] lemma coe_fin_lt {n : ℕ} {a b : fin n} : (a : ℕ) < (b : ℕ) ↔ a < b :=
iff.rfl

/-- `a ≤ b` as natural numbers if and only if `a ≤ b` in `fin n`. -/
@[norm_cast, simp] lemma coe_fin_le {n : ℕ} {a b : fin n} : (a : ℕ) ≤ (b : ℕ) ↔ a ≤ b :=
iff.rfl

instance {n : ℕ} : linear_order (fin n) :=
{ le := (≤), lt := (<),
  decidable_le := fin.decidable_le,
  decidable_lt := fin.decidable_lt,
  decidable_eq := fin.decidable_eq _,
 ..linear_order.lift (coe : fin n → ℕ) (@fin.eq_of_veq _) }

/-- The inclusion map `fin n → ℕ` is a relation embedding. -/
def coe_embedding (n) : (fin n) ↪o ℕ :=
⟨⟨coe, @fin.eq_of_veq _⟩, λ a b, iff.rfl⟩

/-- The ordering on `fin n` is a well order. -/
instance fin.lt.is_well_order (n) : is_well_order (fin n) (<) :=
(coe_embedding n).is_well_order

/-- Use the ordering on `fin n` for checking recursive definitions.

For example, the following definition is not accepted by the termination checker,
unless we declare the `has_well_founded` instance:
```lean
def factorial {n : ℕ} : fin n → ℕ
| ⟨0, _⟩ := 1
| ⟨i + 1, hi⟩ := (i + 1) * factorial ⟨i, i.lt_succ_self.trans hi⟩
```
-/
instance {n : ℕ} : has_well_founded (fin n) :=
⟨_, measure_wf coe⟩

@[simp] lemma coe_zero {n : ℕ} : ((0 : fin (n+1)) : ℕ) = 0 := rfl
attribute [simp] val_zero
@[simp] lemma val_zero' (n) : (0 : fin (n+1)).val = 0 := rfl
@[simp] lemma mk_zero : (⟨0, nat.succ_pos'⟩ : fin (n + 1)) = (0 : fin _) := rfl

lemma zero_le (a : fin (n + 1)) : 0 ≤ a := zero_le a.1

lemma zero_lt_one : (0 : fin (n + 2)) < 1 := nat.zero_lt_one

lemma pos_iff_ne_zero (a : fin (n+1)) : 0 < a ↔ a ≠ 0 :=
by rw [← coe_fin_lt, coe_zero, pos_iff_ne_zero, ne.def, ne.def, ext_iff, coe_zero]

lemma eq_zero_or_eq_succ {n : ℕ} (i : fin (n+1)) : i = 0 ∨ ∃ j : fin n, i = j.succ :=
begin
  rcases i with ⟨_|j, h⟩,
  { left, refl, },
  { right, exact ⟨⟨j, nat.lt_of_succ_lt_succ h⟩, rfl⟩, }
end

/-- The greatest value of `fin (n+1)` -/
def last (n : ℕ) : fin (n+1) := ⟨_, n.lt_succ_self⟩

@[simp, norm_cast] lemma coe_last (n : ℕ) : (last n : ℕ) = n := rfl

lemma last_val (n : ℕ) : (last n).val = n := rfl

theorem le_last (i : fin (n+1)) : i ≤ last n :=
le_of_lt_succ i.is_lt

instance : bounded_order (fin (n + 1)) :=
{ top := last n,
  le_top := le_last,
  bot := 0,
  bot_le := zero_le }

instance : lattice (fin (n + 1)) := lattice_of_linear_order

lemma last_pos : (0 : fin (n + 2)) < last (n + 1) :=
by simp [lt_iff_coe_lt_coe]

lemma eq_last_of_not_lt {i : fin (n+1)} (h : ¬ (i : ℕ) < n) : i = last n :=
le_antisymm (le_last i) (not_lt.1 h)

lemma top_eq_last (n : ℕ) : ⊤ = fin.last n := rfl

lemma bot_eq_zero (n : ℕ) : ⊥ = (0 : fin (n + 1)) := rfl

section

variables {α : Type*} [preorder α]
open set

/-- If `e` is an `order_iso` between `fin n` and `fin m`, then `n = m` and `e` is the identity
map. In this lemma we state that for each `i : fin n` we have `(e i : ℕ) = (i : ℕ)`. -/
@[simp] lemma coe_order_iso_apply (e : fin n ≃o fin m) (i : fin n) : (e i : ℕ) = i :=
begin
  rcases i with ⟨i, hi⟩,
  rw [subtype.coe_mk],
  induction i using nat.strong_induction_on with i h,
  refine le_antisymm (forall_lt_iff_le.1 $ λ j hj, _) (forall_lt_iff_le.1 $ λ j hj, _),
  { have := e.symm.lt_iff_lt.2 (mk_lt_of_lt_coe hj),
    rw e.symm_apply_apply at this,
    convert this,
    simpa using h _ this (e.symm _).is_lt },
  { rwa [← h j hj (hj.trans hi), ← lt_iff_coe_lt_coe, e.lt_iff_lt] }
end

instance order_iso_subsingleton : subsingleton (fin n ≃o α) :=
⟨λ e e', by { ext i,
  rw [← e.symm.apply_eq_iff_eq, e.symm_apply_apply, ← e'.trans_apply, ext_iff,
    coe_order_iso_apply] }⟩

instance order_iso_subsingleton' : subsingleton (α ≃o fin n) :=
order_iso.symm_injective.subsingleton

instance order_iso_unique : unique (fin n ≃o fin n) := unique.mk' _

/-- Two strictly monotone functions from `fin n` are equal provided that their ranges
are equal. -/
lemma strict_mono_unique {f g : fin n → α} (hf : strict_mono f) (hg : strict_mono g)
  (h : range f = range g) : f = g :=
have (hf.order_iso f).trans (order_iso.set_congr _ _ h) = hg.order_iso g,
  from subsingleton.elim _ _,
congr_arg (function.comp (coe : range g → α)) (funext $ rel_iso.ext_iff.1 this)

/-- Two order embeddings of `fin n` are equal provided that their ranges are equal. -/
lemma order_embedding_eq {f g : fin n ↪o α} (h : range f = range g) : f = g :=
rel_embedding.ext $ funext_iff.1 $ strict_mono_unique f.strict_mono g.strict_mono h

end

/-- A function `f` on `fin n` is strictly monotone if and only if `f i < f (i+1)` for all `i`. -/
lemma strict_mono_iff_lt_succ {α : Type*} [preorder α] {f : fin n → α} :
  strict_mono f ↔ ∀ i (h : i + 1 < n), f ⟨i, lt_of_le_of_lt (nat.le_succ i) h⟩ < f ⟨i+1, h⟩ :=
begin
  split,
  { assume H i hi,
    apply H,
    exact nat.lt_succ_self _ },
  { assume H,
    have A : ∀ i j (h : i < j) (h' : j < n), f ⟨i, lt_trans h h'⟩ < f ⟨j, h'⟩,
    { assume i j h h',
      induction h with k h IH,
      { exact H _ _ },
      { exact lt_trans (IH (nat.lt_of_succ_lt h')) (H _ _) } },
    assume i j hij,
    convert A (i : ℕ) (j : ℕ) hij j.2; ext; simp only [subtype.coe_eta] }
end

end order

section add

/-!
### addition, numerals, and coercion from nat
-/

/-- Given a positive `n`, `fin.of_nat' i` is `i % n` as an element of `fin n`. -/
def of_nat' [h : fact (0 < n)] (i : ℕ) : fin n := ⟨i%n, mod_lt _ h.1⟩

lemma one_val {n : ℕ} : (1 : fin (n+1)).val = 1 % (n+1) := rfl
lemma coe_one' {n : ℕ} : ((1 : fin (n+1)) : ℕ) = 1 % (n+1) := rfl
@[simp] lemma val_one  {n : ℕ} : (1 : fin (n+2)).val = 1 := rfl
@[simp] lemma coe_one  {n : ℕ} : ((1 : fin (n+2)) : ℕ) = 1 := rfl
@[simp] lemma mk_one : (⟨1, nat.succ_lt_succ (nat.succ_pos n)⟩ : fin (n + 2)) = (1 : fin _) := rfl

instance {n : ℕ} : nontrivial (fin (n + 2)) := ⟨⟨0, 1, dec_trivial⟩⟩

section monoid

@[simp] protected lemma add_zero (k : fin (n + 1)) : k + 0 = k :=
by simp [eq_iff_veq, add_def, mod_eq_of_lt (is_lt k)]

@[simp] protected lemma zero_add (k : fin (n + 1)) : (0 : fin (n + 1)) + k = k :=
by simp [eq_iff_veq, add_def, mod_eq_of_lt (is_lt k)]

instance add_comm_monoid (n : ℕ) : add_comm_monoid (fin (n + 1)) :=
{ add := (+),
  add_assoc := by simp [eq_iff_veq, add_def, add_assoc],
  zero := 0,
  zero_add := fin.zero_add,
  add_zero := fin.add_zero,
  add_comm := by simp [eq_iff_veq, add_def, add_comm] }

end monoid

lemma val_add {n : ℕ} : ∀ a b : fin n, (a + b).val = (a.val + b.val) % n
| ⟨_, _⟩ ⟨_, _⟩ := rfl

lemma coe_add {n : ℕ} : ∀ a b : fin n, ((a + b : fin n) : ℕ) = (a + b) % n
| ⟨_, _⟩ ⟨_, _⟩ := rfl

lemma coe_add_eq_ite {n : ℕ} (a b : fin n) :
  (↑(a + b) : ℕ) = if n ≤ a + b then a + b - n else a + b :=
by rw [fin.coe_add, nat.add_mod_eq_ite,
       nat.mod_eq_of_lt (show ↑a < n, from a.2), nat.mod_eq_of_lt (show ↑b < n, from b.2)]

lemma coe_bit0 {n : ℕ} (k : fin n) : ((bit0 k : fin n) : ℕ) = bit0 (k : ℕ) % n :=
by { cases k, refl }

lemma coe_bit1 {n : ℕ} (k : fin (n + 1)) :
  ((bit1 k : fin (n + 1)) : ℕ) = bit1 (k : ℕ) % (n + 1) :=
begin
  cases n, { cases k with k h, cases k, {show _ % _ = _, simp}, cases h with _ h, cases h },
  simp [bit1, fin.coe_bit0, fin.coe_add, fin.coe_one],
end

lemma coe_add_one_of_lt {n : ℕ} {i : fin n.succ} (h : i < last _) :
  (↑(i + 1) : ℕ) = i + 1 :=
begin
  -- First show that `((1 : fin n.succ) : ℕ) = 1`, because `n.succ` is at least 2.
  cases n,
  { cases h },
  -- Then just unfold the definitions.
  rw [fin.coe_add, fin.coe_one, nat.mod_eq_of_lt (nat.succ_lt_succ _)],
  exact h
end

@[simp] lemma last_add_one : ∀ n, last n + 1 = 0
| 0 := subsingleton.elim _ _
| (n + 1) := by { ext, rw [coe_add, coe_zero, coe_last, coe_one, nat.mod_self] }

lemma coe_add_one {n : ℕ} (i : fin (n + 1)) :
  ((i + 1 : fin (n + 1)) : ℕ) = if i = last _ then 0 else i + 1 :=
begin
  rcases (le_last i).eq_or_lt with rfl|h,
  { simp },
  { simpa [h.ne] using coe_add_one_of_lt h }
end

section bit

@[simp] lemma mk_bit0 {m n : ℕ} (h : bit0 m < n) :
  (⟨bit0 m, h⟩ : fin n) = (bit0 ⟨m, (nat.le_add_right m m).trans_lt h⟩ : fin _) :=
eq_of_veq (nat.mod_eq_of_lt h).symm

@[simp] lemma mk_bit1 {m n : ℕ} (h : bit1 m < n + 1) :
  (⟨bit1 m, h⟩ : fin (n + 1)) = (bit1 ⟨m, (nat.le_add_right m m).trans_lt
    ((m + m).lt_succ_self.trans h)⟩ : fin _) :=
begin
  ext,
  simp only [bit1, bit0] at h,
  simp only [bit1, bit0, coe_add, coe_one', coe_mk, ←nat.add_mod, nat.mod_eq_of_lt h],
end

end bit

@[simp] lemma val_two  {n : ℕ} : (2 : fin (n+3)).val = 2 := rfl
@[simp] lemma coe_two  {n : ℕ} : ((2 : fin (n+3)) : ℕ) = 2 := rfl

section of_nat_coe

@[simp]
lemma of_nat_eq_coe (n : ℕ) (a : ℕ) : (of_nat a : fin (n+1)) = a :=
begin
  induction a with a ih, { refl },
  ext, show (a+1) % (n+1) = subtype.val (a+1 : fin (n+1)),
  { rw [val_add, ← ih, of_nat],
    exact add_mod _ _ _ }
end

/-- Converting an in-range number to `fin (n + 1)` produces a result
whose value is the original number.  -/
lemma coe_val_of_lt {n : ℕ} {a : ℕ} (h : a < n + 1) :
  ((a : fin (n + 1)).val) = a :=
begin
  rw ←of_nat_eq_coe,
  exact nat.mod_eq_of_lt h
end

/-- Converting the value of a `fin (n + 1)` to `fin (n + 1)` results
in the same value.  -/
lemma coe_val_eq_self {n : ℕ} (a : fin (n + 1)) : (a.val : fin (n + 1)) = a :=
begin
  rw fin.eq_iff_veq,
  exact coe_val_of_lt a.property
end

/-- Coercing an in-range number to `fin (n + 1)`, and converting back
to `ℕ`, results in that number. -/
lemma coe_coe_of_lt {n : ℕ} {a : ℕ} (h : a < n + 1) :
  ((a : fin (n + 1)) : ℕ) = a :=
coe_val_of_lt h

/-- Converting a `fin (n + 1)` to `ℕ` and back results in the same
value. -/
@[simp] lemma coe_coe_eq_self {n : ℕ} (a : fin (n + 1)) : ((a : ℕ) : fin (n + 1)) = a :=
coe_val_eq_self a

lemma coe_nat_eq_last (n) : (n : fin (n + 1)) = fin.last n :=
by { rw [←fin.of_nat_eq_coe, fin.of_nat, fin.last], simp only [nat.mod_eq_of_lt n.lt_succ_self] }

lemma le_coe_last (i : fin (n + 1)) : i ≤ n :=
by { rw fin.coe_nat_eq_last, exact fin.le_last i }

end of_nat_coe

lemma add_one_pos (i : fin (n + 1)) (h : i < fin.last n) : (0 : fin (n + 1)) < i + 1 :=
begin
  cases n,
  { exact absurd h (nat.not_lt_zero _) },
  { rw [lt_iff_coe_lt_coe, coe_last, ←add_lt_add_iff_right 1] at h,
    rw [lt_iff_coe_lt_coe, coe_add, coe_zero, coe_one, nat.mod_eq_of_lt h],
    exact nat.zero_lt_succ _ }
end

lemma one_pos : (0 : fin (n + 2)) < 1 := succ_pos 0

lemma zero_ne_one : (0 : fin (n + 2)) ≠ 1 := ne_of_lt one_pos

@[simp] lemma zero_eq_one_iff : (0 : fin (n + 1)) = 1 ↔ n = 0 :=
begin
  split,
  { cases n; intro h,
    { refl },
    { have := zero_ne_one, contradiction } },
  { rintro rfl, refl }
end

@[simp] lemma one_eq_zero_iff : (1 : fin (n + 1)) = 0 ↔ n = 0 :=
by rw [eq_comm, zero_eq_one_iff]

end add

section succ

/-!
### succ and casts into larger fin types
-/

@[simp] lemma coe_succ (j : fin n) : (j.succ : ℕ) = j + 1 :=
by cases j; simp [fin.succ]

lemma succ_pos (a : fin n) : (0 : fin (n + 1)) < a.succ := by simp [lt_iff_coe_lt_coe]

/-- `fin.succ` as an `order_embedding` -/
def succ_embedding (n : ℕ) : fin n ↪o fin (n + 1) :=
order_embedding.of_strict_mono fin.succ $ λ ⟨i, hi⟩ ⟨j, hj⟩ h, succ_lt_succ h

@[simp] lemma coe_succ_embedding : ⇑(succ_embedding n) = fin.succ := rfl

@[simp] lemma succ_le_succ_iff : a.succ ≤ b.succ ↔ a ≤ b :=
(succ_embedding n).le_iff_le

@[simp] lemma succ_lt_succ_iff : a.succ < b.succ ↔ a < b :=
(succ_embedding n).lt_iff_lt

lemma succ_injective (n : ℕ) : injective (@fin.succ n) :=
(succ_embedding n).injective

@[simp] lemma succ_inj {a b : fin n} : a.succ = b.succ ↔ a = b :=
(succ_injective n).eq_iff

lemma succ_ne_zero {n} : ∀ k : fin n, fin.succ k ≠ 0
| ⟨k, hk⟩ heq := nat.succ_ne_zero k $ (ext_iff _ _).1 heq

@[simp] lemma succ_zero_eq_one : fin.succ (0 : fin (n + 1)) = 1 := rfl

@[simp] lemma succ_one_eq_two : fin.succ (1 : fin (n + 2)) = 2 := rfl

@[simp] lemma succ_mk (n i : ℕ) (h : i < n) : fin.succ ⟨i, h⟩ = ⟨i + 1, nat.succ_lt_succ h⟩ :=
rfl

lemma mk_succ_pos (i : ℕ) (h : i < n) : (0 : fin (n + 1)) < ⟨i.succ, add_lt_add_right h 1⟩ :=
by { rw [lt_iff_coe_lt_coe, coe_zero], exact nat.succ_pos i }

lemma one_lt_succ_succ (a : fin n) : (1 : fin (n + 2)) < a.succ.succ :=
begin
  cases n,
  { exact fin_zero_elim a },
  { rw [←succ_zero_eq_one, succ_lt_succ_iff], exact succ_pos a }
end

lemma succ_succ_ne_one (a : fin n) : fin.succ (fin.succ a) ≠ 1 := ne_of_gt (one_lt_succ_succ a)

/-- `cast_lt i h` embeds `i` into a `fin` where `h` proves it belongs into.  -/
def cast_lt (i : fin m) (h : i.1 < n) : fin n := ⟨i.1, h⟩

@[simp] lemma coe_cast_lt (i : fin m) (h : i.1 < n) : (cast_lt i h : ℕ) = i := rfl

@[simp] lemma cast_lt_mk (i n m : ℕ) (hn : i < n) (hm : i < m) : cast_lt ⟨i, hn⟩ hm = ⟨i, hm⟩ := rfl

/-- `cast_le h i` embeds `i` into a larger `fin` type.  -/
def cast_le (h : n ≤ m) : fin n ↪o fin m :=
order_embedding.of_strict_mono (λ a, cast_lt a (lt_of_lt_of_le a.2 h)) $ λ a b h, h

@[simp] lemma coe_cast_le (h : n ≤ m) (i : fin n) : (cast_le h i : ℕ) = i := rfl

@[simp] lemma cast_le_mk (i n m : ℕ) (hn : i < n) (h : n ≤ m) :
  cast_le h ⟨i, hn⟩ = ⟨i, lt_of_lt_of_le hn h⟩ := rfl

@[simp] lemma cast_le_zero {n m : ℕ} (h : n.succ ≤ m.succ) :
  cast_le h 0 = 0 :=
by simp [eq_iff_veq]

@[simp] lemma range_cast_le {n k : ℕ} (h : n ≤ k) :
  set.range (cast_le h) = {i | (i : ℕ) < n} :=
set.ext (λ x, ⟨λ ⟨y, hy⟩, hy ▸ y.2, λ hx, ⟨⟨x, hx⟩, fin.ext rfl⟩⟩)

@[simp] lemma coe_of_injective_cast_le_symm {n k : ℕ} (h : n ≤ k) (i : fin k) (hi) :
  ((equiv.of_injective _ (cast_le h).injective).symm ⟨i, hi⟩ : ℕ) = i :=
begin
  rw ← coe_cast_le,
  exact congr_arg coe (equiv.apply_of_injective_symm _ _ _)
end

@[simp] lemma cast_le_succ {m n : ℕ} (h : (m + 1) ≤ (n + 1)) (i : fin m) :
  cast_le h i.succ = (cast_le (nat.succ_le_succ_iff.mp h) i).succ :=
by simp [fin.eq_iff_veq]

/-- `cast eq i` embeds `i` into a equal `fin` type, see also `equiv.fin_congr`. -/
def cast (eq : n = m) : fin n ≃o fin m :=
{ to_equiv := ⟨cast_le eq.le, cast_le eq.symm.le, λ a, eq_of_veq rfl, λ a, eq_of_veq rfl⟩,
  map_rel_iff' := λ a b, iff.rfl }

@[simp] lemma symm_cast (h : n = m) : (cast h).symm = cast h.symm := rfl

/-- While `fin.coe_order_iso_apply` is a more general case of this, we mark this `simp` anyway
as it is eligible for `dsimp`. -/
@[simp]
lemma coe_cast (h : n = m) (i : fin n) : (cast h i : ℕ) = i := rfl

@[simp] lemma cast_mk (h : n = m) (i : ℕ) (hn : i < n) :
  cast h ⟨i, hn⟩ = ⟨i, lt_of_lt_of_le hn h.le⟩ := rfl

@[simp] lemma cast_trans {k : ℕ} (h : n = m) (h' : m = k) {i : fin n} :
  cast h' (cast h i) = cast (eq.trans h h') i := rfl

@[simp] lemma cast_refl (h : n = n := rfl) : cast h = order_iso.refl (fin n) :=
by { ext, refl }

/-- While in many cases `fin.cast` is better than `equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
lemma cast_to_equiv (h : n = m) : (cast h).to_equiv = equiv.cast (h ▸ rfl) :=
by { subst h, simp }

/-- While in many cases `fin.cast` is better than `equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
lemma cast_eq_cast (h : n = m) : (cast h : fin n → fin m) = _root_.cast (h ▸ rfl) :=
by { subst h, ext, simp }

/-- `cast_add m i` embeds `i : fin n` in `fin (n+m)`. See also `fin.nat_add` and `fin.add_nat`. -/
def cast_add (m) : fin n ↪o fin (n + m) := cast_le $ nat.le_add_right n m

@[simp] lemma coe_cast_add (m : ℕ) (i : fin n) : (cast_add m i : ℕ) = i := rfl

lemma cast_add_lt {m : ℕ} (n : ℕ) (i : fin m) : (cast_add n i : ℕ) < m := i.2

@[simp] lemma cast_add_mk (m : ℕ) (i : ℕ) (h : i < n) :
  cast_add m ⟨i, h⟩ = ⟨i, lt_add_right i n m h⟩ := rfl

@[simp] lemma cast_add_cast_lt (m : ℕ) (i : fin (n + m)) (hi : i.val < n) :
  cast_add m (cast_lt i hi) = i :=
ext rfl

@[simp] lemma cast_lt_cast_add (m : ℕ) (i : fin n) :
  cast_lt (cast_add m i) (cast_add_lt m i) = i :=
ext rfl

/-- For rewriting in the reverse direction, see `fin.cast_cast_add_left`. -/
lemma cast_add_cast {n n' : ℕ} (m : ℕ) (i : fin n') (h : n' = n) :
  cast_add m (fin.cast h i) = fin.cast (congr_arg _ h) (cast_add m i) :=
ext rfl

lemma cast_cast_add_left {n n' m : ℕ} (i : fin n') (h : n' + m = n + m) :
  cast h (cast_add m i) = cast_add m (cast (add_right_cancel h) i) :=
ext rfl

@[simp] lemma cast_cast_add_right {n m m' : ℕ} (i : fin n) (h : n + m' = n + m) :
  cast h (cast_add m' i) = cast_add m i :=
ext rfl

/-- The cast of the successor is the succesor of the cast. See `fin.succ_cast_eq` for rewriting in
the reverse direction. -/
@[simp] lemma cast_succ_eq {n' : ℕ} (i : fin n) (h : n.succ = n'.succ) :
  cast h i.succ = (cast (nat.succ.inj h) i).succ :=
ext $ by simp

lemma succ_cast_eq {n' : ℕ} (i : fin n) (h : n = n') : (cast h i).succ = cast (by rw h) i.succ :=
ext $ by simp

/-- `cast_succ i` embeds `i : fin n` in `fin (n+1)`. -/
def cast_succ : fin n ↪o fin (n + 1) := cast_add 1

@[simp] lemma coe_cast_succ (i : fin n) : (i.cast_succ : ℕ) = i := rfl

@[simp] lemma cast_succ_mk (n i : ℕ) (h : i < n) : cast_succ ⟨i, h⟩ = ⟨i, nat.lt.step h⟩ := rfl

lemma cast_succ_lt_succ (i : fin n) : i.cast_succ < i.succ :=
lt_iff_coe_lt_coe.2 $ by simp only [coe_cast_succ, coe_succ, nat.lt_succ_self]

lemma le_cast_succ_iff {i : fin (n + 1)} {j : fin n} : i ≤ j.cast_succ ↔ i < j.succ :=
by simpa [lt_iff_coe_lt_coe, le_iff_coe_le_coe] using nat.succ_le_succ_iff.symm

@[simp] lemma succ_last (n : ℕ) : (last n).succ = last (n.succ) := rfl

@[simp] lemma succ_eq_last_succ {n : ℕ} (i : fin n.succ) :
  i.succ = last (n + 1) ↔ i = last n :=
by rw [← succ_last, (succ_injective _).eq_iff]

@[simp] lemma cast_succ_cast_lt (i : fin (n + 1)) (h : (i : ℕ) < n) : cast_succ (cast_lt i h) = i :=
fin.eq_of_veq rfl

@[simp] lemma cast_lt_cast_succ {n : ℕ} (a : fin n) (h : (a : ℕ) < n) :
  cast_lt (cast_succ a) h = a :=
by cases a; refl

@[simp] lemma cast_succ_lt_cast_succ_iff : a.cast_succ < b.cast_succ ↔ a < b :=
(@cast_succ n).lt_iff_lt

lemma cast_succ_injective (n : ℕ) : injective (@fin.cast_succ n) :=
(cast_succ : fin n ↪o _).injective

lemma cast_succ_inj {a b : fin n} : a.cast_succ = b.cast_succ ↔ a = b :=
(cast_succ_injective n).eq_iff

lemma cast_succ_lt_last (a : fin n) : cast_succ a < last n := lt_iff_coe_lt_coe.mpr a.is_lt

@[simp] lemma cast_succ_zero : cast_succ (0 : fin (n + 1)) = 0 := rfl

@[simp] lemma cast_succ_one {n : ℕ} : fin.cast_succ (1 : fin (n + 2)) = 1 := rfl

/-- `cast_succ i` is positive when `i` is positive -/
lemma cast_succ_pos {i : fin (n + 1)} (h : 0 < i) : 0 < cast_succ i :=
by simpa [lt_iff_coe_lt_coe] using h

@[simp] lemma cast_succ_eq_zero_iff (a : fin (n + 1)) : a.cast_succ = 0 ↔ a = 0 :=
subtype.ext_iff.trans $ (subtype.ext_iff.trans $ by exact iff.rfl).symm

lemma cast_succ_ne_zero_iff (a : fin (n + 1)) : a.cast_succ ≠ 0 ↔ a ≠ 0 :=
not_iff_not.mpr $ cast_succ_eq_zero_iff a

lemma cast_succ_fin_succ (n : ℕ) (j : fin n) :
  cast_succ (fin.succ j) = fin.succ (cast_succ j) :=
by simp [fin.ext_iff]

@[norm_cast, simp] lemma coe_eq_cast_succ : (a : fin (n + 1)) = a.cast_succ :=
begin
  ext,
  exact coe_val_of_lt (nat.lt.step a.is_lt),
end

@[simp] lemma coe_succ_eq_succ : a.cast_succ + 1 = a.succ :=
begin
  cases n,
  { exact fin_zero_elim a },
  { simp [a.is_lt, eq_iff_veq, add_def, nat.mod_eq_of_lt] }
end

lemma lt_succ : a.cast_succ < a.succ :=
by { rw [cast_succ, lt_iff_coe_lt_coe, coe_cast_add, coe_succ], exact lt_add_one a.val }

@[simp] lemma range_cast_succ {n : ℕ} :
  set.range (cast_succ : fin n → fin n.succ) = {i | (i : ℕ) < n} :=
range_cast_le _

@[simp] lemma coe_of_injective_cast_succ_symm {n : ℕ} (i : fin n.succ) (hi) :
  ((equiv.of_injective cast_succ (cast_succ_injective _)).symm ⟨i, hi⟩ : ℕ) = i :=
begin
  rw ← coe_cast_succ,
  exact congr_arg coe (equiv.apply_of_injective_symm _ _ _)
end

lemma succ_cast_succ {n : ℕ} (i : fin n) :
  i.cast_succ.succ = i.succ.cast_succ :=
fin.ext (by simp)

/-- `add_nat m i` adds `m` to `i`, generalizes `fin.succ`. -/
def add_nat (m) : fin n ↪o fin (n + m) :=
order_embedding.of_strict_mono (λ i, ⟨(i : ℕ) + m, add_lt_add_right i.2 _⟩) $
  λ i j h, lt_iff_coe_lt_coe.2 $ add_lt_add_right h _

@[simp] lemma coe_add_nat (m : ℕ) (i : fin n) : (add_nat m i : ℕ) = i + m := rfl

lemma le_coe_add_nat (m : ℕ) (i : fin n) : m ≤ add_nat m i := nat.le_add_left _ _

@[simp] lemma add_nat_mk (n i : ℕ) (hi : i < m) :
  add_nat n ⟨i, hi⟩ = ⟨i + n, add_lt_add_right hi n⟩ := rfl

@[simp] lemma cast_add_nat_zero {n n' : ℕ} (i : fin n) (h : n + 0 = n') :
  cast h (add_nat 0 i) = cast ((add_zero _).symm.trans h) i :=
ext $ add_zero _

/-- For rewriting in the reverse direction, see `fin.cast_add_nat_left`. -/
lemma add_nat_cast {n n' m : ℕ} (i : fin n') (h : n' = n) :
  add_nat m (cast h i) = cast (congr_arg _ h) (add_nat m i) :=
ext rfl

lemma cast_add_nat_left {n n' m : ℕ} (i : fin n') (h : n' + m = n + m) :
  cast h (add_nat m i) = add_nat m (cast (add_right_cancel h) i) :=
ext rfl

@[simp] lemma cast_add_nat_right {n m m' : ℕ} (i : fin n) (h : n + m' = n + m) :
  cast h (add_nat m' i) = add_nat m i :=
ext $ (congr_arg ((+) (i : ℕ)) (add_left_cancel h) : _)

/-- `nat_add n i` adds `n` to `i` "on the left". -/
def nat_add (n) {m} : fin m ↪o fin (n + m) :=
order_embedding.of_strict_mono (λ i, ⟨n + (i : ℕ), add_lt_add_left i.2 _⟩) $
  λ i j h, lt_iff_coe_lt_coe.2 $ add_lt_add_left h _

@[simp] lemma coe_nat_add (n : ℕ) {m : ℕ} (i : fin m) : (nat_add n i : ℕ) = n + i := rfl

@[simp] lemma nat_add_mk (n i : ℕ) (hi : i < m) :
  nat_add n ⟨i, hi⟩ = ⟨n + i, add_lt_add_left hi n⟩ := rfl

lemma le_coe_nat_add (m : ℕ) (i : fin n) : m ≤ nat_add m i := nat.le_add_right _ _

lemma nat_add_zero {n : ℕ} : fin.nat_add 0 = (fin.cast (zero_add n).symm).to_rel_embedding :=
by { ext, apply zero_add }

/-- For rewriting in the reverse direction, see `fin.cast_nat_add_right`. -/
lemma nat_add_cast {n n' : ℕ} (m : ℕ) (i : fin n') (h : n' = n) :
  nat_add m (cast h i) = cast (congr_arg _ h) (nat_add m i) :=
ext rfl

lemma cast_nat_add_right {n n' m : ℕ} (i : fin n') (h : m + n' = m + n) :
  cast h (nat_add m i) = nat_add m (cast (add_left_cancel h) i) :=
ext rfl

@[simp] lemma cast_nat_add_left {n m m' : ℕ} (i : fin n) (h : m' + n = m + n) :
  cast h (nat_add m' i) = nat_add m i :=
ext $ (congr_arg (+ (i : ℕ)) (add_right_cancel h) : _)

@[simp] lemma cast_nat_add_zero {n n' : ℕ} (i : fin n) (h : 0 + n = n') :
  cast h (nat_add 0 i) = cast ((zero_add _).symm.trans h) i :=
ext $ zero_add _

@[simp] lemma cast_nat_add (n : ℕ) {m : ℕ} (i : fin m) :
  cast (add_comm _ _) (nat_add n i) = add_nat n i :=
ext $ add_comm _ _

@[simp] lemma cast_add_nat {n : ℕ} (m : ℕ) (i : fin n) :
  cast (add_comm _ _) (add_nat m i) = nat_add m i :=
ext $ add_comm _ _

end succ

section pred

/-!
### pred
-/

@[simp] lemma coe_pred (j : fin (n+1)) (h : j ≠ 0) : (j.pred h : ℕ) = j - 1 :=
by { cases j, refl }

@[simp] lemma succ_pred : ∀(i : fin (n+1)) (h : i ≠ 0), (i.pred h).succ = i
| ⟨0,     h⟩ hi := by contradiction
| ⟨n + 1, h⟩ hi := rfl

@[simp] lemma pred_succ (i : fin n) {h : i.succ ≠ 0} : i.succ.pred h = i :=
by { cases i, refl }

@[simp] lemma pred_mk_succ (i : ℕ) (h : i < n + 1) :
  fin.pred ⟨i + 1, add_lt_add_right h 1⟩ (ne_of_vne (ne_of_gt (mk_succ_pos i h))) = ⟨i, h⟩ :=
by simp only [ext_iff, coe_pred, coe_mk, add_tsub_cancel_right]

-- This is not a simp lemma by default, because `pred_mk_succ` is nicer when it applies.
lemma pred_mk {n : ℕ} (i : ℕ) (h : i < n + 1) (w) :
  fin.pred ⟨i, h⟩ w =
  ⟨i - 1, by rwa tsub_lt_iff_right (nat.succ_le_of_lt $ nat.pos_of_ne_zero (fin.vne_of_ne w))⟩ :=
rfl

@[simp] lemma pred_le_pred_iff {n : ℕ} {a b : fin n.succ} {ha : a ≠ 0} {hb : b ≠ 0} :
  a.pred ha ≤ b.pred hb ↔ a ≤ b :=
by rw [←succ_le_succ_iff, succ_pred, succ_pred]

@[simp] lemma pred_lt_pred_iff {n : ℕ} {a b : fin n.succ} {ha : a ≠ 0} {hb : b ≠ 0} :
  a.pred ha < b.pred hb ↔ a < b :=
by rw [←succ_lt_succ_iff, succ_pred, succ_pred]

@[simp] lemma pred_inj :
  ∀ {a b : fin (n + 1)} {ha : a ≠ 0} {hb : b ≠ 0}, a.pred ha = b.pred hb ↔ a = b
| ⟨0,   _⟩  b         ha hb := by contradiction
| ⟨i+1, _⟩  ⟨0,   _⟩  ha hb := by contradiction
| ⟨i+1, hi⟩ ⟨j+1, hj⟩ ha hb := by simp [fin.eq_iff_veq]

@[simp] lemma pred_one {n : ℕ} : fin.pred (1 : fin (n + 2)) (ne.symm (ne_of_lt one_pos)) = 0 := rfl

lemma pred_add_one (i : fin (n + 2)) (h : (i : ℕ) < n + 1) :
  pred (i + 1) (ne_of_gt (add_one_pos _ (lt_iff_coe_lt_coe.mpr h))) = cast_lt i h :=
begin
  rw [ext_iff, coe_pred, coe_cast_lt, coe_add, coe_one, mod_eq_of_lt, add_tsub_cancel_right],
  exact add_lt_add_right h 1,
end

/-- `sub_nat i h` subtracts `m` from `i`, generalizes `fin.pred`. -/
def sub_nat (m) (i : fin (n + m)) (h : m ≤ (i : ℕ)) : fin n :=
⟨(i : ℕ) - m, by { rw [tsub_lt_iff_right h], exact i.is_lt }⟩

@[simp] lemma coe_sub_nat (i : fin (n + m)) (h : m ≤ i) : (i.sub_nat m h : ℕ) = i - m :=
rfl

@[simp] lemma sub_nat_mk {i : ℕ} (h₁ : i < n + m) (h₂ : m ≤ i) :
  sub_nat m ⟨i, h₁⟩ h₂ = ⟨i - m, (tsub_lt_iff_right h₂).2 h₁⟩ :=
rfl

@[simp] lemma pred_cast_succ_succ (i : fin n) :
  pred (cast_succ i.succ) (ne_of_gt (cast_succ_pos i.succ_pos)) = i.cast_succ :=
by simp [eq_iff_veq]

@[simp] lemma add_nat_sub_nat {i : fin (n + m)} (h : m ≤ i) :
  add_nat m (sub_nat m i h) = i :=
ext $ tsub_add_cancel_of_le h

@[simp] lemma sub_nat_add_nat (i : fin n) (m : ℕ) (h : m ≤ add_nat m i := le_coe_add_nat m i) :
  sub_nat m (add_nat m i) h = i :=
ext $ add_tsub_cancel_right i m

@[simp] lemma nat_add_sub_nat_cast {i : fin (n + m)} (h : n ≤ i) :
  nat_add n (sub_nat n (cast (add_comm _ _) i) h) = i :=
by simp [← cast_add_nat]

end pred

section div_mod

/-- Compute `i / n`, where `n` is a `nat` and inferred the type of `i`. -/
def div_nat (i : fin (m * n)) : fin m :=
⟨i / n, nat.div_lt_of_lt_mul $ mul_comm m n ▸ i.prop⟩

@[simp] lemma coe_div_nat (i : fin (m * n)) : (i.div_nat : ℕ) = i / n := rfl

/-- Compute `i % n`, where `n` is a `nat` and inferred the type of `i`. -/
def mod_nat (i : fin (m * n)) : fin n :=
⟨i % n, nat.mod_lt _ $ pos_of_mul_pos_left ((nat.zero_le i).trans_lt i.is_lt) m.zero_le⟩

@[simp] lemma coe_mod_nat (i : fin (m * n)) : (i.mod_nat : ℕ) = i % n := rfl

end div_mod

section rec

/-!
### recursion and induction principles
-/

/-- Define `C n i` by induction on `i : fin n` interpreted as `(0 : fin (n - i)).succ.succ…`.
This function has two arguments: `H0 n` defines `0`-th element `C (n+1) 0` of an `(n+1)`-tuple,
and `Hs n i` defines `(i+1)`-st element of `(n+1)`-tuple based on `n`, `i`, and `i`-th element
of `n`-tuple. -/
@[elab_as_eliminator] def succ_rec
  {C : Π n, fin n → Sort*}
  (H0 : Π n, C (succ n) 0)
  (Hs : Π n i, C n i → C (succ n) i.succ) : Π {n : ℕ} (i : fin n), C n i
| 0        i           := i.elim0
| (succ n) ⟨0, _⟩      := H0 _
| (succ n) ⟨succ i, h⟩ := Hs _ _ (succ_rec ⟨i, lt_of_succ_lt_succ h⟩)

/-- Define `C n i` by induction on `i : fin n` interpreted as `(0 : fin (n - i)).succ.succ…`.
This function has two arguments: `H0 n` defines `0`-th element `C (n+1) 0` of an `(n+1)`-tuple,
and `Hs n i` defines `(i+1)`-st element of `(n+1)`-tuple based on `n`, `i`, and `i`-th element
of `n`-tuple.

A version of `fin.succ_rec` taking `i : fin n` as the first argument. -/
@[elab_as_eliminator] def succ_rec_on {n : ℕ} (i : fin n)
  {C : Π n, fin n → Sort*}
  (H0 : Π n, C (succ n) 0)
  (Hs : Π n i, C n i → C (succ n) i.succ) : C n i :=
i.succ_rec H0 Hs

@[simp] theorem succ_rec_on_zero {C : ∀ n, fin n → Sort*} {H0 Hs} (n) :
  @fin.succ_rec_on (succ n) 0 C H0 Hs = H0 n :=
rfl

@[simp] theorem succ_rec_on_succ {C : ∀ n, fin n → Sort*} {H0 Hs} {n} (i : fin n) :
  @fin.succ_rec_on (succ n) i.succ C H0 Hs = Hs n i (fin.succ_rec_on i H0 Hs) :=
by cases i; refl

/--
Define `C i` by induction on `i : fin (n + 1)` via induction on the underlying `nat` value.
This function has two arguments: `h0` handles the base case on `C 0`,
and `hs` defines the inductive step using `C i.cast_succ`.
-/
@[elab_as_eliminator] def induction
  {C : fin (n + 1) → Sort*}
  (h0 : C 0)
  (hs : ∀ i : fin n, C i.cast_succ → C i.succ) :
  Π (i : fin (n + 1)), C i :=
begin
  rintro ⟨i, hi⟩,
  induction i with i IH,
  { rwa [fin.mk_zero] },
  { refine hs ⟨i, lt_of_succ_lt_succ hi⟩ _,
    exact IH (lt_of_succ_lt hi) }
end

/--
Define `C i` by induction on `i : fin (n + 1)` via induction on the underlying `nat` value.
This function has two arguments: `h0` handles the base case on `C 0`,
and `hs` defines the inductive step using `C i.cast_succ`.

A version of `fin.induction` taking `i : fin (n + 1)` as the first argument.
-/
@[elab_as_eliminator] def induction_on (i : fin (n + 1))
  {C : fin (n + 1) → Sort*}
  (h0 : C 0)
  (hs : ∀ i : fin n, C i.cast_succ → C i.succ) : C i :=
induction h0 hs i

/-- Define `f : Π i : fin n.succ, C i` by separately handling the cases `i = 0` and
`i = j.succ`, `j : fin n`. -/
@[elab_as_eliminator] def cases
  {C : fin (succ n) → Sort*} (H0 : C 0) (Hs : Π i : fin n, C (i.succ)) :
  Π (i : fin (succ n)), C i :=
induction H0 (λ i _, Hs i)

@[simp] theorem cases_zero {n} {C : fin (succ n) → Sort*} {H0 Hs} : @fin.cases n C H0 Hs 0 = H0 :=
rfl

@[simp] theorem cases_succ {n} {C : fin (succ n) → Sort*} {H0 Hs} (i : fin n) :
  @fin.cases n C H0 Hs i.succ = Hs i :=
by cases i; refl

@[simp] theorem cases_succ' {n} {C : fin (succ n) → Sort*} {H0 Hs} {i : ℕ} (h : i + 1 < n + 1) :
  @fin.cases n C H0 Hs ⟨i.succ, h⟩ = Hs ⟨i, lt_of_succ_lt_succ h⟩ :=
by cases i; refl

lemma forall_fin_succ {P : fin (n+1) → Prop} :
  (∀ i, P i) ↔ P 0 ∧ (∀ i:fin n, P i.succ) :=
⟨λ H, ⟨H 0, λ i, H _⟩, λ ⟨H0, H1⟩ i, fin.cases H0 H1 i⟩

lemma exists_fin_succ {P : fin (n+1) → Prop} :
  (∃ i, P i) ↔ P 0 ∨ (∃i:fin n, P i.succ) :=
⟨λ ⟨i, h⟩, fin.cases or.inl (λ i hi, or.inr ⟨i, hi⟩) i h,
  λ h, or.elim h (λ h, ⟨0, h⟩) $ λ⟨i, hi⟩, ⟨i.succ, hi⟩⟩

lemma forall_fin_one {p : fin 1 → Prop} : (∀ i, p i) ↔ p 0 := @unique.forall_iff (fin 1) _ p
lemma exists_fin_one {p : fin 1 → Prop} : (∃ i, p i) ↔ p 0 := @unique.exists_iff (fin 1) _ p

lemma forall_fin_two {p : fin 2 → Prop} : (∀ i, p i) ↔ p 0 ∧ p 1 :=
forall_fin_succ.trans $ and_congr_right $ λ _, forall_fin_one

lemma exists_fin_two {p : fin 2 → Prop} : (∃ i, p i) ↔ p 0 ∨ p 1 :=
exists_fin_succ.trans $ or_congr_right exists_fin_one

lemma fin_two_eq_of_eq_zero_iff {a b : fin 2} (h : a = 0 ↔ b = 0) : a = b :=
by { revert a b, simp [forall_fin_two] }

/--
Define `C i` by reverse induction on `i : fin (n + 1)` via induction on the underlying `nat` value.
This function has two arguments: `hlast` handles the base case on `C (fin.last n)`,
and `hs` defines the inductive step using `C i.succ`, inducting downwards.
-/
@[elab_as_eliminator]
def reverse_induction {n : ℕ}
  {C : fin (n + 1) → Sort*}
  (hlast : C (fin.last n))
  (hs : ∀ i : fin n, C i.succ → C i.cast_succ) :
  Π (i : fin (n + 1)), C i
| i :=
if hi : i = fin.last n
then _root_.cast (by rw hi) hlast
else
  let j : fin n := ⟨i, lt_of_le_of_ne (nat.le_of_lt_succ i.2) (λ h, hi (fin.ext h))⟩ in
  have wf : n + 1 - j.succ < n + 1 - i, begin
    cases i,
    rw [tsub_lt_tsub_iff_left_of_le];
    simp [*, nat.succ_le_iff],
  end,
  have hi : i = fin.cast_succ j, from fin.ext rfl,
_root_.cast (by rw hi) (hs _ (reverse_induction j.succ))
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ i : fin (n+1), n + 1 - i)⟩],
  dec_tac := `[assumption] }

@[simp] lemma reverse_induction_last {n : ℕ}
  {C : fin (n + 1) → Sort*}
  (h0 : C (fin.last n))
  (hs : ∀ i : fin n, C i.succ → C i.cast_succ) :
  (reverse_induction h0 hs (fin.last n) : C (fin.last n)) = h0 :=
by rw [reverse_induction]; simp

@[simp] lemma reverse_induction_cast_succ {n : ℕ}
  {C : fin (n + 1) → Sort*}
  (h0 : C (fin.last n))
  (hs : ∀ i : fin n, C i.succ → C i.cast_succ) (i : fin n):
  (reverse_induction h0 hs i.cast_succ : C i.cast_succ) =
    hs i (reverse_induction h0 hs i.succ) :=
begin
  rw [reverse_induction, dif_neg (ne_of_lt (fin.cast_succ_lt_last i))],
  cases i,
  refl
end

/-- Define `f : Π i : fin n.succ, C i` by separately handling the cases `i = fin.last n` and
`i = j.cast_succ`, `j : fin n`. -/
@[elab_as_eliminator, elab_strategy]
def last_cases {n : ℕ} {C : fin (n + 1) → Sort*}
  (hlast : C (fin.last n)) (hcast : (Π (i : fin n), C i.cast_succ)) (i : fin (n + 1)) : C i :=
reverse_induction hlast (λ i _, hcast i) i

@[simp] lemma last_cases_last {n : ℕ} {C : fin (n + 1) → Sort*}
  (hlast : C (fin.last n)) (hcast : (Π (i : fin n), C i.cast_succ)) :
  (fin.last_cases hlast hcast (fin.last n): C (fin.last n)) = hlast :=
reverse_induction_last _ _

@[simp] lemma last_cases_cast_succ {n : ℕ} {C : fin (n + 1) → Sort*}
  (hlast : C (fin.last n)) (hcast : (Π (i : fin n), C i.cast_succ)) (i : fin n) :
  (fin.last_cases hlast hcast (fin.cast_succ i): C (fin.cast_succ i)) = hcast i :=
reverse_induction_cast_succ _ _ _

/-- Define `f : Π i : fin (m + n), C i` by separately handling the cases `i = cast_add n i`,
`j : fin m` and `i = nat_add m j`, `j : fin n`. -/
@[elab_as_eliminator, elab_strategy]
def add_cases {m n : ℕ} {C : fin (m + n) → Sort u}
  (hleft : Π i, C (cast_add n i))
  (hright : Π i, C (nat_add m i)) (i : fin (m + n)) : C i :=
if hi : (i : ℕ) < m then eq.rec_on (cast_add_cast_lt n i hi) (hleft (cast_lt i hi))
else eq.rec_on (nat_add_sub_nat_cast (le_of_not_lt hi)) (hright _)

@[simp] lemma add_cases_left {m n : ℕ} {C : fin (m + n) → Sort*}
  (hleft : Π i, C (cast_add n i)) (hright : Π i, C (nat_add m i)) (i : fin m) :
  add_cases hleft hright (fin.cast_add n i) = hleft i :=
begin
  cases i with i hi,
  rw [add_cases, dif_pos (cast_add_lt _ _)],
  refl
end

@[simp] lemma add_cases_right {m n : ℕ} {C : fin (m + n) → Sort*}
  (hleft : Π i, C (cast_add n i)) (hright : Π i, C (nat_add m i)) (i : fin n) :
  add_cases hleft hright (nat_add m i) = hright i :=
begin
  have : ¬ (nat_add m i : ℕ) < m, from (le_coe_nat_add _ _).not_lt,
  rw [add_cases, dif_neg this],
  refine eq_of_heq ((eq_rec_heq _ _).trans _), congr' 1,
  simp
end

end rec

section add_group

open nat int

/-- Negation on `fin n` -/
instance (n : ℕ) : has_neg (fin n) :=
⟨λ a, ⟨(n - a) % n, nat.mod_lt _ (lt_of_le_of_lt (nat.zero_le _) a.2)⟩⟩

/-- Abelian group structure on `fin (n+1)`. -/
instance (n : ℕ) : add_comm_group (fin (n+1)) :=
{ add_left_neg := λ ⟨a, ha⟩, fin.ext $ trans (nat.mod_add_mod _ _ _) $
    by { rw [fin.coe_mk, fin.coe_zero, tsub_add_cancel_of_le, nat.mod_self], exact le_of_lt ha },
  sub_eq_add_neg := λ ⟨a, ha⟩ ⟨b, hb⟩, fin.ext $
    show (a + (n + 1 - b)) % (n + 1) = (a + (n + 1 - b) % (n + 1)) % (n + 1), by simp,
  sub := fin.sub,
  ..fin.add_comm_monoid n,
  ..fin.has_neg n.succ }

protected lemma coe_neg (a : fin n) : ((-a : fin n) : ℕ) = (n - a) % n := rfl

protected lemma coe_sub (a b : fin n) : ((a - b : fin n) : ℕ) = (a + (n - b)) % n :=
by cases a; cases b; refl

end add_group

section succ_above

lemma succ_above_aux (p : fin (n + 1)) :
  strict_mono (λ i : fin n, if i.cast_succ < p then i.cast_succ else i.succ) :=
(cast_succ : fin n ↪o _).strict_mono.ite (succ_embedding n).strict_mono
  (λ i j hij hj, lt_trans ((cast_succ : fin n ↪o _).lt_iff_lt.2 hij) hj)
  (λ i, (cast_succ_lt_succ i).le)

/-- `succ_above p i` embeds `fin n` into `fin (n + 1)` with a hole around `p`. -/
def succ_above (p : fin (n + 1)) : fin n ↪o fin (n + 1) :=
order_embedding.of_strict_mono _ p.succ_above_aux

/-- Embedding `i : fin n` into `fin (n + 1)` with a hole around `p : fin (n + 1)`
embeds `i` by `cast_succ` when the resulting `i.cast_succ < p`. -/
lemma succ_above_below (p : fin (n + 1)) (i : fin n) (h : i.cast_succ < p) :
  p.succ_above i = i.cast_succ :=
by { rw [succ_above], exact if_pos h }

@[simp] lemma succ_above_ne_zero_zero {a : fin (n + 2)} (ha : a ≠ 0) : a.succ_above 0 = 0 :=
begin
  rw fin.succ_above_below,
  { refl },
  { exact bot_lt_iff_ne_bot.mpr ha }
end

lemma succ_above_eq_zero_iff {a : fin (n + 2)} {b : fin (n + 1)} (ha : a ≠ 0) :
  a.succ_above b = 0 ↔ b = 0 :=
by simp only [←succ_above_ne_zero_zero ha, order_embedding.eq_iff_eq]

lemma succ_above_ne_zero {a : fin (n + 2)} {b : fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0) :
  a.succ_above b ≠ 0 :=
mt (succ_above_eq_zero_iff ha).mp hb

/-- Embedding `fin n` into `fin (n + 1)` with a hole around zero embeds by `succ`. -/
@[simp] lemma succ_above_zero : ⇑(succ_above (0 : fin (n + 1))) = fin.succ := rfl

/-- Embedding `fin n` into `fin (n + 1)` with a hole around `last n` embeds by `cast_succ`. -/
@[simp] lemma succ_above_last : succ_above (fin.last n) = cast_succ :=
by { ext, simp only [succ_above_below, cast_succ_lt_last] }

lemma succ_above_last_apply (i : fin n) : succ_above (fin.last n) i = i.cast_succ :=
by rw succ_above_last

/-- Embedding `i : fin n` into `fin (n + 1)` with a hole around `p : fin (n + 1)`
embeds `i` by `succ` when the resulting `p < i.succ`. -/
lemma succ_above_above (p : fin (n + 1)) (i : fin n) (h : p ≤ i.cast_succ) :
  p.succ_above i = i.succ :=
by simp [succ_above, h.not_lt]

/-- Embedding `i : fin n` into `fin (n + 1)` is always about some hole `p`. -/
lemma succ_above_lt_ge (p : fin (n + 1)) (i : fin n) : i.cast_succ < p ∨ p ≤ i.cast_succ :=
lt_or_ge (cast_succ i) p

/-- Embedding `i : fin n` into `fin (n + 1)` is always about some hole `p`. -/
lemma succ_above_lt_gt (p : fin (n + 1)) (i : fin n) : i.cast_succ < p ∨ p < i.succ :=
or.cases_on (succ_above_lt_ge p i)
  (λ h, or.inl h) (λ h, or.inr (lt_of_le_of_lt h (cast_succ_lt_succ i)))

/-- Embedding `i : fin n` into `fin (n + 1)` using a pivot `p` that is greater
results in a value that is less than `p`. -/
@[simp] lemma succ_above_lt_iff (p : fin (n + 1)) (i : fin n) :
  p.succ_above i < p ↔ i.cast_succ < p :=
begin
  refine iff.intro _ _,
  { intro h,
    cases succ_above_lt_ge p i with H H,
    { exact H },
    { rw succ_above_above _ _ H at h,
      exact lt_trans (cast_succ_lt_succ i) h } },
  { intro h,
    rw succ_above_below _ _ h,
    exact h }
end

/-- Embedding `i : fin n` into `fin (n + 1)` using a pivot `p` that is lesser
results in a value that is greater than `p`. -/
lemma lt_succ_above_iff (p : fin (n + 1)) (i : fin n) : p < p.succ_above i ↔ p ≤ i.cast_succ :=
begin
  refine iff.intro _ _,
  { intro h,
    cases succ_above_lt_ge p i with H H,
    { rw succ_above_below _ _ H at h,
      exact le_of_lt h },
    { exact H } },
  { intro h,
    rw succ_above_above _ _ h,
    exact lt_of_le_of_lt h (cast_succ_lt_succ i) },
end

/-- Embedding `i : fin n` into `fin (n + 1)` with a hole around `p : fin (n + 1)`
never results in `p` itself -/
theorem succ_above_ne (p : fin (n + 1)) (i : fin n) : p.succ_above i ≠ p :=
begin
  intro eq,
  by_cases H : i.cast_succ < p,
  { simpa [lt_irrefl, ←succ_above_below _ _ H, eq] using H },
  { simpa [←succ_above_above _ _ (le_of_not_lt H), eq] using cast_succ_lt_succ i }
end

/-- Embedding a positive `fin n` results in a positive fin (n + 1)` -/
lemma succ_above_pos (p : fin (n + 2)) (i : fin (n + 1)) (h : 0 < i) : 0 < p.succ_above i :=
begin
  by_cases H : i.cast_succ < p,
  { simpa [succ_above_below _ _ H] using cast_succ_pos h },
  { simpa [succ_above_above _ _ (le_of_not_lt H)] using succ_pos _ },
end

@[simp] lemma succ_above_cast_lt {x y : fin (n + 1)} (h : x < y)
  (hx : x.1 < n := lt_of_lt_of_le h y.le_last) :
  y.succ_above (x.cast_lt hx) = x :=
by { rw [succ_above_below, cast_succ_cast_lt], exact h }

@[simp] lemma succ_above_pred {x y : fin (n + 1)} (h : x < y)
  (hy : y ≠ 0 := (x.zero_le.trans_lt h).ne') :
  x.succ_above (y.pred hy) = y :=
by { rw [succ_above_above, succ_pred], simpa [le_iff_coe_le_coe] using nat.le_pred_of_lt h }

lemma cast_lt_succ_above {x : fin n} {y : fin (n + 1)} (h : cast_succ x < y)
  (h' : (y.succ_above x).1 < n := lt_of_lt_of_le ((succ_above_lt_iff _ _).2 h) (le_last y)) :
  (y.succ_above x).cast_lt h' = x :=
by simp only [succ_above_below _ _ h, cast_lt_cast_succ]

lemma pred_succ_above {x : fin n} {y : fin (n + 1)} (h : y ≤ cast_succ x)
  (h' : y.succ_above x ≠ 0 := (y.zero_le.trans_lt $ (lt_succ_above_iff _ _).2 h).ne') :
  (y.succ_above x).pred h' = x :=
by simp only [succ_above_above _ _ h, pred_succ]

lemma exists_succ_above_eq {x y : fin (n + 1)} (h : x ≠ y) : ∃ z, y.succ_above z = x :=
begin
  cases h.lt_or_lt with hlt hlt,
  exacts [⟨_, succ_above_cast_lt hlt⟩, ⟨_, succ_above_pred hlt⟩],
end

@[simp] lemma exists_succ_above_eq_iff {x y : fin (n + 1)} : (∃ z, x.succ_above z = y) ↔ y ≠ x :=
begin
  refine ⟨_, exists_succ_above_eq⟩,
  rintro ⟨y, rfl⟩,
  exact succ_above_ne _ _
end

/-- The range of `p.succ_above` is everything except `p`. -/
@[simp] lemma range_succ_above (p : fin (n + 1)) : set.range (p.succ_above) = {p}ᶜ :=
set.ext $ λ _, exists_succ_above_eq_iff

/-- Given a fixed pivot `x : fin (n + 1)`, `x.succ_above` is injective -/
lemma succ_above_right_injective {x : fin (n + 1)} : injective (succ_above x) :=
(succ_above x).injective

/-- Given a fixed pivot `x : fin (n + 1)`, `x.succ_above` is injective -/
lemma succ_above_right_inj {x : fin (n + 1)} :
  x.succ_above a = x.succ_above b ↔ a = b :=
succ_above_right_injective.eq_iff

/-- `succ_above` is injective at the pivot -/
lemma succ_above_left_injective : injective (@succ_above n) :=
λ _ _ h, by simpa [range_succ_above] using congr_arg (λ f : fin n ↪o fin (n + 1), (set.range f)ᶜ) h

/-- `succ_above` is injective at the pivot -/
@[simp] lemma succ_above_left_inj {x y : fin (n + 1)} :
  x.succ_above = y.succ_above ↔ x = y :=
succ_above_left_injective.eq_iff

@[simp] lemma zero_succ_above {n : ℕ} (i : fin n) :
  (0 : fin (n + 1)).succ_above i = i.succ :=
rfl

@[simp] lemma succ_succ_above_zero {n : ℕ} (i : fin (n + 1)) :
  (i.succ).succ_above 0 = 0 :=
succ_above_below _ _ (succ_pos _)

@[simp] lemma succ_succ_above_succ {n : ℕ} (i : fin (n + 1)) (j : fin n) :
  (i.succ).succ_above j.succ = (i.succ_above j).succ :=
(lt_or_ge j.cast_succ i).elim
  (λ h, have h' : j.succ.cast_succ < i.succ, by simpa [lt_iff_coe_lt_coe] using h,
        by { ext, simp [succ_above_below _ _ h, succ_above_below _ _ h'] })
  (λ h, have h' : i.succ ≤ j.succ.cast_succ, by simpa [le_iff_coe_le_coe] using h,
        by { ext, simp [succ_above_above _ _ h, succ_above_above _ _ h'] })

@[simp] lemma one_succ_above_zero {n : ℕ} :
  (1 : fin (n + 2)).succ_above 0 = 0 :=
succ_succ_above_zero 0

/-- By moving `succ` to the outside of this expression, we create opportunities for further
simplification using `succ_above_zero` or `succ_succ_above_zero`. -/
@[simp] lemma succ_succ_above_one {n : ℕ} (i : fin (n + 2)) :
  (i.succ).succ_above 1 = (i.succ_above 0).succ :=
succ_succ_above_succ i 0

@[simp] lemma one_succ_above_succ {n : ℕ} (j : fin n) :
  (1 : fin (n + 2)).succ_above j.succ = j.succ.succ :=
succ_succ_above_succ 0 j

@[simp] lemma one_succ_above_one {n : ℕ} :
  (1 : fin (n + 3)).succ_above 1 = 2 :=
succ_succ_above_succ 0 0

end succ_above

section pred_above

/-- `pred_above p i` embeds `i : fin (n+1)` into `fin n` by subtracting one if `p < i`. -/
def pred_above (p : fin n) (i : fin (n+1)) : fin n :=
if h : p.cast_succ < i then
  i.pred (ne_of_lt (lt_of_le_of_lt (zero_le p.cast_succ) h)).symm
else
  i.cast_lt (lt_of_le_of_lt (le_of_not_lt h) p.2)

lemma pred_above_right_monotone (p : fin n) : monotone p.pred_above :=
λ a b H,
begin
  dsimp [pred_above],
  split_ifs with ha hb hb,
  all_goals { simp only [le_iff_coe_le_coe, coe_pred], },
  { exact pred_le_pred H, },
  { calc _ ≤ _ : nat.pred_le _
        ... ≤ _ : H, },
  { simp at ha, exact le_pred_of_lt (lt_of_le_of_lt ha hb), },
  { exact H, },
end

lemma pred_above_left_monotone (i : fin (n + 1)) : monotone (λ p, pred_above p i) :=
λ a b H,
begin
  dsimp [pred_above],
  split_ifs with ha hb hb,
  all_goals { simp only [le_iff_coe_le_coe, coe_pred] },
  { exact pred_le _, },
  { have : b < a := cast_succ_lt_cast_succ_iff.mpr (hb.trans_le (le_of_not_gt ha)),
    exact absurd H this.not_le }
end

/-- `cast_pred` embeds `i : fin (n + 2)` into `fin (n + 1)`
by lowering just `last (n + 1)` to `last n`. -/
def cast_pred (i : fin (n + 2)) : fin (n + 1) :=
pred_above (last n) i

@[simp] lemma cast_pred_zero : cast_pred (0 : fin (n + 2)) = 0 := rfl

@[simp] lemma cast_pred_one : cast_pred (1 : fin (n + 2)) = 1 :=
by { cases n, apply subsingleton.elim, refl }

@[simp] theorem pred_above_zero {i : fin (n + 2)} (hi : i ≠ 0) :
  pred_above 0 i = i.pred hi :=
begin
  dsimp [pred_above],
  rw dif_pos,
  exact (pos_iff_ne_zero _).mpr hi,
end

@[simp] lemma cast_pred_last : cast_pred (last (n + 1)) = last n :=
by simp [eq_iff_veq, cast_pred, pred_above, cast_succ_lt_last]

@[simp] lemma cast_pred_mk (n i : ℕ) (h : i < n + 1) :
  cast_pred ⟨i, lt_succ_of_lt h⟩ = ⟨i, h⟩ :=
begin
  have : ¬cast_succ (last n) < ⟨i, lt_succ_of_lt h⟩,
  { simpa [lt_iff_coe_lt_coe] using le_of_lt_succ h },
  simp [cast_pred, pred_above, this]
end

lemma pred_above_below (p : fin (n + 1)) (i : fin (n + 2)) (h : i ≤ p.cast_succ) :
  p.pred_above i = i.cast_pred :=
begin
  have : i ≤ (last n).cast_succ := h.trans p.le_last,
  simp [pred_above, cast_pred, h.not_lt, this.not_lt]
end

@[simp] lemma pred_above_last : pred_above (fin.last n) = cast_pred := rfl

lemma pred_above_last_apply (i : fin n) : pred_above (fin.last n) i = i.cast_pred :=
by rw pred_above_last

lemma pred_above_above (p : fin n) (i : fin (n + 1)) (h : p.cast_succ < i) :
  p.pred_above i = i.pred (p.cast_succ.zero_le.trans_lt h).ne.symm :=
by simp [pred_above, h]

lemma cast_pred_monotone : monotone (@cast_pred n) :=
pred_above_right_monotone (last _)

/-- Sending `fin (n+1)` to `fin n` by subtracting one from anything above `p`
then back to `fin (n+1)` with a gap around `p` is the identity away from `p`. -/
@[simp] lemma succ_above_pred_above {p : fin n} {i : fin (n + 1)} (h : i ≠ p.cast_succ) :
  p.cast_succ.succ_above (p.pred_above i) = i :=
begin
  dsimp [pred_above, succ_above],
  rcases p with ⟨p, _⟩,
  rcases i with ⟨i, _⟩,
  cases lt_or_le i p with H H,
  { rw dif_neg, rw if_pos, refl, exact H, simp, apply le_of_lt H, },
  { rw dif_pos, rw if_neg,
    swap 3, -- For some reason `simp` doesn't fire fully unless we discharge the third goal.
    { exact lt_of_le_of_ne H (ne.symm h), },
    { simp, },
    { simp only [subtype.mk_eq_mk, ne.def, fin.cast_succ_mk] at h,
      simp only [pred, subtype.mk_lt_mk, not_lt],
      exact nat.le_pred_of_lt (nat.lt_of_le_and_ne H (ne.symm h)), }, },
end

/-- Sending `fin n` into `fin (n + 1)` with a gap at `p`
then back to `fin n` by subtracting one from anything above `p` is the identity. -/
@[simp] lemma pred_above_succ_above (p : fin n) (i : fin n) :
  p.pred_above (p.cast_succ.succ_above i) = i :=
begin
  dsimp [pred_above, succ_above],
  rcases p with ⟨p, _⟩,
  rcases i with ⟨i, _⟩,
  split_ifs,
  { rw dif_neg,
    { refl },
    { simp_rw [if_pos h],
      simp only [subtype.mk_lt_mk, not_lt],
      exact le_of_lt h, }, },
  { rw dif_pos,
    { refl, },
    { simp_rw [if_neg h],
      exact lt_succ_iff.mpr (not_lt.mp h), }, },
end

lemma cast_succ_pred_eq_pred_cast_succ  {a : fin (n + 1)} (ha : a ≠ 0)
  (ha' := a.cast_succ_ne_zero_iff.mpr ha) : (a.pred ha).cast_succ = a.cast_succ.pred ha' :=
by { cases a, refl }

/-- `pred` commutes with `succ_above`. -/
lemma pred_succ_above_pred {a : fin (n + 2)} {b : fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0)
  (hk := succ_above_ne_zero ha hb) :
  (a.pred ha).succ_above (b.pred hb) = (a.succ_above b).pred hk :=
begin
  obtain hbelow | habove := lt_or_le b.cast_succ a, -- `rwa` uses them
  { rw fin.succ_above_below,
    { rwa [cast_succ_pred_eq_pred_cast_succ , fin.pred_inj, fin.succ_above_below] },
    { rwa [cast_succ_pred_eq_pred_cast_succ , pred_lt_pred_iff] } },
  { rw fin.succ_above_above,
    have : (b.pred hb).succ = b.succ.pred (fin.succ_ne_zero _), by rw [succ_pred, pred_succ],
    { rwa [this, fin.pred_inj, fin.succ_above_above] },
    { rwa [cast_succ_pred_eq_pred_cast_succ , fin.pred_le_pred_iff] } }
end

@[simp] theorem cast_pred_cast_succ (i : fin (n + 1)) :
  cast_pred i.cast_succ = i :=
by simp [cast_pred, pred_above, le_last]

lemma cast_succ_cast_pred {i : fin (n + 2)} (h : i < last _) : cast_succ i.cast_pred = i :=
begin
  rw [cast_pred, pred_above, dif_neg],
  { simp [fin.eq_iff_veq] },
  { exact h.not_le }
end

lemma coe_cast_pred_le_self (i : fin (n + 2)) : (i.cast_pred : ℕ) ≤ i :=
begin
  rcases i.le_last.eq_or_lt with rfl|h,
  { simp },
  { rw [cast_pred, pred_above, dif_neg],
    { simp },
    { simpa [lt_iff_coe_lt_coe, le_iff_coe_le_coe, lt_succ_iff] using h } }
end

lemma coe_cast_pred_lt_iff {i : fin (n + 2)} : (i.cast_pred : ℕ) < i ↔ i = fin.last _ :=
begin
  rcases i.le_last.eq_or_lt with rfl|H,
  { simp },
  { simp only [ne_of_lt H],
    rw ←cast_succ_cast_pred H,
    simp }
end

lemma lt_last_iff_coe_cast_pred {i : fin (n + 2)} : i < fin.last _ ↔ (i.cast_pred : ℕ) = i :=
begin
  rcases i.le_last.eq_or_lt with rfl|H,
  { simp },
  { simp only [H],
    rw ←cast_succ_cast_pred H,
    simp }
end

end pred_above

/-- `min n m` as an element of `fin (m + 1)` -/
def clamp (n m : ℕ) : fin (m + 1) := of_nat $ min n m

@[simp] lemma coe_clamp (n m : ℕ) : (clamp n m : ℕ) = min n m :=
nat.mod_eq_of_lt $ nat.lt_succ_iff.mpr $ min_le_right _ _

@[simp]
lemma coe_of_nat_eq_mod (m n : ℕ) :
  ((n : fin (succ m)) : ℕ) = n % succ m :=
by rw [← of_nat_eq_coe]; refl

@[simp] lemma coe_of_nat_eq_mod' (m n : ℕ) [I : fact (0 < m)] :
  (@fin.of_nat' _ I n : ℕ) = n % m :=
rfl

section mul

/-!
### mul
-/

lemma val_mul {n : ℕ} :  ∀ a b : fin n, (a * b).val = (a.val * b.val) % n
| ⟨_, _⟩ ⟨_, _⟩ := rfl

lemma coe_mul {n : ℕ} :  ∀ a b : fin n, ((a * b : fin n) : ℕ) = (a * b) % n
| ⟨_, _⟩ ⟨_, _⟩ := rfl

@[simp] protected lemma mul_one (k : fin (n + 1)) : k * 1 = k :=
by { cases n, simp, simp [eq_iff_veq, mul_def, mod_eq_of_lt (is_lt k)] }

@[simp] protected lemma one_mul (k : fin (n + 1)) : (1 : fin (n + 1)) * k = k :=
by { cases n, simp, simp [eq_iff_veq, mul_def, mod_eq_of_lt (is_lt k)] }

@[simp] protected lemma mul_zero (k : fin (n + 1)) : k * 0 = 0 :=
by simp [eq_iff_veq, mul_def]

@[simp] protected lemma zero_mul (k : fin (n + 1)) : (0 : fin (n + 1)) * k = 0 :=
by simp [eq_iff_veq, mul_def]

end mul

end fin
