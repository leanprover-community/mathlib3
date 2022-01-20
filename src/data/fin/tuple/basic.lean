/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov, Sébastien Gouëzel, Chris Hughes
-/
import data.fin.basic
/-!
# Operation on tuples

We interpret maps `Π i : fin n, α i` as `n`-tuples of elements of possibly varying type `α i`,
`(α 0, …, α (n-1))`. A particular case is `fin n → α` of elements with all the same type.
In this case when `α i` is a constant map, then tuples are isomorphic (but not definitionally equal)
to `vector`s.

We define the following operations:

* `fin.tail` : the tail of an `n+1` tuple, i.e., its last `n` entries;
* `fin.cons` : adding an element at the beginning of an `n`-tuple, to get an `n+1`-tuple;
* `fin.init` : the beginning of an `n+1` tuple, i.e., its first `n` entries;
* `fin.snoc` : adding an element at the end of an `n`-tuple, to get an `n+1`-tuple. The name `snoc`
  comes from `cons` (i.e., adding an element to the left of a tuple) read in reverse order.
* `fin.insert_nth` : insert an element to a tuple at a given position.
* `fin.find p` : returns the first index `n` where `p n` is satisfied, and `none` if it is never
  satisfied.

-/
universes u v

namespace fin

variables {m n : ℕ}
open function

section tuple

/-- There is exactly one tuple of size zero. -/
example (α : fin 0 → Sort u) : unique (Π i : fin 0, α i) :=
by apply_instance

@[simp] lemma tuple0_le {α : Π i : fin 0, Type*} [Π i, preorder (α i)] (f g : Π i, α i) : f ≤ g :=
fin_zero_elim

variables {α : fin (n+1) → Type u} (x : α 0) (q : Πi, α i) (p : Π(i : fin n), α (i.succ))
  (i : fin n) (y : α i.succ) (z : α 0)

/-- The tail of an `n+1` tuple, i.e., its last `n` entries. -/
def tail (q : Πi, α i) : (Π(i : fin n), α (i.succ)) := λ i, q i.succ

lemma tail_def {n : ℕ} {α : fin (n+1) → Type*} {q : Π i, α i} :
  tail (λ k : fin (n+1), q k) = (λ k : fin n, q k.succ) := rfl

/-- Adding an element at the beginning of an `n`-tuple, to get an `n+1`-tuple. -/
def cons (x : α 0) (p : Π(i : fin n), α (i.succ)) : Πi, α i :=
λ j, fin.cases x p j

@[simp] lemma tail_cons : tail (cons x p) = p :=
by simp [tail, cons]

@[simp] lemma cons_succ : cons x p i.succ = p i :=
by simp [cons]

@[simp] lemma cons_zero : cons x p 0 = x :=
by simp [cons]

/-- Updating a tuple and adding an element at the beginning commute. -/
@[simp] lemma cons_update : cons x (update p i y) = update (cons x p) i.succ y :=
begin
  ext j,
  by_cases h : j = 0,
  { rw h, simp [ne.symm (succ_ne_zero i)] },
  { let j' := pred j h,
    have : j'.succ = j := succ_pred j h,
    rw [← this, cons_succ],
    by_cases h' : j' = i,
    { rw h', simp },
    { have : j'.succ ≠ i.succ, by rwa [ne.def, succ_inj],
      rw [update_noteq h', update_noteq this, cons_succ] } }
end

/-- Adding an element at the beginning of a tuple and then updating it amounts to adding it
directly. -/
lemma update_cons_zero : update (cons x p) 0 z = cons z p :=
begin
  ext j,
  by_cases h : j = 0,
  { rw h, simp },
  { simp only [h, update_noteq, ne.def, not_false_iff],
    let j' := pred j h,
    have : j'.succ = j := succ_pred j h,
    rw [← this, cons_succ, cons_succ] }
end

/-- Concatenating the first element of a tuple with its tail gives back the original tuple -/
@[simp] lemma cons_self_tail : cons (q 0) (tail q) = q :=
begin
  ext j,
  by_cases h : j = 0,
  { rw h, simp },
  { let j' := pred j h,
    have : j'.succ = j := succ_pred j h,
    rw [← this, tail, cons_succ] }
end

/-- Updating the first element of a tuple does not change the tail. -/
@[simp] lemma tail_update_zero : tail (update q 0 z) = tail q :=
by { ext j, simp [tail, fin.succ_ne_zero] }

/-- Updating a nonzero element and taking the tail commute. -/
@[simp] lemma tail_update_succ :
  tail (update q i.succ y) = update (tail q) i y :=
begin
  ext j,
  by_cases h : j = i,
  { rw h, simp [tail] },
  { simp [tail, (fin.succ_injective n).ne h, h] }
end

lemma comp_cons {α : Type*} {β : Type*} (g : α → β) (y : α) (q : fin n → α) :
  g ∘ (cons y q) = cons (g y) (g ∘ q) :=
begin
  ext j,
  by_cases h : j = 0,
  { rw h, refl },
  { let j' := pred j h,
    have : j'.succ = j := succ_pred j h,
    rw [← this, cons_succ, comp_app, cons_succ] }
end

lemma comp_tail {α : Type*} {β : Type*} (g : α → β) (q : fin n.succ → α) :
  g ∘ (tail q) = tail (g ∘ q) :=
by { ext j, simp [tail] }

lemma le_cons [Π i, preorder (α i)] {x : α 0} {q : Π i, α i} {p : Π i : fin n, α i.succ} :
  q ≤ cons x p ↔ q 0 ≤ x ∧ tail q ≤ p :=
forall_fin_succ.trans $ and_congr iff.rfl $ forall_congr $ λ j, by simp [tail]

lemma cons_le [Π i, preorder (α i)] {x : α 0} {q : Π i, α i} {p : Π i : fin n, α i.succ} :
  cons x p ≤ q ↔ x ≤ q 0 ∧ p ≤ tail q :=
@le_cons  _ (λ i, order_dual (α i)) _ x q p

@[simp]
lemma range_cons {α : Type*} {n : ℕ} (x : α) (b : fin n → α) :
  set.range (fin.cons x b : fin n.succ → α) = insert x (set.range b) :=
begin
  ext y,
  simp only [set.mem_range, set.mem_insert_iff],
  split,
  { rintros ⟨i, rfl⟩,
    refine cases (or.inl (cons_zero _ _)) (λ i, or.inr ⟨i, _⟩) i,
    rw cons_succ },
  { rintros (rfl | ⟨i, hi⟩),
    { exact ⟨0, fin.cons_zero _ _⟩ },
    { refine ⟨i.succ, _⟩,
      rw [cons_succ, hi] } }
end

/-- `fin.append ho u v` appends two vectors of lengths `m` and `n` to produce
one of length `o = m + n`.  `ho` provides control of definitional equality
for the vector length. -/
def append {α : Type*} {o : ℕ} (ho : o = m + n) (u : fin m → α) (v : fin n → α) : fin o → α :=
λ i, if h : (i : ℕ) < m
  then u ⟨i, h⟩
  else v ⟨(i : ℕ) - m, (tsub_lt_iff_left (le_of_not_lt h)).2 (ho ▸ i.property)⟩

@[simp] lemma fin_append_apply_zero {α : Type*} {o : ℕ} (ho : (o + 1) = (m + 1) + n)
  (u : fin (m + 1) → α) (v : fin n → α) :
  fin.append ho u v 0 = u 0 := rfl

end tuple

section tuple_right
/-! In the previous section, we have discussed inserting or removing elements on the left of a
tuple. In this section, we do the same on the right. A difference is that `fin (n+1)` is constructed
inductively from `fin n` starting from the left, not from the right. This implies that Lean needs
more help to realize that elements belong to the right types, i.e., we need to insert casts at
several places. -/

variables {α : fin (n+1) → Type u} (x : α (last n)) (q : Πi, α i) (p : Π(i : fin n), α i.cast_succ)
(i : fin n) (y : α i.cast_succ) (z : α (last n))

/-- The beginning of an `n+1` tuple, i.e., its first `n` entries -/
def init (q : Πi, α i) (i : fin n) : α i.cast_succ :=
q i.cast_succ

lemma init_def {n : ℕ} {α : fin (n+1) → Type*} {q : Π i, α i} :
  init (λ k : fin (n+1), q k) = (λ k : fin n, q k.cast_succ) := rfl

/-- Adding an element at the end of an `n`-tuple, to get an `n+1`-tuple. The name `snoc` comes from
`cons` (i.e., adding an element to the left of a tuple) read in reverse order. -/
def snoc (p : Π(i : fin n), α i.cast_succ) (x : α (last n)) (i : fin (n+1)) : α i :=
if h : i.val < n
then _root_.cast (by rw fin.cast_succ_cast_lt i h) (p (cast_lt i h))
else _root_.cast (by rw eq_last_of_not_lt h) x

@[simp] lemma init_snoc : init (snoc p x) = p :=
begin
  ext i,
  have h' := fin.cast_lt_cast_succ i i.is_lt,
  simp [init, snoc, i.is_lt, h'],
  convert cast_eq rfl (p i)
end

@[simp] lemma snoc_cast_succ : snoc p x i.cast_succ = p i :=
begin
  have : i.cast_succ.val < n := i.is_lt,
  have h' := fin.cast_lt_cast_succ i i.is_lt,
  simp [snoc, this, h'],
  convert cast_eq rfl (p i)
end

@[simp] lemma snoc_last : snoc p x (last n) = x :=
by { simp [snoc] }

/-- Updating a tuple and adding an element at the end commute. -/
@[simp] lemma snoc_update : snoc (update p i y) x = update (snoc p x) i.cast_succ y :=
begin
  ext j,
  by_cases h : j.val < n,
  { simp only [snoc, h, dif_pos],
    by_cases h' : j = cast_succ i,
    { have C1 : α i.cast_succ = α j, by rw h',
      have E1 : update (snoc p x) i.cast_succ y j = _root_.cast C1 y,
      { have : update (snoc p x) j (_root_.cast C1 y) j = _root_.cast C1 y, by simp,
        convert this,
        { exact h'.symm },
        { exact heq_of_cast_eq (congr_arg α (eq.symm h')) rfl } },
      have C2 : α i.cast_succ = α (cast_succ (cast_lt j h)),
        by rw [cast_succ_cast_lt, h'],
      have E2 : update p i y (cast_lt j h) = _root_.cast C2 y,
      { have : update p (cast_lt j h) (_root_.cast C2 y) (cast_lt j h) = _root_.cast C2 y,
          by simp,
        convert this,
        { simp [h, h'] },
        { exact heq_of_cast_eq C2 rfl } },
      rw [E1, E2],
      exact eq_rec_compose _ _ _ },
    { have : ¬(cast_lt j h = i),
        by { assume E, apply h', rw [← E, cast_succ_cast_lt] },
      simp [h', this, snoc, h] } },
  { rw eq_last_of_not_lt h,
    simp [ne.symm (ne_of_lt (cast_succ_lt_last i))] }
end

/-- Adding an element at the beginning of a tuple and then updating it amounts to adding it
directly. -/
lemma update_snoc_last : update (snoc p x) (last n) z = snoc p z :=
begin
  ext j,
  by_cases h : j.val < n,
  { have : j ≠ last n := ne_of_lt h,
    simp [h, update_noteq, this, snoc] },
  { rw eq_last_of_not_lt h,
    simp }
end

/-- Concatenating the first element of a tuple with its tail gives back the original tuple -/
@[simp] lemma snoc_init_self : snoc (init q) (q (last n)) = q :=
begin
  ext j,
  by_cases h : j.val < n,
  { have : j ≠ last n := ne_of_lt h,
    simp [h, update_noteq, this, snoc, init, cast_succ_cast_lt],
    have A : cast_succ (cast_lt j h) = j := cast_succ_cast_lt _ _,
    rw ← cast_eq rfl (q j),
    congr' 1; rw A },
  { rw eq_last_of_not_lt h,
    simp }
end

/-- Updating the last element of a tuple does not change the beginning. -/
@[simp] lemma init_update_last : init (update q (last n) z) = init q :=
by { ext j, simp [init, ne_of_lt, cast_succ_lt_last] }

/-- Updating an element and taking the beginning commute. -/
@[simp] lemma init_update_cast_succ :
  init (update q i.cast_succ y) = update (init q) i y :=
begin
  ext j,
  by_cases h : j = i,
  { rw h, simp [init] },
  { simp [init, h] }
end

/-- `tail` and `init` commute. We state this lemma in a non-dependent setting, as otherwise it
would involve a cast to convince Lean that the two types are equal, making it harder to use. -/
lemma tail_init_eq_init_tail {β : Type*} (q : fin (n+2) → β) :
  tail (init q) = init (tail q) :=
by { ext i, simp [tail, init, cast_succ_fin_succ] }

/-- `cons` and `snoc` commute. We state this lemma in a non-dependent setting, as otherwise it
would involve a cast to convince Lean that the two types are equal, making it harder to use. -/
lemma cons_snoc_eq_snoc_cons {β : Type*} (a : β) (q : fin n → β) (b : β) :
  @cons n.succ (λ i, β) a (snoc q b) = snoc (cons a q) b :=
begin
  ext i,
  by_cases h : i = 0,
  { rw h, refl },
  set j := pred i h with ji,
  have : i = j.succ, by rw [ji, succ_pred],
  rw [this, cons_succ],
  by_cases h' : j.val < n,
  { set k := cast_lt j h' with jk,
    have : j = k.cast_succ, by rw [jk, cast_succ_cast_lt],
    rw [this, ← cast_succ_fin_succ],
    simp },
  rw [eq_last_of_not_lt h', succ_last],
  simp
end


lemma comp_snoc {α : Type*} {β : Type*} (g : α → β) (q : fin n → α) (y : α) :
  g ∘ (snoc q y) = snoc (g ∘ q) (g y) :=
begin
  ext j,
  by_cases h : j.val < n,
  { have : j ≠ last n := ne_of_lt h,
    simp [h, this, snoc, cast_succ_cast_lt] },
  { rw eq_last_of_not_lt h,
    simp }
end

lemma comp_init {α : Type*} {β : Type*} (g : α → β) (q : fin n.succ → α) :
  g ∘ (init q) = init (g ∘ q) :=
by { ext j, simp [init] }

end tuple_right

section insert_nth

variables {α : fin (n+1) → Type u} {β : Type v}

/-- Define a function on `fin (n + 1)` from a value on `i : fin (n + 1)` and values on each
`fin.succ_above i j`, `j : fin n`. This version is elaborated as eliminator and works for
propositions, see also `fin.insert_nth` for a version without an `@[elab_as_eliminator]`
attribute. -/
@[elab_as_eliminator]
def succ_above_cases {α : fin (n + 1) → Sort u} (i : fin (n + 1)) (x : α i)
  (p : Π j : fin n, α (i.succ_above j)) (j : fin (n + 1)) : α j :=
if hj : j = i then eq.rec x hj.symm
else if hlt : j < i then eq.rec_on (succ_above_cast_lt hlt) (p _)
else eq.rec_on (succ_above_pred $ (ne.lt_or_lt hj).resolve_left hlt) (p _)

lemma forall_iff_succ_above {p : fin (n + 1) → Prop} (i : fin (n + 1)) :
  (∀ j, p j) ↔ p i ∧ ∀ j, p (i.succ_above j) :=
⟨λ h, ⟨h _, λ j, h _⟩, λ h, succ_above_cases i h.1 h.2⟩

/-- Insert an element into a tuple at a given position. For `i = 0` see `fin.cons`,
for `i = fin.last n` see `fin.snoc`. See also `fin.succ_above_cases` for a version elaborated
as an eliminator. -/
def insert_nth (i : fin (n + 1)) (x : α i) (p : Π j : fin n, α (i.succ_above j)) (j : fin (n + 1)) :
  α j :=
succ_above_cases i x p j

@[simp] lemma insert_nth_apply_same (i : fin (n + 1)) (x : α i) (p : Π j, α (i.succ_above j)) :
  insert_nth i x p i = x :=
by simp [insert_nth, succ_above_cases]

@[simp] lemma insert_nth_apply_succ_above (i : fin (n + 1)) (x : α i) (p : Π j, α (i.succ_above j))
  (j : fin n) :
  insert_nth i x p (i.succ_above j) = p j :=
begin
  simp only [insert_nth, succ_above_cases, dif_neg (succ_above_ne _ _)],
  by_cases hlt : j.cast_succ < i,
  { rw [dif_pos ((succ_above_lt_iff _ _).2 hlt)],
    apply eq_of_heq ((eq_rec_heq _ _).trans _),
    rw [cast_lt_succ_above hlt] },
  { rw [dif_neg (mt (succ_above_lt_iff _ _).1 hlt)],
    apply eq_of_heq ((eq_rec_heq _ _).trans _),
    rw [pred_succ_above (le_of_not_lt hlt)] }
end

@[simp] lemma succ_above_cases_eq_insert_nth :
  @succ_above_cases.{u + 1} = @insert_nth.{u} := rfl

@[simp] lemma insert_nth_comp_succ_above (i : fin (n + 1)) (x : β) (p : fin n → β) :
  insert_nth i x p ∘ i.succ_above = p :=
funext $ insert_nth_apply_succ_above i x p

lemma insert_nth_eq_iff {i : fin (n + 1)} {x : α i} {p : Π j, α (i.succ_above j)} {q : Π j, α j} :
  i.insert_nth x p = q ↔ q i = x ∧ p = (λ j, q (i.succ_above j)) :=
by simp [funext_iff, forall_iff_succ_above i, eq_comm]

lemma eq_insert_nth_iff {i : fin (n + 1)} {x : α i} {p : Π j, α (i.succ_above j)} {q : Π j, α j} :
  q = i.insert_nth x p ↔ q i = x ∧ p = (λ j, q (i.succ_above j)) :=
eq_comm.trans insert_nth_eq_iff

lemma insert_nth_apply_below {i j : fin (n + 1)} (h : j < i) (x : α i)
  (p : Π k, α (i.succ_above k)) :
  i.insert_nth x p j = eq.rec_on (succ_above_cast_lt h) (p $ j.cast_lt _) :=
by rw [insert_nth, succ_above_cases, dif_neg h.ne, dif_pos h]

lemma insert_nth_apply_above {i j : fin (n + 1)} (h : i < j) (x : α i)
  (p : Π k, α (i.succ_above k)) :
  i.insert_nth x p j = eq.rec_on (succ_above_pred h) (p $ j.pred _) :=
by rw [insert_nth, succ_above_cases, dif_neg h.ne', dif_neg h.not_lt]

lemma insert_nth_zero (x : α 0) (p : Π j : fin n, α (succ_above 0 j)) :
  insert_nth 0 x p = cons x (λ j, _root_.cast (congr_arg α (congr_fun succ_above_zero j)) (p j)) :=
begin
  refine insert_nth_eq_iff.2 ⟨by simp, _⟩,
  ext j,
  convert (cons_succ _ _ _).symm
end

@[simp] lemma insert_nth_zero' (x : β) (p : fin n → β) :
  @insert_nth _ (λ _, β) 0 x p = cons x p :=
by simp [insert_nth_zero]

lemma insert_nth_last (x : α (last n)) (p : Π j : fin n, α ((last n).succ_above j)) :
  insert_nth (last n) x p =
    snoc (λ j, _root_.cast (congr_arg α (succ_above_last_apply j)) (p j)) x :=
begin
  refine insert_nth_eq_iff.2 ⟨by simp, _⟩,
  ext j,
  apply eq_of_heq,
  transitivity snoc (λ j, _root_.cast (congr_arg α (succ_above_last_apply j)) (p j)) x j.cast_succ,
  { rw [snoc_cast_succ], exact (cast_heq _ _).symm },
  { apply congr_arg_heq,
    rw [succ_above_last] }
end

@[simp] lemma insert_nth_last' (x : β) (p : fin n → β) :
  @insert_nth _ (λ _, β) (last n) x p = snoc p x :=
by simp [insert_nth_last]

@[simp] lemma insert_nth_zero_right [Π j, has_zero (α j)] (i : fin (n + 1)) (x : α i) :
  i.insert_nth x 0 = pi.single i x :=
insert_nth_eq_iff.2 $ by simp [succ_above_ne, pi.zero_def]

lemma insert_nth_binop (op : Π j, α j → α j → α j) (i : fin (n + 1))
  (x y : α i) (p q : Π j, α (i.succ_above j)) :
  i.insert_nth (op i x y) (λ j, op _ (p j) (q j)) =
    λ j, op j (i.insert_nth x p j) (i.insert_nth y q j) :=
insert_nth_eq_iff.2 $ by simp

@[simp] lemma insert_nth_mul [Π j, has_mul (α j)] (i : fin (n + 1))
  (x y : α i) (p q : Π j, α (i.succ_above j)) :
  i.insert_nth (x * y) (p * q) = i.insert_nth x p * i.insert_nth y q :=
insert_nth_binop (λ _, (*)) i x y p q

@[simp] lemma insert_nth_add [Π j, has_add (α j)] (i : fin (n + 1))
  (x y : α i) (p q : Π j, α (i.succ_above j)) :
  i.insert_nth (x + y) (p + q) = i.insert_nth x p + i.insert_nth y q :=
insert_nth_binop (λ _, (+)) i x y p q

@[simp] lemma insert_nth_div [Π j, has_div (α j)] (i : fin (n + 1))
  (x y : α i) (p q : Π j, α (i.succ_above j)) :
  i.insert_nth (x / y) (p / q) = i.insert_nth x p / i.insert_nth y q :=
insert_nth_binop (λ _, (/)) i x y p q

@[simp] lemma insert_nth_sub [Π j, has_sub (α j)] (i : fin (n + 1))
  (x y : α i) (p q : Π j, α (i.succ_above j)) :
  i.insert_nth (x - y) (p - q) = i.insert_nth x p - i.insert_nth y q :=
insert_nth_binop (λ _, has_sub.sub) i x y p q

@[simp] lemma insert_nth_sub_same [Π j, add_group (α j)] (i : fin (n + 1))
  (x y : α i) (p : Π j, α (i.succ_above j)) :
  i.insert_nth x p - i.insert_nth y p = pi.single i (x - y) :=
by simp_rw [← insert_nth_sub, ← insert_nth_zero_right, pi.sub_def, sub_self, pi.zero_def]

variables [Π i, preorder (α i)]

lemma insert_nth_le_iff {i : fin (n + 1)} {x : α i} {p : Π j, α (i.succ_above j)} {q : Π j, α j} :
  i.insert_nth x p ≤ q ↔ x ≤ q i ∧ p ≤ (λ j, q (i.succ_above j)) :=
by simp [pi.le_def, forall_iff_succ_above i]

lemma le_insert_nth_iff {i : fin (n + 1)} {x : α i} {p : Π j, α (i.succ_above j)} {q : Π j, α j} :
  q ≤ i.insert_nth x p ↔ q i ≤ x ∧ (λ j, q (i.succ_above j)) ≤ p :=
by simp [pi.le_def, forall_iff_succ_above i]

open set

lemma insert_nth_mem_Icc {i : fin (n + 1)} {x : α i} {p : Π j, α (i.succ_above j)}
  {q₁ q₂ : Π j, α j} :
  i.insert_nth x p ∈ Icc q₁ q₂ ↔
    x ∈ Icc (q₁ i) (q₂ i) ∧ p ∈ Icc (λ j, q₁ (i.succ_above j)) (λ j, q₂ (i.succ_above j)) :=
by simp only [mem_Icc, insert_nth_le_iff, le_insert_nth_iff, and.assoc, and.left_comm]

lemma preimage_insert_nth_Icc_of_mem {i : fin (n + 1)} {x : α i} {q₁ q₂ : Π j, α j}
  (hx : x ∈ Icc (q₁ i) (q₂ i)) :
  i.insert_nth x ⁻¹' (Icc q₁ q₂) = Icc (λ j, q₁ (i.succ_above j)) (λ j, q₂ (i.succ_above j)) :=
set.ext $ λ p, by simp only [mem_preimage, insert_nth_mem_Icc, hx, true_and]

lemma preimage_insert_nth_Icc_of_not_mem {i : fin (n + 1)} {x : α i} {q₁ q₂ : Π j, α j}
  (hx : x ∉ Icc (q₁ i) (q₂ i)) :
  i.insert_nth x ⁻¹' (Icc q₁ q₂) = ∅ :=
set.ext $ λ p, by simp only [mem_preimage, insert_nth_mem_Icc, hx, false_and, mem_empty_eq]

end insert_nth

section find

/-- `find p` returns the first index `n` where `p n` is satisfied, and `none` if it is never
satisfied. -/
def find : Π {n : ℕ} (p : fin n → Prop) [decidable_pred p], option (fin n)
| 0     p _ := none
| (n+1) p _ := by resetI; exact option.cases_on
  (@find n (λ i, p (i.cast_lt (nat.lt_succ_of_lt i.2))) _)
  (if h : p (fin.last n) then some (fin.last n) else none)
  (λ i, some (i.cast_lt (nat.lt_succ_of_lt i.2)))

/-- If `find p = some i`, then `p i` holds -/
lemma find_spec : Π {n : ℕ} (p : fin n → Prop) [decidable_pred p] {i : fin n}
  (hi : i ∈ by exactI fin.find p), p i
| 0     p I i hi := option.no_confusion hi
| (n+1) p I i hi := begin
  dsimp [find] at hi,
  resetI,
  cases h : find (λ i : fin n, (p (i.cast_lt (nat.lt_succ_of_lt i.2)))) with j,
  { rw h at hi,
    dsimp at hi,
    split_ifs at hi with hl hl,
    { exact option.some_inj.1 hi ▸ hl },
    { exact option.no_confusion hi } },
  { rw h at hi,
    rw [← option.some_inj.1 hi],
    exact find_spec _ h }
end

/-- `find p` does not return `none` if and only if `p i` holds at some index `i`. -/
lemma is_some_find_iff : Π {n : ℕ} {p : fin n → Prop} [decidable_pred p],
  by exactI (find p).is_some ↔ ∃ i, p i
| 0     p _ := iff_of_false (λ h, bool.no_confusion h) (λ ⟨i, _⟩, fin_zero_elim i)
| (n+1) p _ := ⟨λ h, begin
  rw [option.is_some_iff_exists] at h,
  cases h with i hi,
  exactI ⟨i, find_spec _ hi⟩
end, λ ⟨⟨i, hin⟩, hi⟩,
begin
  resetI,
  dsimp [find],
  cases h : find (λ i : fin n, (p (i.cast_lt (nat.lt_succ_of_lt i.2)))) with j,
  { split_ifs with hl hl,
    { exact option.is_some_some },
    { have := (@is_some_find_iff n (λ x, p (x.cast_lt (nat.lt_succ_of_lt x.2))) _).2
        ⟨⟨i, lt_of_le_of_ne (nat.le_of_lt_succ hin)
        (λ h, by clear_aux_decl; cases h; exact hl hi)⟩, hi⟩,
      rw h at this,
      exact this } },
  { simp }
end⟩

/-- `find p` returns `none` if and only if `p i` never holds. -/
lemma find_eq_none_iff {n : ℕ} {p : fin n → Prop} [decidable_pred p] :
  find p = none ↔ ∀ i, ¬ p i :=
by rw [← not_exists, ← is_some_find_iff]; cases (find p); simp

/-- If `find p` returns `some i`, then `p j` does not hold for `j < i`, i.e., `i` is minimal among
the indices where `p` holds. -/
lemma find_min : Π {n : ℕ} {p : fin n → Prop} [decidable_pred p] {i : fin n}
  (hi : i ∈ by exactI fin.find p) {j : fin n} (hj : j < i), ¬ p j
| 0     p _ i hi j hj hpj := option.no_confusion hi
| (n+1) p _ i hi ⟨j, hjn⟩ hj hpj := begin
  resetI,
  dsimp [find] at hi,
  cases h : find (λ i : fin n, (p (i.cast_lt (nat.lt_succ_of_lt i.2)))) with k,
  { rw [h] at hi,
    split_ifs at hi with hl hl,
    { have := option.some_inj.1 hi,
      subst this,
      rw [find_eq_none_iff] at h,
      exact h ⟨j, hj⟩ hpj },
    { exact option.no_confusion hi } },
  { rw h at hi,
    dsimp at hi,
    have := option.some_inj.1 hi,
    subst this,
    exact find_min h (show (⟨j, lt_trans hj k.2⟩ : fin n) < k, from hj) hpj }
end

lemma find_min' {p : fin n → Prop} [decidable_pred p] {i : fin n}
  (h : i ∈ fin.find p) {j : fin n} (hj : p j) : i ≤ j :=
le_of_not_gt (λ hij, find_min h hij hj)

lemma nat_find_mem_find {p : fin n → Prop} [decidable_pred p]
  (h : ∃ i, ∃ hin : i < n, p ⟨i, hin⟩) :
  (⟨nat.find h, (nat.find_spec h).fst⟩ : fin n) ∈ find p :=
let ⟨i, hin, hi⟩ := h in
begin
  cases hf : find p with f,
  { rw [find_eq_none_iff] at hf,
    exact (hf ⟨i, hin⟩ hi).elim },
  { refine option.some_inj.2 (le_antisymm _ _),
    { exact find_min' hf (nat.find_spec h).snd },
    { exact nat.find_min' _ ⟨f.2, by convert find_spec p hf;
        exact fin.eta _ _⟩ } }
end

lemma mem_find_iff {p : fin n → Prop} [decidable_pred p] {i : fin n} :
  i ∈ fin.find p ↔ p i ∧ ∀ j, p j → i ≤ j :=
⟨λ hi, ⟨find_spec _ hi, λ _, find_min' hi⟩,
  begin
    rintros ⟨hpi, hj⟩,
    cases hfp : fin.find p,
    { rw [find_eq_none_iff] at hfp,
      exact (hfp _ hpi).elim },
    { exact option.some_inj.2 (le_antisymm (find_min' hfp hpi) (hj _ (find_spec _ hfp))) }
  end⟩

lemma find_eq_some_iff {p : fin n → Prop} [decidable_pred p] {i : fin n} :
  fin.find p = some i ↔ p i ∧ ∀ j, p j → i ≤ j :=
 mem_find_iff

lemma mem_find_of_unique {p : fin n → Prop} [decidable_pred p]
  (h : ∀ i j, p i → p j → i = j) {i : fin n} (hi : p i) : i ∈ fin.find p :=
mem_find_iff.2 ⟨hi, λ j hj, le_of_eq $ h i j hi hj⟩

end find

end fin
