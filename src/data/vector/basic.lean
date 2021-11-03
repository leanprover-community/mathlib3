/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.vector
import data.list.nodup
import data.list.of_fn
import control.applicative
/-!
# Additional theorems and definitions about the `vector` type

This file introduces the infix notation `::ᵥ` for `vector.cons`.
-/
universes u
variables {n : ℕ}

namespace vector
variables {α : Type*}

infixr `::ᵥ`:67  := vector.cons

attribute [simp] head_cons tail_cons

instance [inhabited α] : inhabited (vector α n) :=
⟨of_fn (λ _, default α)⟩

theorem to_list_injective : function.injective (@to_list α n) :=
subtype.val_injective

/-- Two `v w : vector α n` are equal iff they are equal at every single index. -/
@[ext] theorem ext : ∀ {v w : vector α n}
  (h : ∀ m : fin n, vector.nth v m = vector.nth w m), v = w
| ⟨v, hv⟩ ⟨w, hw⟩ h := subtype.eq (list.ext_le (by rw [hv, hw])
  (λ m hm hn, h ⟨m, hv ▸ hm⟩))

/-- The empty `vector` is a `subsingleton`. -/
instance zero_subsingleton : subsingleton (vector α 0) :=
⟨λ _ _, vector.ext (λ m, fin.elim0 m)⟩

@[simp] theorem cons_val (a : α) : ∀ (v : vector α n), (a ::ᵥ v).val = a :: v.val
| ⟨_, _⟩ := rfl

@[simp] theorem cons_head (a : α) : ∀ (v : vector α n), (a ::ᵥ v).head = a
| ⟨_, _⟩ := rfl

@[simp] theorem cons_tail (a : α) : ∀ (v : vector α n), (a ::ᵥ v).tail = v
| ⟨_, _⟩ := rfl

@[simp] theorem to_list_of_fn : ∀ {n} (f : fin n → α), to_list (of_fn f) = list.of_fn f
| 0     f := rfl
| (n+1) f := by rw [of_fn, list.of_fn_succ, to_list_cons, to_list_of_fn]

@[simp] theorem mk_to_list :
  ∀ (v : vector α n) h, (⟨to_list v, h⟩ : vector α n) = v
| ⟨l, h₁⟩ h₂ := rfl

@[simp]
lemma length_coe (v : vector α n) :
  ((coe : { l : list α // l.length = n } → list α) v).length = n :=
v.2

@[simp] lemma to_list_map {β : Type*} (v : vector α n) (f : α → β) : (v.map f).to_list =
  v.to_list.map f := by cases v; refl

theorem nth_eq_nth_le : ∀ (v : vector α n) (i),
  nth v i = v.to_list.nth_le i.1 (by rw to_list_length; exact i.2)
| ⟨l, h⟩ i := rfl

@[simp]
lemma nth_repeat (a : α) (i : fin n) :
  (vector.repeat a n).nth i = a :=
by apply list.nth_le_repeat

@[simp] lemma nth_map {β : Type*} (v : vector α n) (f : α → β) (i : fin n) :
  (v.map f).nth i = f (v.nth i) :=
by simp [nth_eq_nth_le]

@[simp] theorem nth_of_fn {n} (f : fin n → α) (i) : nth (of_fn f) i = f i :=
by rw [nth_eq_nth_le, ← list.nth_le_of_fn f];
   congr; apply to_list_of_fn

@[simp] theorem of_fn_nth (v : vector α n) : of_fn (nth v) = v :=
begin
  rcases v with ⟨l, rfl⟩,
  apply to_list_injective,
  change nth ⟨l, eq.refl _⟩ with λ i, nth ⟨l, rfl⟩ i,
  simpa only [to_list_of_fn] using list.of_fn_nth_le _
end

/-- The natural equivalence between length-`n` vectors and functions from `fin n`. -/
def _root_.equiv.vector_equiv_fin (α : Type*) (n : ℕ) : vector α n ≃ (fin n → α) :=
⟨vector.nth, vector.of_fn, vector.of_fn_nth, λ f, funext $ vector.nth_of_fn f⟩

theorem nth_tail (x : vector α n) (i) :
  x.tail.nth i = x.nth ⟨i.1 + 1, lt_tsub_iff_right.mp i.2⟩ :=
by { rcases x with ⟨_|_, h⟩; refl, }

@[simp]
theorem nth_tail_succ : ∀ (v : vector α n.succ) (i : fin n),
  nth (tail v) i = nth v i.succ
| ⟨a::l, e⟩ ⟨i, h⟩ := by simp [nth_eq_nth_le]; refl

@[simp] theorem tail_val : ∀ (v : vector α n.succ), v.tail.val = v.val.tail
| ⟨a::l, e⟩ := rfl

/-- The `tail` of a `nil` vector is `nil`. -/
@[simp] lemma tail_nil : (@nil α).tail = nil := rfl

/-- The `tail` of a vector made up of one element is `nil`. -/
@[simp] lemma singleton_tail (v : vector α 1) : v.tail = vector.nil :=
by simp only [←cons_head_tail, eq_iff_true_of_subsingleton]

@[simp] theorem tail_of_fn {n : ℕ} (f : fin n.succ → α) :
  tail (of_fn f) = of_fn (λ i, f i.succ) :=
(of_fn_nth _).symm.trans $ by { congr, funext i, cases i, simp, }

/-- The list that makes up a `vector` made up of a single element,
retrieved via `to_list`, is equal to the list of that single element. -/
@[simp] lemma to_list_singleton (v : vector α 1) : v.to_list = [v.head] :=
begin
  rw ←v.cons_head_tail,
  simp only [to_list_cons, to_list_nil, cons_head, eq_self_iff_true,
             and_self, singleton_tail]
end

/-- Mapping under `id` does not change a vector. -/
@[simp] lemma map_id {n : ℕ} (v : vector α n) : vector.map id v = v :=
  vector.eq _ _ (by simp only [list.map_id, vector.to_list_map])

lemma mem_iff_nth {a : α} {v : vector α n} : a ∈ v.to_list ↔ ∃ i, v.nth i = a :=
by simp only [list.mem_iff_nth_le, fin.exists_iff, vector.nth_eq_nth_le];
  exact ⟨λ ⟨i, hi, h⟩, ⟨i, by rwa to_list_length at hi, h⟩,
    λ ⟨i, hi, h⟩, ⟨i, by rwa to_list_length, h⟩⟩

lemma nodup_iff_nth_inj {v : vector α n} : v.to_list.nodup ↔ function.injective v.nth :=
begin
  cases v with l hl,
  subst hl,
  simp only [list.nodup_iff_nth_le_inj],
  split,
  { intros h i j hij,
    cases i, cases j, ext, apply h, simpa },
  { intros h i j hi hj hij,
    have := @h ⟨i, hi⟩ ⟨j, hj⟩, simp [nth_eq_nth_le] at *, tauto }
end

@[simp] lemma nth_mem (i : fin n) (v : vector α n) : v.nth i ∈ v.to_list :=
by rw [nth_eq_nth_le]; exact list.nth_le_mem _ _ _

theorem head'_to_list : ∀ (v : vector α n.succ),
  (to_list v).head' = some (head v)
| ⟨a::l, e⟩ := rfl

/-- Reverse a vector. -/
def reverse (v : vector α n) : vector α n :=
⟨v.to_list.reverse, by simp⟩

/-- The `list` of a vector after a `reverse`, retrieved by `to_list` is equal
to the `list.reverse` after retrieving a vector's `to_list`. -/
lemma to_list_reverse {v : vector α n} : v.reverse.to_list = v.to_list.reverse := rfl

@[simp]
lemma reverse_reverse {v : vector α n} : v.reverse.reverse = v :=
by { cases v, simp [vector.reverse], }

@[simp] theorem nth_zero : ∀ (v : vector α n.succ), nth v 0 = head v
| ⟨a::l, e⟩ := rfl

@[simp] theorem head_of_fn
  {n : ℕ} (f : fin n.succ → α) : head (of_fn f) = f 0 :=
by rw [← nth_zero, nth_of_fn]

@[simp] theorem nth_cons_zero
  (a : α) (v : vector α n) : nth (a ::ᵥ v) 0 = a :=
by simp [nth_zero]

/-- Accessing the `nth` element of a vector made up
of one element `x : α` is `x` itself. -/
@[simp] lemma nth_cons_nil {ix : fin 1}
  (x : α) : nth (x ::ᵥ nil) ix = x :=
by convert nth_cons_zero x nil

@[simp] theorem nth_cons_succ
  (a : α) (v : vector α n) (i : fin n) : nth (a ::ᵥ v) i.succ = nth v i :=
by rw [← nth_tail_succ, tail_cons]

/-- The last element of a `vector`, given that the vector is at least one element. -/
def last (v : vector α (n + 1)) : α := v.nth (fin.last n)

/-- The last element of a `vector`, given that the vector is at least one element. -/
lemma last_def {v : vector α (n + 1)} : v.last = v.nth (fin.last n) := rfl

/-- The `last` element of a vector is the `head` of the `reverse` vector. -/
lemma reverse_nth_zero {v : vector α (n + 1)} : v.reverse.head = v.last :=
begin
  have : 0 = v.to_list.length - 1 - n,
    { simp only [nat.add_succ_sub_one, add_zero, to_list_length, tsub_self,
                 list.length_reverse] },
  rw [←nth_zero, last_def, nth_eq_nth_le, nth_eq_nth_le],
  simp_rw [to_list_reverse, fin.val_eq_coe, fin.coe_last, fin.coe_zero, this],
  rw list.nth_le_reverse,
end

section scan

variables {β : Type*}
variables (f : β → α → β) (b : β)
variables (v : vector α n)

/--
Construct a `vector β (n + 1)` from a `vector α n` by scanning `f : β → α → β`
from the "left", that is, from 0 to `fin.last n`, using `b : β` as the starting value.
-/
def scanl : vector β (n + 1) :=
⟨list.scanl f b v.to_list, by rw [list.length_scanl, to_list_length]⟩

/-- Providing an empty vector to `scanl` gives the starting value `b : β`. -/
@[simp] lemma scanl_nil : scanl f b nil = b ::ᵥ nil := rfl

/--
The recursive step of `scanl` splits a vector `x ::ᵥ v : vector α (n + 1)`
into the provided starting value `b : β` and the recursed `scanl`
`f b x : β` as the starting value.

This lemma is the `cons` version of `scanl_nth`.
-/
@[simp] lemma scanl_cons (x : α) : scanl f b (x ::ᵥ v) = b ::ᵥ scanl f (f b x) v :=
by simpa only [scanl, to_list_cons]

/--
The underlying `list` of a `vector` after a `scanl` is the `list.scanl`
of the underlying `list` of the original `vector`.
-/
@[simp] lemma scanl_val : ∀ {v : vector α n}, (scanl f b v).val = list.scanl f b v.val
| ⟨l, hl⟩ := rfl

/--
The `to_list` of a `vector` after a `scanl` is the `list.scanl`
of the `to_list` of the original `vector`.
-/
@[simp] lemma to_list_scanl : (scanl f b v).to_list = list.scanl f b v.to_list := rfl

/--
The recursive step of `scanl` splits a vector made up of a single element
`x ::ᵥ nil : vector α 1` into a `vector` of the provided starting value `b : β`
and the mapped `f b x : β` as the last value.
-/
@[simp] lemma scanl_singleton (v : vector α 1) : scanl f b v = b ::ᵥ f b v.head ::ᵥ nil :=
begin
  rw [←cons_head_tail v],
  simp only [scanl_cons, scanl_nil, cons_head, singleton_tail]
end

/--
The first element of `scanl` of a vector `v : vector α n`,
retrieved via `head`, is the starting value `b : β`.
-/
@[simp] lemma scanl_head : (scanl f b v).head = b :=
begin
  cases n,
  { have : v = nil := by simp only [eq_iff_true_of_subsingleton],
    simp only [this, scanl_nil, cons_head] },
  { rw ←cons_head_tail v,
    simp only [←nth_zero, nth_eq_nth_le, to_list_scanl,
                to_list_cons, list.scanl, fin.val_zero', list.nth_le] }
end

/--
For an index `i : fin n`, the `nth` element of `scanl` of a
vector `v : vector α n` at `i.succ`, is equal to the application
function `f : β → α → β` of the `i.cast_succ` element of
`scanl f b v` and `nth v i`.

This lemma is the `nth` version of `scanl_cons`.
-/
@[simp] lemma scanl_nth (i : fin n) :
  (scanl f b v).nth i.succ = f ((scanl f b v).nth i.cast_succ) (v.nth i) :=
begin
  cases n,
  { exact fin_zero_elim i },
  induction n with n hn generalizing b,
  { have i0 : i = 0 := by simp only [eq_iff_true_of_subsingleton],
    simpa only [scanl_singleton, i0, nth_zero] },
  { rw [←cons_head_tail v, scanl_cons, nth_cons_succ],
    refine fin.cases _ _ i,
    { simp only [nth_zero, scanl_head, fin.cast_succ_zero, cons_head] },
    { intro i',
      simp only [hn, fin.cast_succ_fin_succ, nth_cons_succ] } }
end

end scan

/-- Monadic analog of `vector.of_fn`.
Given a monadic function on `fin n`, return a `vector α n` inside the monad. -/
def m_of_fn {m} [monad m] {α : Type u} : ∀ {n}, (fin n → m α) → m (vector α n)
| 0     f := pure nil
| (n+1) f := do a ← f 0, v ← m_of_fn (λi, f i.succ), pure (a ::ᵥ v)

theorem m_of_fn_pure {m} [monad m] [is_lawful_monad m] {α} :
  ∀ {n} (f : fin n → α), @m_of_fn m _ _ _ (λ i, pure (f i)) = pure (of_fn f)
| 0     f := rfl
| (n+1) f := by simp [m_of_fn, @m_of_fn_pure n, of_fn]

/-- Apply a monadic function to each component of a vector,
returning a vector inside the monad. -/
def mmap {m} [monad m] {α} {β : Type u} (f : α → m β) :
  ∀ {n}, vector α n → m (vector β n)
| 0 xs := pure nil
| (n+1) xs := do h' ← f xs.head, t' ← @mmap n xs.tail, pure (h' ::ᵥ t')

@[simp] theorem mmap_nil {m} [monad m] {α β} (f : α → m β) :
  mmap f nil = pure nil := rfl

@[simp] theorem mmap_cons {m} [monad m] {α β} (f : α → m β) (a) :
  ∀ {n} (v : vector α n), mmap f (a ::ᵥ v) =
  do h' ← f a, t' ← mmap f v, pure (h' ::ᵥ t')
| _ ⟨l, rfl⟩ := rfl

/-- Define `C v` by induction on `v : vector α n`.

This function has two arguments: `h_nil` handles the base case on `C nil`,
and `h_cons` defines the inductive step using `∀ x : α, C w → C (x ::ᵥ w)`. -/
@[elab_as_eliminator] def induction_on {C : Π {n : ℕ}, vector α n → Sort*}
  (v : vector α n)
  (h_nil : C nil)
  (h_cons : ∀ {n : ℕ} {x : α} {w : vector α n}, C w → C (x ::ᵥ w)) :
    C v :=
begin
  induction n with n ih generalizing v,
  { rcases v with ⟨_|⟨-,-⟩,-|-⟩,
    exact h_nil, },
  { rcases v with ⟨_|⟨a,v⟩,_⟩,
    cases v_property,
    apply @h_cons n _ ⟨v, (add_left_inj 1).mp v_property⟩,
    apply ih, }
end

variables {β γ : Type*}

/-- Define `C v w` by induction on a pair of vectors `v : vector α n` and `w : vector β n`. -/
@[elab_as_eliminator] def induction_on₂ {C : Π {n}, vector α n → vector β n → Sort*}
  (v : vector α n) (w : vector β n)
  (h_nil : C nil nil)
  (h_cons : ∀ {n a b} {x : vector α n} {y}, C x y → C (a ::ᵥ x) (b ::ᵥ y)) : C v w :=
begin
  induction n with n ih generalizing v w,
  { rcases v with ⟨_|⟨-,-⟩,-|-⟩, rcases w with ⟨_|⟨-,-⟩,-|-⟩,
    exact h_nil, },
  { rcases v with ⟨_|⟨a,v⟩,_⟩,
    cases v_property,
    rcases w with ⟨_|⟨b,w⟩,_⟩,
    cases w_property,
    apply @h_cons n _ _ ⟨v, (add_left_inj 1).mp v_property⟩ ⟨w, (add_left_inj 1).mp w_property⟩,
    apply ih, }
end

/-- Define `C u v w` by induction on a triplet of vectors
`u : vector α n`, `v : vector β n`, and `w : vector γ b`. -/
@[elab_as_eliminator] def induction_on₃ {C : Π {n}, vector α n → vector β n → vector γ n → Sort*}
  (u : vector α n) (v : vector β n) (w : vector γ n)
  (h_nil : C nil nil nil)
  (h_cons : ∀ {n a b c} {x : vector α n} {y z}, C x y z → C (a ::ᵥ x) (b ::ᵥ y) (c ::ᵥ z)) :
  C u v w :=
begin
  induction n with n ih generalizing u v w,
  { rcases u with ⟨_|⟨-,-⟩,-|-⟩, rcases v with ⟨_|⟨-,-⟩,-|-⟩, rcases w with ⟨_|⟨-,-⟩,-|-⟩,
    exact h_nil, },
  { rcases u with ⟨_|⟨a,u⟩,_⟩,
    cases u_property,
    rcases v with ⟨_|⟨b,v⟩,_⟩,
    cases v_property,
    rcases w with ⟨_|⟨c,w⟩,_⟩,
    cases w_property,
    apply @h_cons n _ _ _ ⟨u, (add_left_inj 1).mp u_property⟩ ⟨v, (add_left_inj 1).mp v_property⟩
      ⟨w, (add_left_inj 1).mp w_property⟩,
    apply ih, }
end

/-- Cast a vector to an array. -/
def to_array : vector α n → array n α
| ⟨xs, h⟩ := cast (by rw h) xs.to_array

section insert_nth
variable {a : α}

/-- `v.insert_nth a i` inserts `a` into the vector `v` at position `i`
(and shifting later components to the right). -/
def insert_nth (a : α) (i : fin (n+1)) (v : vector α n) : vector α (n+1) :=
⟨v.1.insert_nth i a,
  begin
    rw [list.length_insert_nth, v.2],
    rw [v.2, ← nat.succ_le_succ_iff],
    exact i.2
  end⟩

lemma insert_nth_val {i : fin (n+1)} {v : vector α n} :
  (v.insert_nth a i).val = v.val.insert_nth i.1 a :=
rfl

@[simp] lemma remove_nth_val {i : fin n} :
  ∀{v : vector α n}, (remove_nth i v).val = v.val.remove_nth i
| ⟨l, hl⟩ := rfl

lemma remove_nth_insert_nth {v : vector α n} {i : fin (n+1)} :
  remove_nth i (insert_nth a i v) = v :=
subtype.eq $ list.remove_nth_insert_nth i.1 v.1

lemma remove_nth_insert_nth' {v : vector α (n+1)} :
  ∀{i : fin (n+1)} {j : fin (n+2)},
    remove_nth (j.succ_above i) (insert_nth a j v) = insert_nth a (i.pred_above j) (remove_nth i v)
| ⟨i, hi⟩ ⟨j, hj⟩ :=
  begin
    dsimp [insert_nth, remove_nth, fin.succ_above, fin.pred_above],
    simp only [subtype.mk_eq_mk],
    split_ifs,
    { convert (list.insert_nth_remove_nth_of_ge i (j-1) _ _ _).symm,
      { convert (nat.succ_pred_eq_of_pos _).symm, exact lt_of_le_of_lt (zero_le _) h, },
      { apply remove_nth_val, },
      { convert hi, exact v.2, },
      { exact nat.le_pred_of_lt h, }, },
    { convert (list.insert_nth_remove_nth_of_le i j _ _ _).symm,
      { apply remove_nth_val, },
      { convert hi, exact v.2, },
      { simpa using h, }, }
  end

lemma insert_nth_comm (a b : α) (i j : fin (n+1)) (h : i ≤ j) :
  ∀(v : vector α n),
    (v.insert_nth a i).insert_nth b j.succ = (v.insert_nth b j).insert_nth a i.cast_succ
| ⟨l, hl⟩ :=
  begin
    refine subtype.eq _,
    simp only [insert_nth_val, fin.coe_succ, fin.cast_succ, fin.val_eq_coe, fin.coe_cast_add],
    apply list.insert_nth_comm,
    { assumption },
    { rw hl, exact nat.le_of_succ_le_succ j.2 }
  end

end insert_nth

section update_nth

/-- `update_nth v n a` replaces the `n`th element of `v` with `a` -/
def update_nth (v : vector α n) (i : fin n) (a : α) : vector α n :=
⟨v.1.update_nth i.1 a, by rw [list.update_nth_length, v.2]⟩

@[simp] lemma to_list_update_nth (v : vector α n) (i : fin n) (a : α) :
  (v.update_nth i a).to_list = v.to_list.update_nth i a :=
rfl

@[simp] lemma nth_update_nth_same (v : vector α n) (i : fin n) (a : α) :
  (v.update_nth i a).nth i = a :=
by cases v; cases i; simp [vector.update_nth, vector.nth_eq_nth_le]

lemma nth_update_nth_of_ne {v : vector α n} {i j : fin n} (h : i ≠ j) (a : α) :
  (v.update_nth i a).nth j = v.nth j :=
by cases v; cases i; cases j; simp [vector.update_nth, vector.nth_eq_nth_le,
  list.nth_le_update_nth_of_ne (fin.vne_of_ne h)]

lemma nth_update_nth_eq_if {v : vector α n} {i j : fin n} (a : α) :
  (v.update_nth i a).nth j = if i = j then a else v.nth j :=
by split_ifs; try {simp *}; try {rw nth_update_nth_of_ne}; assumption

@[to_additive]
lemma prod_update_nth [monoid α] (v : vector α n) (i : fin n) (a : α) :
  (v.update_nth i a).to_list.prod =
    (v.take i).to_list.prod * a * (v.drop (i + 1)).to_list.prod :=
begin
  refine (list.prod_update_nth v.to_list i a).trans _,
  have : ↑i < v.to_list.length := lt_of_lt_of_le i.2 (le_of_eq v.2.symm),
  simp [this],
end

@[to_additive]
lemma prod_update_nth' [comm_group α] (v : vector α n) (i : fin n) (a : α) :
  (v.update_nth i a).to_list.prod =
    v.to_list.prod * (v.nth i)⁻¹ * a :=
begin
  refine (list.prod_update_nth' v.to_list i a).trans _,
  have : ↑i < v.to_list.length := lt_of_lt_of_le i.2 (le_of_eq v.2.symm),
  simp [this, nth_eq_nth_le, mul_assoc],
end

end update_nth

end vector

namespace vector

section traverse

variables {F G : Type u → Type u}
variables [applicative F] [applicative G]

open applicative functor
open list (cons) nat

private def traverse_aux {α β : Type u} (f : α → F β) :
  Π (x : list α), F (vector β x.length)
| []      := pure vector.nil
| (x::xs) := vector.cons <$> f x <*> traverse_aux xs

/-- Apply an applicative function to each component of a vector. -/
protected def traverse {α β : Type u} (f : α → F β) : vector α n → F (vector β n)
| ⟨v, Hv⟩ := cast (by rw Hv) $ traverse_aux f v

section
variables {α β : Type u}

@[simp] protected lemma traverse_def
  (f : α → F β) (x : α) : ∀ (xs : vector α n),
  (x ::ᵥ xs).traverse f = cons <$> f x <*> xs.traverse f :=
by rintro ⟨xs, rfl⟩; refl

protected lemma id_traverse : ∀ (x : vector α n), x.traverse id.mk = x :=
begin
  rintro ⟨x, rfl⟩, dsimp [vector.traverse, cast],
  induction x with x xs IH, {refl},
  simp! [IH], refl
end

end

open function

variables [is_lawful_applicative F] [is_lawful_applicative G]
variables {α β γ : Type u}

-- We need to turn off the linter here as
-- the `is_lawful_traversable` instance below expects a particular signature.
@[nolint unused_arguments]
protected lemma comp_traverse (f : β → F γ) (g : α → G β) : ∀ (x : vector α n),
  vector.traverse (comp.mk ∘ functor.map f ∘ g) x =
  comp.mk (vector.traverse f <$> vector.traverse g x) :=
by rintro ⟨x, rfl⟩; dsimp [vector.traverse, cast];
   induction x with x xs; simp! [cast, *] with functor_norm;
   [refl, simp [(∘)]]

protected lemma traverse_eq_map_id {α β} (f : α → β) : ∀ (x : vector α n),
  x.traverse (id.mk ∘ f) = id.mk (map f x) :=
by rintro ⟨x, rfl⟩; simp!;
   induction x; simp! * with functor_norm; refl

variable (η : applicative_transformation F G)

protected lemma naturality {α β : Type*}
  (f : α → F β) : ∀ (x : vector α n),
  η (x.traverse f) = x.traverse (@η _ ∘ f) :=
by rintro ⟨x, rfl⟩; simp! [cast];
   induction x with x xs IH; simp! * with functor_norm

end traverse

instance : traversable.{u} (flip vector n) :=
{ traverse := @vector.traverse n,
  map := λ α β, @vector.map.{u u} α β n }

instance : is_lawful_traversable.{u} (flip vector n) :=
{ id_traverse := @vector.id_traverse n,
  comp_traverse := @vector.comp_traverse n,
  traverse_eq_map_id := @vector.traverse_eq_map_id n,
  naturality := @vector.naturality n,
  id_map := by intros; cases x; simp! [(<$>)],
  comp_map := by intros; cases x; simp! [(<$>)] }

end vector
