/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Additional theorems about the `vector` type.
-/
import data.vector
import data.list.nodup
import data.list.of_fn
import control.applicative

universes u
variables {n : ℕ}

namespace vector
variables {α : Type*}

attribute [simp] head_cons tail_cons

instance [inhabited α] : inhabited (vector α n) :=
⟨of_fn (λ _, default α)⟩

theorem to_list_injective : function.injective (@to_list α n) :=
subtype.val_injective

@[simp] theorem cons_val (a : α) : ∀ (v : vector α n), (a :: v).val = a :: v.val
| ⟨_, _⟩ := rfl

@[simp] theorem cons_head (a : α) : ∀ (v : vector α n), (a :: v).head = a
| ⟨_, _⟩ := rfl

@[simp] theorem cons_tail (a : α) : ∀ (v : vector α n), (a :: v).tail = v
| ⟨_, _⟩ := rfl

@[simp] theorem to_list_of_fn : ∀ {n} (f : fin n → α), to_list (of_fn f) = list.of_fn f
| 0     f := rfl
| (n+1) f := by rw [of_fn, list.of_fn_succ, to_list_cons, to_list_of_fn]

@[simp] theorem mk_to_list :
  ∀ (v : vector α n) h, (⟨to_list v, h⟩ : vector α n) = v
| ⟨l, h₁⟩ h₂ := rfl

@[simp] lemma to_list_map {β : Type*} (v : vector α n) (f : α → β) : (v.map f).to_list =
  v.to_list.map f := by cases v; refl

theorem nth_eq_nth_le : ∀ (v : vector α n) (i),
  nth v i = v.to_list.nth_le i.1 (by rw to_list_length; exact i.2)
| ⟨l, h⟩ i := rfl

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
  simp [nth, list.of_fn_nth_le]
end

@[simp] theorem nth_tail : ∀ (v : vector α n.succ) (i : fin n),
  nth (tail v) i = nth v i.succ
| ⟨a::l, e⟩ ⟨i, h⟩ := by simp [nth_eq_nth_le]; refl

@[simp] theorem tail_val : ∀ (v : vector α n.succ), v.tail.val = v.val.tail
| ⟨a::l, e⟩ := rfl

@[simp] theorem tail_of_fn {n : ℕ} (f : fin n.succ → α) :
  tail (of_fn f) = of_fn (λ i, f i.succ) :=
(of_fn_nth _).symm.trans $ by congr; funext i; simp

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
    cases i, cases j, simp [nth_eq_nth_le] at *, tauto },
  { intros h i j hi hj hij,
    have := @h ⟨i, hi⟩ ⟨j, hj⟩, simp [nth_eq_nth_le] at *, tauto }
end

@[simp] lemma nth_mem (i : fin n) (v : vector α n) : v.nth i ∈ v.to_list :=
by rw [nth_eq_nth_le]; exact list.nth_le_mem _ _ _

theorem head'_to_list : ∀ (v : vector α n.succ),
  (to_list v).head' = some (head v)
| ⟨a::l, e⟩ := rfl

def reverse (v : vector α n) : vector α n :=
⟨v.to_list.reverse, by simp⟩

@[simp] theorem nth_zero : ∀ (v : vector α n.succ), nth v 0 = head v
| ⟨a::l, e⟩ := rfl

@[simp] theorem head_of_fn
  {n : ℕ} (f : fin n.succ → α) : head (of_fn f) = f 0 :=
by rw [← nth_zero, nth_of_fn]

@[simp] theorem nth_cons_zero
  (a : α) (v : vector α n) : nth (a :: v) 0 = a :=
by simp [nth_zero]

@[simp] theorem nth_cons_succ
  (a : α) (v : vector α n) (i : fin n) : nth (a :: v) i.succ = nth v i :=
by rw [← nth_tail, tail_cons]

def m_of_fn {m} [monad m] {α : Type u} : ∀ {n}, (fin n → m α) → m (vector α n)
| 0     f := pure nil
| (n+1) f := do a ← f 0, v ← m_of_fn (λi, f i.succ), pure (a :: v)

theorem m_of_fn_pure {m} [monad m] [is_lawful_monad m] {α} :
  ∀ {n} (f : fin n → α), @m_of_fn m _ _ _ (λ i, pure (f i)) = pure (of_fn f)
| 0     f := rfl
| (n+1) f := by simp [m_of_fn, @m_of_fn_pure n, of_fn]

def mmap {m} [monad m] {α} {β : Type u} (f : α → m β) :
  ∀ {n}, vector α n → m (vector β n)
| _ ⟨[], rfl⟩   := pure nil
| _ ⟨a::l, rfl⟩ := do h' ← f a, t' ← mmap ⟨l, rfl⟩, pure (h' :: t')

@[simp] theorem mmap_nil {m} [monad m] {α β} (f : α → m β) :
  mmap f nil = pure nil := rfl

@[simp] theorem mmap_cons {m} [monad m] {α β} (f : α → m β) (a) :
  ∀ {n} (v : vector α n), mmap f (a::v) =
  do h' ← f a, t' ← mmap f v, pure (h' :: t')
| _ ⟨l, rfl⟩ := rfl

@[ext] theorem ext : ∀ {v w : vector α n}
  (h : ∀ m : fin n, vector.nth v m = vector.nth w m), v = w
| ⟨v, hv⟩ ⟨w, hw⟩ h := subtype.eq (list.ext_le (by rw [hv, hw])
  (λ m hm hn, h ⟨m, hv ▸ hm⟩))

instance zero_subsingleton : subsingleton (vector α 0) :=
⟨λ _ _, vector.ext (λ m, fin.elim0 m)⟩

def to_array : vector α n → array n α
| ⟨xs, h⟩ := cast (by rw h) xs.to_array

section insert_nth
variable {a : α}

def insert_nth (a : α) (i : fin (n+1)) (v : vector α n) : vector α (n+1) :=
⟨v.1.insert_nth i.1 a,
  begin
    rw [list.length_insert_nth, v.2],
    rw [v.2, ← nat.succ_le_succ_iff],
    exact i.2
  end⟩

lemma insert_nth_val {i : fin (n+1)} {v : vector α n} :
  (v.insert_nth a i).val = v.val.insert_nth i.1 a :=
rfl

@[simp] lemma remove_nth_val {i : fin n} :
  ∀{v : vector α n}, (remove_nth i v).val = v.val.remove_nth i.1
| ⟨l, hl⟩ := rfl

lemma remove_nth_insert_nth {v : vector α n} {i : fin (n+1)} : remove_nth i (insert_nth a i v) = v :=
subtype.eq $ list.remove_nth_insert_nth i.1 v.1

lemma remove_nth_insert_nth_ne {v : vector α (n+1)} :
  ∀{i j : fin (n+2)} (h : i ≠ j),
    remove_nth i (insert_nth a j v) = insert_nth a (i.pred_above j h.symm) (remove_nth (j.pred_above i h) v)
| ⟨i, hi⟩ ⟨j, hj⟩ ne :=
  begin
    have : i ≠ j := fin.vne_of_ne ne,
    refine subtype.eq _,
    dsimp [insert_nth, remove_nth, fin.pred_above, fin.cast_lt, -subtype.val_eq_coe],
    rcases lt_trichotomy i j with h | h | h,
    { have h_nji : ¬ j < i := lt_asymm h,
      have j_pos : 0 < j := lt_of_le_of_lt (zero_le i) h,
      simp [h, h_nji, fin.lt_iff_val_lt_val, -subtype.val_eq_coe],
      rw [show j.pred = j - 1, from rfl, list.insert_nth_remove_nth_of_ge, nat.sub_add_cancel j_pos],
      { rw [v.2], exact lt_of_lt_of_le h (nat.le_of_succ_le_succ hj) },
      { exact nat.le_sub_right_of_add_le h } },
    { exact (this h).elim },
    { have h_nij : ¬ i < j := lt_asymm h,
      have i_pos : 0 < i := lt_of_le_of_lt (zero_le j) h,
      simp [h, h_nij, fin.lt_iff_val_lt_val],
      rw [show i.pred = i - 1, from rfl, list.insert_nth_remove_nth_of_le, nat.sub_add_cancel i_pos],
      { show i - 1 + 1 ≤ v.val.length,
        rw [v.2, nat.sub_add_cancel i_pos],
        exact nat.le_of_lt_succ hi },
      { exact nat.le_sub_right_of_add_le h } }
  end

lemma insert_nth_comm (a b : α) (i j : fin (n+1)) (h : i ≤ j) :
  ∀(v : vector α n), (v.insert_nth a i).insert_nth b j.succ = (v.insert_nth b j).insert_nth a i.cast_succ
| ⟨l, hl⟩ :=
  begin
    refine subtype.eq _,
    simp [insert_nth_val, fin.succ_val, fin.cast_succ],
    apply list.insert_nth_comm,
    { assumption },
    { rw hl, exact nat.le_of_succ_le_succ j.2 }
  end

end insert_nth

section update_nth

/-- `update_nth v n a` replaces the `n`th element of `v` with `a` -/
def update_nth (v : vector α n) (i : fin n) (a : α) : vector α n :=
⟨v.1.update_nth i.1 a, by rw [list.update_nth_length, v.2]⟩

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

protected def traverse {α β : Type u} (f : α → F β) : vector α n → F (vector β n)
| ⟨v, Hv⟩ := cast (by rw Hv) $ traverse_aux f v

variables [is_lawful_applicative F] [is_lawful_applicative G]
variables {α β γ : Type u}

@[simp] protected lemma traverse_def
  (f : α → F β) (x : α) : ∀ (xs : vector α n),
  (x :: xs).traverse f = cons <$> f x <*> xs.traverse f :=
by rintro ⟨xs, rfl⟩; refl

protected lemma id_traverse : ∀ (x : vector α n), x.traverse id.mk = x :=
begin
  rintro ⟨x, rfl⟩, dsimp [vector.traverse, cast],
  induction x with x xs IH, {refl},
  simp! [IH], refl
end

open function

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
