import theories.number_theory.pell data.set data.pfun

universe u

open nat function

namespace int
  lemma eq_nat_abs_iff_mul (x n) : nat_abs x = n ↔ (x - n) * (x + n) = 0 :=
  begin
    refine iff.trans _ mul_eq_zero_iff_eq_zero_or_eq_zero.symm,
    refine iff.trans _ (or_congr sub_eq_zero_iff_eq (show _ ↔ x = -↑n, by rw ← sub_neg_eq_add; exact sub_eq_zero_iff_eq)).symm,
    exact ⟨λe, by rw ← e; apply nat_abs_eq, λo, by cases o; rw a; try {rw nat_abs_neg}; refl⟩
  end

  example : integral_domain int := by apply_instance
end int

inductive fin2 : ℕ → Type
| fz {n} : fin2 (succ n)
| fs {n} : fin2 n → fin2 (succ n)

namespace fin2

  @[elab_as_eliminator]
  protected def cases' {n} {C : fin2 (succ n) → Sort u} (H1 : C fz) (H2 : Π n, C (fs n)) :
    Π (i : fin2 (succ n)), C i
  | fz     := H1
  | (fs n) := H2 n
  
  def elim0 {C : fin2 0 → Sort u} : Π (i : fin2 0), C i.

  def opt_of_nat : Π {n} (k : ℕ), option (fin2 n)
  | 0 _ := none
  | (succ n) 0 := some fz
  | (succ n) (succ k) := fs <$> @opt_of_nat n k
  
  def add {n} (i : fin2 n) : Π k, fin2 (n + k)
  | 0        := i
  | (succ k) := fs (add k)
  
  def left (k) : Π {n}, fin2 n → fin2 (k + n)
  | ._ (@fz n)   := fz
  | ._ (@fs n i) := fs (left i)
  
  def insert_perm : Π {n}, fin2 n → fin2 n → fin2 n
  | ._ (@fz n)          (@fz ._)   := fz
  | ._ (@fz n)          (@fs ._ j) := fs j
  | ._ (@fs (succ n) i) (@fz ._)   := fs fz
  | ._ (@fs (succ n) i) (@fs ._ j) := match insert_perm i j with fz := fz | fs k := fs (fs k) end

  def remap_left {m n} (f : fin2 m → fin2 n) : Π k, fin2 (m + k) → fin2 (n + k)
  | 0        i          := f i
  | (succ k) (@fz ._)   := fz
  | (succ k) (@fs ._ i) := fs (remap_left _ i)

  class is_lt (m n : ℕ) := (h : m < n)
  instance is_lt.zero (n) : is_lt 0 (succ n) := ⟨succ_pos _⟩
  instance is_lt.succ (m n) [l : is_lt m n] : is_lt (succ m) (succ n) := ⟨succ_lt_succ l.h⟩

  def of_nat' : Π {n} m [is_lt m n], fin2 n
  | 0        m        ⟨h⟩ := absurd h (not_lt_zero _)
  | (succ n) 0        ⟨h⟩ := fz
  | (succ n) (succ m) ⟨h⟩ := fs (@of_nat' n m ⟨lt_of_succ_lt_succ h⟩)

  local prefix `&`:max := of_nat'

end fin2

open fin2

inductive vector2 (α : Type u) : ℕ → Type u
| nil {} : vector2 0
| cons {n} : α → vector2 n → vector2 (succ n)

notation a :: b := vector2.cons a b
notation `[` l:(foldr `, ` (h t, vector2.cons h t) vector2.nil `]`) := l

def vector3 (α : Type u) (n : ℕ) : Type u := fin2 n → α

namespace vector3

  @[pattern] def nil {α} : vector3 α 0 := λi, match i with end
  @[pattern] def cons {α} {n} (a : α) (v : vector3 α n) : vector3 α (succ n) :=
  λi, by {refine i.cases' _ _, exact a, exact v}

  notation a :: b := cons a b
  notation `[` l:(foldr `, ` (h t, cons h t) nil `]`) := l

  @[simp] def cons_fz {α} {n} (a : α) (v : vector3 α n) : (a :: v) fz = a := rfl
  @[simp] def cons_fs {α} {n} (a : α) (v : vector3 α n) (i) : (a :: v) (fs i) = v i := rfl

  @[reducible] def nth {α} {n} (i : fin2 n) (v : vector3 α n) : α := v i

  @[reducible] def of_fn {α} {n} (f : fin2 n → α) : vector3 α n := f

  def head {α} {n} (v : vector3 α (succ n)) : α := v fz

  def tail {α} {n} (v : vector3 α (succ n)) : vector3 α n := λi, v (fs i)

  theorem eq_nil {α} (v : vector3 α 0) : v = [] :=
  funext $ λi, match i with end

  theorem cons_head_tail {α} {n} (v : vector3 α (succ n)) : head v :: tail v = v :=
  funext $ λi, fin2.cases' rfl (λ_, rfl) i

  def nil_elim {α} {C : vector3 α 0 → Sort u} (H : C []) (v : vector3 α 0) : C v :=
  by rw eq_nil v; apply H

  def cons_elim {α n} {C : vector3 α (succ n) → Sort u} (H : Π (a : α) (t : vector3 α n), C (a :: t))
    (v : vector3 α (succ n)) : C v :=
  by rw ← (cons_head_tail v); apply H

  @[simp] theorem cons_elim_cons {α n C H a t} : @cons_elim α n C H (a :: t) = H a t := rfl

  @[elab_as_eliminator]
  protected def rec_on {α} {C : Π {n}, vector3 α n → Sort u} {n} (v : vector3 α n)
    (H0 : C [])
    (Hs : Π {n} (a) (w : vector3 α n), C w → C (a :: w)) : C v :=
  nat.rec_on n
    (λv, v.nil_elim H0)
    (λn IH v, v.cons_elim (λa t, Hs _ _ (IH _))) v

  @[simp] theorem rec_on_nil {α C H0 Hs} : @vector3.rec_on α @C 0 [] H0 @Hs = H0 :=
  rfl

  @[simp] theorem rec_on_cons {α C H0 Hs n a v} :
    @vector3.rec_on α @C (succ n) (a :: v) H0 @Hs = Hs a v (@vector3.rec_on α @C n v H0 @Hs) :=
  rfl

  def append {α} {m} (v : vector3 α m) {n} (w : vector3 α n) : vector3 α (n+m) :=
  nat.rec_on m (λ_, w) (λm IH v, v.cons_elim $ λa t, @fin2.cases' (n+m) (λ_, α) a (IH t)) v

  infix ` +-+ `:65 := append

  @[simp] def append_nil {α} {n} (w : vector3 α n) : [] +-+ w = w := rfl

  @[simp] def append_cons {α} (a : α) {m} (v : vector3 α m) {n} (w : vector3 α n) :
    (a::v) +-+ w = a :: (v +-+ w) := rfl

  @[simp] def append_left {α} : ∀ {m} (i : fin2 m) (v : vector3 α m) {n} (w : vector3 α n),
    (v +-+ w) (left n i) = v i
  | ._ (@fz m)   v n w := v.cons_elim (λa t, by simp [*, left])
  | ._ (@fs m i) v n w := v.cons_elim (λa t, by simp [*, left])

  @[simp] def append_add {α} : ∀ {m} (v : vector3 α m) {n} (w : vector3 α n) (i : fin2 n),
    (v +-+ w) (add i m) = w i
  | 0        v n w i := rfl
  | (succ m) v n w i := v.cons_elim (λa t, by simp [*, add])

  def insert {α} (a : α) {n} (v : vector3 α n) (i : fin2 (succ n)) : vector3 α (succ n) :=
  λj, (a :: v) (insert_perm i j)

  @[simp] theorem insert_fz {α} (a : α) {n} (v : vector3 α n) : insert a v fz = a :: v :=
  by refine funext (λj, j.cases' _ _); intros; refl

  @[simp] def insert_fs {α} (a : α) {n} (b : α) (v : vector3 α n) (i : fin2 (succ n)) :
    insert a (b :: v) (fs i) = b :: insert a v i :=
  funext $ λj, by {
    refine j.cases' _ (λj, _); simp [insert, insert_perm],
    refine fin2.cases' _ _ (insert_perm i j); simp [insert_perm] }

  theorem append_insert {α} (a : α) {k} (t : vector3 α k) {n} (v : vector3 α n) (i : fin2 (succ n)) (e : succ n + k = succ (n + k)) :
    insert a (t +-+ v) (eq.rec_on e (i.add k)) = eq.rec_on e (t +-+ insert a v i) :=
  begin
    refine vector3.rec_on t (λe, _) (λk b t IH e, _) e, refl,
    have e' := succ_add n k,
    change insert a (b :: (t +-+ v)) (eq.rec_on (congr_arg succ e') (fs (add i k)))
      = eq.rec_on (congr_arg succ e') (b :: (t +-+ insert a v i)),
    rw ← (eq.drec_on e' rfl : fs (eq.rec_on e' (i.add k) : fin2 (succ (n + k))) = eq.rec_on (congr_arg succ e') (fs (i.add k))),
    simp, rw IH, exact eq.drec_on e' rfl
  end

end vector3

/-
namespace vector2

def cons_elim {α n} {C : vector2 α (succ n) → Sort u} (H : Π (a : α) (t : vector2 α n), C (a :: t)) :
  Π (v : vector2 α (succ n)), C v
| (a::t) := H a t

def nth {α} : Π {n}, fin2 n → vector2 α n → α
| ._ (@fz n)   (a :: v) := a
| ._ (@fs n i) (a :: v) := nth i v

def of_fn {α} : Π {n}, (fin2 n → α) → vector2 α n
| 0 f := []
| (succ n) f := f fz :: of_fn (f ∘ fs)

@[simp] theorem nth_of_fn {α} : Π {n} (i : fin2 n) (f : fin2 n → α), (of_fn f).nth i = f i
| ._ (@fz n)   f := rfl
| ._ (@fs n i) f := by simph [nth, of_fn]

@[simp] theorem of_fn_nth {α} : Π {n} (v : vector2 α n), of_fn (λi, v.nth i) = v
| ._ []               := rfl
| ._ (@cons ._ n a v) := by dsimp [nth, of_fn]; rw of_fn_nth

def append {α} : Π {m}, vector2 α m → Π {n}, vector2 α n → vector2 α (n+m)
| ._ []               n w := w
| ._ (@cons ._ m a v) n w := a :: append v w

infix ` +-+ `:65 := append

inductive left_extends {α m} (v : vector2 α m) : Π {n}, vector2 α n → Prop
| refl : left_extends v
| cons {} {n} {w : vector2 α n} (a) : left_extends w → left_extends (a :: w)

infix ` ≺ `:50 := left_extends

theorem left_extends.le {α m} {v : vector2 α m} {n} {w : vector2 α n} (h : v ≺ w) : m ≤ n :=
by { induction h, apply nat.le_refl, apply le_succ_of_le ih_1 }

theorem append_left_extends {α m} (v : vector2 α m) : Π {n} (w : vector2 α n), v ≺ w +-+ v
| ._ []               := left_extends.refl _
| ._ (@cons ._ n a w) := left_extends.cons a (append_left_extends w)

theorem left_extends_iff_append {α m} {v : vector2 α m} {n} {w : vector2 α n} : v ≺ w ↔ ∃ k (e : n = m + k) (t : vector2 α k), t +-+ v = eq.rec_on e w :=
⟨λh, by {
  induction h with n w a h IH,
  exact ⟨0, rfl, [], rfl⟩,
  exact match n, w, IH with ._, ._, ⟨k, rfl, t, rfl⟩ := ⟨succ k, rfl, a::t, rfl⟩ end },
λh, match n, w, h with ._, ._, ⟨k, rfl, t, rfl⟩ := append_left_extends v t end⟩

theorem exists_left_extends_iff_append {α m} {v : vector2 α m} {n} {p : vector2 α (m + n) → Prop} : (∃w, v ≺ w ∧ p w) ↔ ∃ w, p (w +-+ v) :=
⟨λ⟨w, h, pw⟩, let ⟨k, e, t, ht⟩ := left_extends_iff_append.1 h in
  match k, nat.add_left_cancel e, e, t, w, ht, pw with ._, rfl, rfl, t, ._, rfl, pw := ⟨t, pw⟩ end,
λ⟨w, pw⟩, ⟨_, append_left_extends _ _, pw⟩⟩

-- the first two cases are redundant, but I couldn't otherwise get the match to compile
def insert {α} (a : α) : Π {n}, vector2 α n → fin2 (succ n) → vector2 α (succ n)
| ._ []               fz     := [a]
| ._ (@cons ._ n b v) fz     := a :: b :: v
| ._ (@cons ._ n b v) (fs i) := b :: insert v i

@[simp] theorem insert_fz {α} (a : α) : Π {n} (v : vector2 α n), insert a v fz = a :: v
| ._ []               := rfl
| ._ (@cons ._ n b w) := rfl

theorem insert_perm_nth {α} (a : α) : Π {n} (v : vector2 α n) (i : fin2 (succ n)) (j : fin2 (succ n)), nth j (insert a v i) = nth (insert_perm i j) (a :: v)
| ._ []               fz     fz     := by simph[insert, nth, insert_perm]
| ._ (@cons ._ n b v) fz     fz     := by simph[insert, nth, insert_perm]
| ._ (@cons ._ n b v) fz     (fs j) := by simph[insert, nth, insert_perm]
| ._ (@cons ._ n b v) (fs i) fz     := by simph[insert, nth, insert_perm]
| ._ (@cons ._ n b v) (fs i) (fs j) := by simph[insert, nth, insert_perm]; cases (insert_perm i j); simp [nth, insert_perm]

@[simp] theorem insert_nth {α} (a : α) : Π {n} (v : vector2 α n) (i : fin2 (succ n)), nth i (insert a v i) = a
| ._ []               fz     := rfl
| ._ (@cons ._ n b v) fz     := rfl
| ._ (@cons ._ n b v) (fs i) := by simph[insert, nth]

theorem append_insert {α} (a : α) : Π {k} (t : vector2 α k) {n} (v : vector2 α n) (i : fin2 (succ n)) (e : succ n + k = succ (n + k)),
  insert a (t +-+ v) (eq.rec_on e (i.add k)) = eq.rec_on e (t +-+ insert a v i)
| ._ []               n v i e := rfl
| ._ (@cons ._ k b t) n v i e := let e' := succ_add n k in
  show insert a (b :: (t +-+ v)) (eq.rec_on (congr_arg succ e') (fs (add i k)))
     = eq.rec_on (congr_arg succ e') (b :: (t +-+ insert a v i)), from
  by rw ← (eq.drec_on e' rfl : fs (eq.rec_on e' (i.add k) : fin2 (succ (n + k))) = eq.rec_on (congr_arg succ e') (fs (i.add k)));
     dsimp [insert]; rw append_insert; exact eq.drec_on (succ_add n k) rfl

end vector2
-/
open vector3

/-def vector.nth' {α} : Π {n} (v : vector α n), fin n → α
| 0     v i        := i.elim0
| (n+1) v ⟨0,   h⟩ := v.head
| (n+1) v ⟨i+1, h⟩ := @vector.nth' n v.tail ⟨i, nat.le_of_succ_le_succ h⟩

theorem vector.nth'_eq_nth_le {α} : Π (l : list α) (i h), vector.nth' ⟨l, rfl⟩ ⟨i, h⟩ = l.nth_le i h
| []       n     h := absurd h n.not_lt_zero
| (a :: l) 0     h := by simp [list.nth_le, vector.nth', vector.head]
| (a :: l) (n+1) h := by simp [list.nth_le, vector.nth', vector.tail]; apply vector.nth'_eq_nth_le

theorem vector.nth'_eq_nth_le' {α : Type u} {n : nat} (v : vector α n) : ∀ (i : fin n),
  @vector.nth' _ n v i = v.1.nth_le i.1 (eq.substr v.2 i.2) :=
v.elim $ by exact λl ⟨i, h⟩, vector.nth'_eq_nth_le l i h

@[simp] theorem vector.nth'_zero {α n} (v : vector α (n+1)) : v.nth' 0 = v.head := rfl

@[simp] theorem vector.nth'_succ {α n} (v : vector α (n+1)) : ∀ (i : fin n), v.nth' i.succ = v.tail.nth' i
| ⟨i, h⟩ := rfl

@[simp] theorem vector.nth'_of_fn {α} : Π {n} (f : fin n → α) (i : fin n), (vector.of_fn f).nth' i = f i
| 0     f i        := i.elim0
| (n+1) f ⟨0,   h⟩ := by simp [vector.nth', vector.of_fn, vector.head_cons];
                        rw ← (@fin.eq_of_veq n.succ 0 ⟨0, h⟩ rfl)
| (n+1) f ⟨i+1, h⟩ := by simp [vector.nth', vector.of_fn, vector.tail_cons]; apply vector.nth'_of_fn

@[simp] theorem vector.of_fn_nth' {α} : Π {n} (v : vector α n), (vector.of_fn v.nth') = v
| 0     v := by rw vector.eq_nil v; refl
| (n+1) v := by simp [vector.of_fn]; rw [@vector.of_fn_nth' n v.tail, vector.cons_head_tail]

def vector.append_nth'_left {α m n} (v : vector α m) (w : vector α n) (i) :
  ∀ iv {ivw}, (v.append w).nth' ⟨i, ivw⟩ = v.nth' ⟨i, iv⟩ :=
suffices ∀ (l₁ l₂ : list α) h h', list.nth_le (l₁ ++ l₂) i h' = list.nth_le l₁ i h,
by intros iv ivw; repeat {rw vector.nth'_eq_nth_le'};
   cases v; cases w; simp [vector.append]; dsimp; apply this,
begin
  intros v w, revert i,
  induction v with a v IH; intros i iv ivw; simp [vector.append],
  { exact absurd iv (nat.not_lt_zero _) },
  { dsimp, cases i; simp [list.nth_le], apply IH }
end

def vector.append_nth'_right {α m n} (v : vector α m) (w : vector α n) (i) :
  i ≥ m → ∀ iw {ivw}, (v.append w).nth' ⟨i, ivw⟩ = w.nth' ⟨i - v.length, iw⟩ :=
suffices ∀ (v w : list α) iw ivw,
  i ≥ v.length → list.nth_le (v ++ w) i ivw = list.nth_le w (i - v.length) iw,
by intros iv iw ivw; repeat {rw vector.nth'_eq_nth_le'}; cases v with v vh;
   cases w; simp [vector.append]; dsimp; cases vh; apply this _ _ _ _ iv,
begin
  intros v w, revert i,
  induction v with a v IH; intros i iw ivw iv; simp [vector.append],
  { refl },
  { dsimp, cases i with i; simp [list.nth_le, nat.zero_sub],
    { have h := nat.eq_zero_of_le_zero iv, contradiction },
    { apply IH, exact nat.le_of_succ_le_succ iv } }
end

def vector.nth'_map {α β n} (v : vector α n) (f : α → β) :
  ∀ i, (v.map f).nth' i = f (v.nth' i) :=
begin
  refine @vector.elim _
    (λn v, ∀ (i : fin n), vector.nth' (vector.map f v) i = f (vector.nth' v i))
    (λl i, _) _ v,
  dsimp [vector.map],
  induction l with a l IH,
  { exact i.elim0 },
  { cases i with i; cases i with i h; simp [vector.nth', vector.head, vector.tail],
    assertv IH : ∀ i h', vector.nth' ⟨list.map f l, h'⟩ i = f (vector.nth' ⟨l, rfl⟩ i) := λi h, IH i,
    rw IH, refl }
end-/

def arity (α β : Type u) (n : nat) : Type u :=
nat.rec β (λn T, α → T) n

def curry (α β) : Π {n}, (vector3 α n → β) → arity α β n
| 0 f     := f []
| (succ n) f := λx, curry (λv, f (x :: v))

def uncurry {α β} : Π (n), arity α β n → vector3 α n → β
| 0        f v := f
| (succ n) f v := v.cons_elim $ λa t, uncurry n (f a) t

-- "Curried" exists and forall, i.e. ∃ x1 ... xn, f [x1, ..., xn]
def vector_ex {α} : Π k, (vector3 α k → Prop) → Prop
| 0        f := f []
| (succ k) f := ∃x : α, vector_ex k (λv, f (x :: v))

def vector_all {α} : Π k, (vector3 α k → Prop) → Prop
| 0        f := f []
| (succ k) f := ∀x : α, vector_all k (λv, f (x :: v))

theorem exists_vector_zero {α} (f : vector3 α 0 → Prop) : Exists f ↔ f [] :=
⟨λ⟨v, fv⟩, by rw ← (eq_nil v); exact fv, λf0, ⟨[], f0⟩⟩

theorem exists_vector_succ {α n} (f : vector3 α (succ n) → Prop) : Exists f ↔ ∃x v, f (x :: v) :=
⟨λ⟨v, fv⟩, ⟨_, _, by rw cons_head_tail v; exact fv⟩, λ⟨x, v, fxv⟩, ⟨_, fxv⟩⟩

theorem vector_ex_iff_exists {α} : ∀ {n} (f : vector3 α n → Prop), vector_ex n f ↔ Exists f
| 0        f := (exists_vector_zero f).symm
| (succ n) f := iff.trans (exists_congr (λx, vector_ex_iff_exists _)) (exists_vector_succ f).symm

theorem vector_all_iff_forall {α} : ∀ {n} (f : vector3 α n → Prop), vector_all n f ↔ ∀ v, f v
| 0        f := ⟨λf0 v, v.nil_elim f0, λal, al []⟩
| (succ n) f := (forall_congr (λx, vector_all_iff_forall (λv, f (x :: v)))).trans
  ⟨λal v, v.cons_elim al, λal x v, al (x::v)⟩

def vector_allp {α} (p : α → Prop) {n} (v : vector3 α n) : Prop :=
vector3.rec_on v true (λn a v IH, @vector3.rec_on _ (λn v, Prop) _ v (p a) (λn b v' _, p a ∧ IH))

@[simp] theorem vector_allp_nil {α} (p : α → Prop) : vector_allp p [] = true := rfl
@[simp] theorem vector_allp_singleton {α} (p : α → Prop) (x : α) : vector_allp p [x] = p x := rfl
@[simp] theorem vector_allp_cons {α} (p : α → Prop) {n} (x : α) (v : vector3 α n) :
  vector_allp p (x :: v) ↔ p x ∧ vector_allp p v :=
vector3.rec_on v (and_true _).symm (λn a v IH, iff.rfl)

theorem vector_allp_iff_forall {α} (p : α → Prop) {n} (v : vector3 α n) : vector_allp p v ↔ ∀ i, p (v i) :=
begin refine v.rec_on _ _,
  { exact ⟨λ_, fin2.elim0, λ_, trivial⟩ },
  { simp, refine λn a v IH, (and_congr_right (λ_, IH)).trans
      ⟨λ⟨pa, h⟩ i, by {refine i.cases' _ _, exacts [pa, h]}, λh, ⟨_, λi, _⟩⟩,
    { have h0 := h fz, simp at h0, exact h0 },
    { have hs := h (fs i), simp at hs, exact hs } }
end

theorem vector_allp.imp {α} {p q : α → Prop} (h : ∀ x, p x → q x)
  {n} {v : vector3 α n} (al : vector_allp p v) : vector_allp q v :=
(vector_allp_iff_forall _ _).2 (λi, h _ $ (vector_allp_iff_forall _ _).1 al _)

def list_all {α} (p : α → Prop) : list α → Prop
| []        := true
| (x :: []) := p x
| (x :: l)  := p x ∧ list_all l
attribute [simp] list_all

@[simp] theorem list_all_cons {α} (p : α → Prop) (x : α) : ∀ (l : list α), list_all p (x :: l) ↔ p x ∧ list_all p l
| []       := (and_true _).symm
| (x :: l) := iff.rfl

theorem list_all_iff_forall {α} (p : α → Prop) : ∀ (l : list α), list_all p l ↔ ∀ x ∈ l, p x
| []       := (iff_true_intro $ list.ball_nil _).symm
| (x :: l) := by rw [list.ball_cons, ← list_all_iff_forall l]; simp

theorem list_all.imp {α} {p q : α → Prop} (h : ∀ x, p x → q x) : ∀ {l : list α}, list_all p l → list_all q l
| []       := id
| (x :: l) := by simpa using and.imp (h x) list_all.imp

@[simp] theorem list_all_map {α β} {p : β → Prop} (f : α → β) {l : list α} : list_all p (l.map f) ↔ list_all (p ∘ f) l :=
by induction l; simp *

theorem list_all_congr {α} {p q : α → Prop} (h : ∀ x, p x ↔ q x) {l : list α} : list_all p l ↔ list_all q l :=
⟨list_all.imp (λx, (h x).1), list_all.imp (λx, (h x).2)⟩

instance decidable_list_all {α} (p : α → Prop) [decidable_pred p] (l : list α) : decidable (list_all p l) :=
decidable_of_decidable_of_iff (by apply_instance) (list_all_iff_forall _ _).symm

/- poly -/

inductive is_poly {α} : ((α → ℕ) → ℤ) → Prop
| proj : ∀ i, is_poly (λx : α → ℕ, x i)
| const : Π (n : ℕ), is_poly (λx : α → ℕ, n)
| sub : Π {f g : (α → ℕ) → ℤ}, is_poly f → is_poly g → is_poly (λx, f x - g x)
| mul : Π {f g : (α → ℕ) → ℤ}, is_poly f → is_poly g → is_poly (λx, f x * g x)

def poly (α : Type u) := {f : (α → ℕ) → ℤ // is_poly f}

namespace poly
section
parameter {α : Type u}

def eval (f : poly α) : (α → ℕ) → ℤ := f.1

def isp (f : poly α) : is_poly (eval f) := f.2

def ext {f g : poly α} (e : ∀x, f.eval x = g.eval x) : f = g :=
subtype.eq (funext e)

def subst (f : poly α) (g : (α → ℕ) → ℤ) (e : ∀x, f.eval x = g x) : poly α :=
⟨g, by rw ← (funext e : f.eval = g); exact f.isp⟩
@[simp] theorem subst_eval (f g e x) : eval (subst f g e) x = g x := rfl

def proj (i) : poly α := ⟨_, is_poly.proj i⟩
@[simp] theorem proj_eval (i x) : eval (proj i) x = x i := rfl

def const (n) : poly α := ⟨_, is_poly.const n⟩
@[simp] theorem const_eval (n x) : eval (const n) x = n := rfl

def zero : poly α := const 0
instance : has_zero (poly α) := ⟨poly.zero⟩
@[simp] theorem zero_eval (x) : eval 0 x = 0 := rfl
@[simp] theorem zero_val : zero = 0 := rfl

def one : poly α := const 1
instance : has_one (poly α) := ⟨poly.one⟩
@[simp] theorem one_eval (x) : eval 1 x = 1 := rfl
@[simp] theorem one_val : one = 1 := rfl

def sub : poly α → poly α → poly α | ⟨f, pf⟩ ⟨g, pg⟩ :=
⟨_, is_poly.sub pf pg⟩
instance : has_sub (poly α) := ⟨poly.sub⟩
@[simp] theorem sub_eval : Π (f g x), eval (f - g) x = eval f x - eval g x
| ⟨f, pf⟩ ⟨g, pg⟩ x := rfl
@[simp] theorem sub_val (f g) : sub f g = f - g := rfl

def neg (f : poly α) : poly α := 0 - f
instance : has_neg (poly α) := ⟨poly.neg⟩
@[simp] theorem neg_eval (f x) : eval (-f) x = -eval f x :=
show eval (0-f) x = _, by simp
@[simp] theorem neg_val (f) : neg f = -f := rfl

def add : poly α → poly α → poly α | ⟨f, pf⟩ ⟨g, pg⟩ :=
subst (⟨f, pf⟩ - -⟨g, pg⟩) _
 (λx, show f x - (0 - g x) = f x + g x, by simp)
instance : has_add (poly α) := ⟨poly.add⟩
@[simp] theorem add_eval : Π (f g x), eval (f + g) x = eval f x + eval g x
| ⟨f, pf⟩ ⟨g, pg⟩ x := rfl
@[simp] theorem add_val (f g) : add f g = f + g := rfl

def mul : poly α → poly α → poly α | ⟨f, pf⟩ ⟨g, pg⟩ :=
⟨_, is_poly.mul pf pg⟩
instance : has_mul (poly α) := ⟨poly.mul⟩
@[simp] theorem mul_eval : Π (f g x), eval (f * g) x = eval f x * eval g x
| ⟨f, pf⟩ ⟨g, pg⟩ x := rfl
@[simp] theorem mul_val (f g) : mul f g = f * g := rfl

instance : comm_ring (poly α) := by refine
{ add            := add,
  add_assoc      := _,
  zero           := zero,
  zero_add       := _,
  add_zero       := _,
  neg            := neg,
  add_left_neg   := _,
  add_comm       := _,
  mul            := mul,
  mul_assoc      := _,
  one            := one,
  one_mul        := _,
  mul_one        := _,
  left_distrib   := _,
  right_distrib  := _,
  mul_comm       := _}; {intros, exact ext (λx, by simp [left_distrib])}

def induction {C : poly α → Prop}
  (H1 : ∀i, C (proj i)) (H2 : ∀n, C (const n))
  (H3 : ∀f g, C f → C g → C (f - g))
  (H4 : ∀f g, C f → C g → C (f * g)) (f : poly α) : C f :=
begin
  cases f with f pf,
  induction pf with i n f g pf pg ihf ihg f g pf pg ihf ihg,
  apply H1, apply H2, apply H3 _ _ ihf ihg, apply H4 _ _ ihf ihg
end

def pow (f : poly α) : ℕ → poly α
| 0     := 1
| (n+1) := pow n * f

def sumsq : list (poly α) → poly α
| []      := 0
| (p::ps) := p*p + sumsq ps

theorem sumsq_nonneg (x) : ∀ l, 0 ≤ (sumsq l).eval x
| []      := le_refl 0
| (p::ps) := by simp [sumsq, -add_comm];
                exact add_nonneg (mul_self_nonneg _) (sumsq_nonneg ps)

theorem sumsq_eq_zero (x) : ∀ l, (sumsq l).eval x = 0 ↔ list_all (λa, poly.eval a x = 0) l
| []      := eq_self_iff_true _
| (p::ps) := by rw [list_all_cons, ← sumsq_eq_zero ps]; simp [sumsq, -add_comm]; exact
  ⟨λ(h : eval p x * eval p x + eval (sumsq ps) x = 0),
   have eval p x = 0, from eq_zero_of_mul_self_eq_zero $ le_antisymm
     (by rw ← h; have t := add_le_add_left (sumsq_nonneg x ps) (eval p x * eval p x); rwa [add_zero] at t)
     (mul_self_nonneg _),
   ⟨this, by simp [this] at h; exact h⟩,
  λ⟨h1, h2⟩, by rw [h1, h2]; refl⟩

end

def remap {α β} (f : α → β) (g : poly α) : poly β :=
⟨λv, g.eval $ v ∘ f, g.induction
  (λi, by simp; apply is_poly.proj)
  (λn, by simp; apply is_poly.const)
  (λf g pf pg, by simp; apply is_poly.sub pf pg)
  (λf g pf pg, by simp; apply is_poly.mul pf pg)⟩
@[simp] theorem remap_eval {α β} (f : α → β) (g : poly α) (v) :
  eval (remap f g) v = eval g (v ∘ f) := rfl

/-
def insert_poly {n} (f : poly (succ n)) (i : fin2 (succ n)) : poly (succ n) :=
subst (f.remap $ insert_perm i)
  (λv, f.eval $ v.cons_elim $ λa t, insert a t i)
  (λv, v.cons_elim $ λa t,
    rfl /-suffices (λj, nth (insert_perm i j) (a :: t)) = _,
      by dsimp [cons_elim, eval, remap]; rw [this, -(of_fn_nth (insert a t i))],
    funext $ λj, by rw insert_perm_nth-/)
-/
/-
def remap {m n} (f : fin2 m → fin2 n) (g : poly m) : poly n :=
⟨λv, g.eval $ vector3.of_fn $ λi, v.nth' $ f i, g.induction
  (λi, by simp; apply is_poly.proj)
  (λn, by simp; apply is_poly.const)
  (λf g pf pg, by simp; apply is_poly.sub pf pg)
  (λf g pf pg, by simp; apply is_poly.mul pf pg)⟩

def ndrop {n} (f : poly (n+1)) (i : fin (n+1)) : poly (n+1) :=
subst (f.remap $ λj, nat.cases_on j.1 i (λj', if j' < i.1 then j' else j'+1))
  (λv, f.eval $ v.nth' i :: v.drop i) $ λv, congr_arg f.eval $
suffices ∀k, v.nth' i :: v.drop i, from
show vector3.of_fn
    (λ (i_1 : fin (n + 1)),
       vector3.nth' v ((λ (j : fin (n + 1)), ite (j < i) (j + 1) (ite (j = i) 0 j)) i_1)) = v.nth'
    i :: v.drop i, from _, _
-/
end poly

namespace sum
  def join {α β γ} (f : α → γ) (g : β → γ) : α ⊕ β → γ :=
  by {refine sum.rec _ _, exacts [f, g]} 

  infixr ` ⊗ `:65 := join
end sum

open sum

namespace option
  def cons {α β} (a : β) (v : α → β) : option α → β :=
  by {refine option.rec _ _, exacts [a, v]}

  notation a :: b := cons a b

  @[simp] def cons_head_tail {α β} (v : option α → β) : v none :: v ∘ some = v :=
  funext $ λo, by cases o; refl
end option

/- dioph -/

def dioph {α : Type u} (S : set (α → ℕ)) : Prop :=
∃ {β : Type u} (p : poly (α ⊕ β)), ∀ (v : α → ℕ), S v ↔ ∃t, p.eval (v ⊗ t) = 0

namespace dioph
section
  variables {α β γ : Type u}

  theorem ext {S S' : set (α → ℕ)} (d : dioph S) (H : ∀v, S v ↔ S' v) : dioph S' :=
  eq.rec d $ show S = S', from set.ext H

  theorem of_no_dummies (S : set (α → ℕ)) (p : poly α) (h : ∀ (v : α → ℕ), S v ↔ p.eval v = 0) : dioph S :=
  ⟨ulift empty, p.remap inl, λv, (h v).trans
    ⟨λh, ⟨λt, empty.rec _ t.down, by simp; rw [
      show (v ⊗ λt:ulift empty, empty.rec _ t.down) ∘ inl = v, from rfl, h]⟩,
    λ⟨t, ht⟩, by simp at ht; rwa [show (v ⊗ t) ∘ inl = v, from rfl] at ht⟩⟩

  lemma inject_dummies_lem (f : β → γ) (g : γ → option β) (inv : ∀ x, g (f x) = some x)
    (p : poly (α ⊕ β)) (v : α → ℕ) : (∃t, p.eval (v ⊗ t) = 0) ↔
      (∃t, (p.remap (inl ⊗ (inr ∘ f))).eval (v ⊗ t) = 0) :=
  begin
    simp, refine ⟨λt, _, λt, _⟩; cases t with t ht,
    { have : (v ⊗ (0 :: t) ∘ g) ∘ (inl ⊗ inr ∘ f) = v ⊗ t :=
      funext (λs, by cases s with a b; dsimp [join, (∘)]; try {rw inv}; refl),
      exact ⟨(0 :: t) ∘ g, by rwa this⟩ },
    { have : v ⊗ t ∘ f = (v ⊗ t) ∘ (inl ⊗ inr ∘ f) :=
      funext (λs, by cases s with a b; refl),
      exact ⟨t ∘ f, by rwa this⟩ }
  end

  theorem inject_dummies {S : set (α → ℕ)} (f : β → γ) (g : γ → option β) (inv : ∀ x, g (f x) = some x)
    (p : poly (α ⊕ β)) (h : ∀ (v : α → ℕ), S v ↔ ∃t, p.eval (v ⊗ t) = 0) :
    ∃ q : poly (α ⊕ γ), ∀ (v : α → ℕ), S v ↔ ∃t, q.eval (v ⊗ t) = 0 :=
  ⟨p.remap (inl ⊗ (inr ∘ f)), λv, (h v).trans $ inject_dummies_lem f g inv _ _⟩

  theorem reindex_dioph {S : set (α → ℕ)} : Π (d : dioph S) (f : α → β), dioph (λv, S (v ∘ f))
  | ⟨γ, p, pe⟩ f := ⟨γ, p.remap ((inl ∘ f) ⊗ inr), λv, (pe _).trans $ exists_congr $ λt,
    suffices v ∘ f ⊗ t = (v ⊗ t) ∘ (inl ∘ f ⊗ inr), by simp [this],
    funext $ λs, by cases s with a b; refl⟩

/-
  theorem exists_poly_ge {S : set (α → ℕ)} {β} (p : poly (α ⊕ β))
    (h : ∀ (v : α → ℕ), v ∈ S ↔ ∃t, p.eval (v ⊗ t) = 0) (k') (hk : k' ≥ k) :
    ∃ (p' : poly (n + k')), ∀ (v : α → ℕ), v ∈ S ↔ ∃t, p'.eval (t +-+ v) = 0 :=
  begin
    rw ← (nat.add_sub_of_le hk),
    generalize (k' - k) m, intro m, induction m with m IH,
    { exact ⟨p, h⟩ },
    cases IH with p h,
    refine ⟨p.remap fs, λv, (h v).trans ⟨λt, _, λt, _⟩⟩; cases t with t ht,
    { exact ⟨0::t, by simp [nth, of_fn, ht]⟩ },
    { revert ht, exact t.cons_elim (λa t ht, ⟨t, by simp [nth, of_fn] at ht; exact ht⟩) }
  end
-/

/-
  theorem exists_poly_list (l : list (set (α → ℕ))) (dl : list_all dioph l) :
    ∃ k, list_all (λ S, ∃ (p : poly (n + k)), ∀ (v : α → ℕ), v ∈ S ↔ ∃t, p.eval (t +-+ v) = 0) l :=
  suffices ∃ k, ∀ k' ≥ k, list_all (λ S, ∃ (p : poly (n + k')), ∀ (v : α → ℕ), v ∈ S ↔ ∃t, p.eval (t +-+ v) = 0) l,
    by refine exists_imp_exists (λk al, _) this; exact al k (le_refl _),
  by { induction l with S l IH, exact ⟨0, λk' _, trivial⟩, exact
       let ⟨⟨k₁, p, pe⟩, dl⟩ := (list_all_cons _ _ _).1 dl, ⟨k₂, al⟩ := IH dl in
       ⟨max k₁ k₂, λk' hk', (list_all_cons _ _ _).2
         ⟨exists_poly_ge p pe _ (le_trans (le_max_left _ _) hk'), al _ (le_trans (le_max_right _ _) hk')⟩⟩ }
-/
/-
  theorem dioph_of_list_poly (n k : ℕ) (l : list (poly (n + k))) (S : set (vector3 ℕ n))
    (h : vector_all n (λv : vector3 ℕ n, v ∈ S ↔ vector_ex k
      (λt, list_all (λp : poly (n + k), p.eval (t +-+ v) = 0) l))) : dioph S :=
  ⟨k, poly.sumsq l, λv, ((vector_all_iff_forall _).1 h v).trans $
    (vector_ex_iff_exists _).trans $ exists_congr $ λt, (poly.sumsq_eq_zero _ _).symm⟩
-/
--set_option pp.notation false set_option pp.implicit true
  theorem dioph_list_all (l) (d : list_all dioph l) : dioph (λv, list_all (λS : set (α → ℕ), S v) l) :=
  suffices ∃ β (pl : list (poly (α ⊕ β))), ∀ v, list_all (λS : set _, S v) l ↔ ∃t, list_all (λp, poly.eval p (v ⊗ t) = 0) pl,
    from let ⟨β, pl, h⟩ := this in ⟨β, poly.sumsq pl, λv, (h v).trans $ exists_congr $ λt, (poly.sumsq_eq_zero _ _).symm⟩,
  begin
    induction l with S l IH,
    exact ⟨ulift empty, [], λv, by simp; exact ⟨λ⟨t⟩, empty.rec _ t, trivial⟩⟩,
    simp at d,
    exact let ⟨⟨β, p, pe⟩, dl⟩ := d, ⟨γ, pl, ple⟩ := IH dl in
    ⟨β ⊕ γ, p.remap (inl ⊗ inr ∘ inl) :: pl.map (λq, q.remap (inl ⊗ (inr ∘ inr))), λv,
      by simp; exact iff.trans (and_congr (pe v) (ple v))
      ⟨λ⟨⟨m, hm⟩, ⟨n, hn⟩⟩,
        ⟨m ⊗ n, by rw [
          show (v ⊗ m ⊗ n) ∘ (inl ⊗ inr ∘ inl) = v ⊗ m,
          from funext $ λs, by cases s with a b; refl]; exact hm,
        by { refine list_all.imp (λq hq, _) hn, dsimp [(∘)],
             rw [show (λ (x : α ⊕ γ), (v ⊗ m ⊗ n) ((inl ⊗ λ (x : γ), inr (inr x)) x)) = v ⊗ n,
                 from funext $ λs, by cases s with a b; refl]; exact hq }⟩,
      λ⟨t, hl, hr⟩,
        ⟨⟨t ∘ inl, by rwa [
          show (v ⊗ t) ∘ (inl ⊗ inr ∘ inl) = v ⊗ t ∘ inl,
          from funext $ λs, by cases s with a b; refl] at hl⟩,
        ⟨t ∘ inr, by {
          refine list_all.imp (λq hq, _) hr, dsimp [(∘)] at hq,
          rwa [show (λ (x : α ⊕ γ), (v ⊗ t) ((inl ⊗ λ (x : γ), inr (inr x)) x)) = v ⊗ t ∘ inr,
               from funext $ λs, by cases s with a b; refl] at hq }⟩⟩⟩⟩
  end

  theorem and_dioph {S S' : set (α → ℕ)} (d : dioph S) (d' : dioph S') : dioph (λv, S v ∧ S' v) :=
  dioph_list_all [S, S'] ⟨d, d'⟩

  theorem or_dioph {S S' : set (α → ℕ)} : ∀ (d : dioph S) (d' : dioph S'), dioph (λv, S v ∨ S' v)
  | ⟨β, p, pe⟩ ⟨γ, q, qe⟩ := ⟨β ⊕ γ, p.remap (inl ⊗ inr ∘ inl) * q.remap (inl ⊗ inr ∘ inr), λv,
    begin
      refine iff.trans (or_congr ((pe v).trans _) ((qe v).trans _)) (exists_or_distrib.symm.trans (exists_congr $ λt,
       (@mul_eq_zero_iff_eq_zero_or_eq_zero _ _ (p.eval ((v ⊗ t) ∘ (inl ⊗ inr ∘ inl))) (q.eval ((v ⊗ t) ∘ (inl ⊗ inr ∘ inr)))).symm)),
      exact inject_dummies_lem _ (some ⊗ (λ_, none)) (λx, rfl) _ _,
      exact inject_dummies_lem _ ((λ_, none) ⊗ some) (λx, rfl) _ _,
    end⟩

  def dioph_pfun (f : (α → ℕ) →. ℕ) := dioph (λv : option α → ℕ, f.graph (v ∘ some, v none))

  def dioph_fn (f : (α → ℕ) → ℕ) := dioph (λv : option α → ℕ, f (v ∘ some) = v none)

  theorem reindex_dioph_fn {f : (α → ℕ) → ℕ} (d : dioph_fn f) (g : α → β) : dioph_fn (λv, f (v ∘ g)) :=
  reindex_dioph d (has_map.map g)

/-
  @[simp] theorem eproj_fz (S : set (vector3 ℕ (succ n))) : eproj S fz = eproj1 S :=
  set.ext $ λv, exists_congr $ λx, by rw insert_fz

  def eproj_dioph {n} {S : set (vector3 ℕ (succ n))} (d : dioph S) (i : fin2 (succ n)) : dioph (eproj S i) :=
  let ⟨k, p, pe⟩ := d, E := succ_add n k, p' : poly (succ (n + k)) := E.rec_on p in
  by refine ⟨succ k, p'.insert_poly (E.rec_on $ add i k), λv, (exists_congr $ λx, _).trans (exists_vector_succ _).symm⟩; exact
  show insert x v i ∈ S ↔ ∃ (t : vector3 ℕ k), (E.rec_on p).eval (insert x (t +-+ v) (E.rec_on $ add i k)) = 0, from
  (pe _).trans $ exists_congr $ λt, by rw append_insert; exact match succ (n + k), E with ._, rfl := iff.rfl end
-/

  theorem ex_dioph {S : set (α ⊕ β → ℕ)} : dioph S → dioph (λv, ∃x, S (v ⊗ x))
  | ⟨γ, p, pe⟩ := ⟨β ⊕ γ, p.remap ((inl ⊗ inr ∘ inl) ⊗ inr ∘ inr), λv,
    ⟨λ⟨x, hx⟩, let ⟨t, ht⟩ := (pe _).1 hx in ⟨x ⊗ t, by simp; rw [
      show (v ⊗ x ⊗ t) ∘ ((inl ⊗ inr ∘ inl) ⊗ inr ∘ inr) = (v ⊗ x) ⊗ t,
      from funext $ λs, by cases s with a b; try {cases a}; refl]; exact ht⟩,
    λ⟨t, ht⟩, ⟨t ∘ inl, (pe _).2 ⟨t ∘ inr, by simp at ht; rwa [
      show (v ⊗ t) ∘ ((inl ⊗ inr ∘ inl) ⊗ inr ∘ inr) = (v ⊗ t ∘ inl) ⊗ t ∘ inr,
      from funext $ λs, by cases s with a b; try {cases a}; refl] at ht⟩⟩⟩⟩

  theorem ex1_dioph {S : set (option α → ℕ)} : dioph S → dioph (λv, ∃x, S (x :: v))
  | ⟨β, p, pe⟩ := ⟨option β, p.remap (inr none :: inl ⊗ inr ∘ some), λv,
    ⟨λ⟨x, hx⟩, let ⟨t, ht⟩ := (pe _).1 hx in ⟨x :: t, by simp; rw [
      show (v ⊗ x :: t) ∘ (inr none :: inl ⊗ inr ∘ some) = x :: v ⊗ t,
      from funext $ λs, by cases s with a b; try {cases a}; refl]; exact ht⟩,
    λ⟨t, ht⟩, ⟨t none, (pe _).2 ⟨t ∘ some, by simp at ht; rwa [
      show (v ⊗ t) ∘ (inr none :: inl ⊗ inr ∘ some) = t none :: v ⊗ t ∘ some,
      from funext $ λs, by cases s with a b; try {cases a}; refl] at ht⟩⟩⟩⟩

  theorem dom_dioph {f : (α → ℕ) →. ℕ} (d : dioph_pfun f) : dioph f.dom :=
  cast (congr_arg dioph $ set.ext $ λv, (pfun.dom_iff_graph _ _).symm) (ex1_dioph d)

  theorem dioph_fn_iff_pfun (f : (α → ℕ) → ℕ) : dioph_fn f = @dioph_pfun α f :=
  by refine congr_arg dioph (set.ext $ λv, _); exact pfun.lift_graph.symm

  theorem abs_poly_dioph (p : poly α) : dioph_fn (λv, (p.eval v).nat_abs) :=
  by refine of_no_dummies _ ((p.remap some - poly.proj none) * (p.remap some + poly.proj none)) (λv, _);
     apply int.eq_nat_abs_iff_mul

  theorem proj_dioph (i : α) : dioph_fn (λv, v i) :=
  abs_poly_dioph (poly.proj i)

  theorem dioph_pfun_comp1 {S : set (option α → ℕ)} (d : dioph S) {f} (df : dioph_pfun f) :
    dioph (λv : α → ℕ, ∃ h : f.dom v, S (f.fn v h :: v)) :=
  ext (ex1_dioph (and_dioph d df)) $ λv,
  ⟨λ⟨x, hS, (h: Exists _)⟩, by
    rw [show (x :: v) ∘ some = v, from funext $ λs, rfl] at h;
    cases h with hf h; refine ⟨hf, _⟩; rw [pfun.fn, h]; exact hS,
  λ⟨x, hS⟩, ⟨f.fn v x, hS, show Exists _,
    by rw [show (f.fn v x :: v) ∘ some = v, from funext $ λs, rfl]; exact ⟨x, rfl⟩⟩⟩

  theorem dioph_fn_comp1 {S : set (option α → ℕ)} (d : dioph S) {f : (α → ℕ) → ℕ} (df : dioph_fn f) :
    dioph (λv : α → ℕ, S (f v :: v)) :=
  ext (dioph_pfun_comp1 d (cast (dioph_fn_iff_pfun f) df)) $ λv,
  ⟨λ⟨_, h⟩, h, λh, ⟨trivial, h⟩⟩

end

section
  variables {α β γ : Type}

  theorem dioph_fn_vec_comp1 {n} {S : set (vector3 ℕ (succ n))} (d : dioph S) {f : (vector3 ℕ n) → ℕ} (df : dioph_fn f) :
    dioph (λv : vector3 ℕ n, S (cons (f v) v)) :=
  ext (dioph_fn_comp1 (reindex_dioph d (none :: some)) df) $ λv, by rw [
    show option.cons (f v) v ∘ (cons none some) = f v :: v,
    from funext $ λs, by cases s with a b; refl]
   
  theorem vec_ex1_dioph (n) {S : set (vector3 ℕ (succ n))} (d : dioph S) : dioph (λv : vector3 ℕ n, ∃x, S (x :: v)) :=
  ext (ex1_dioph $ reindex_dioph d (none :: some)) $ λv, exists_congr $ λx, by rw [
    show (option.cons x v) ∘ (cons none some) = x :: v,
    from funext $ λs, by cases s with a b; refl]

  theorem dioph_fn_vec {n} (f : vector3 ℕ n → ℕ) : dioph_fn f ↔ dioph (λv : vector3 ℕ (succ n), f (v ∘ fs) = v fz) :=
  ⟨λh, reindex_dioph h (fz :: fs), λh, reindex_dioph h (none :: some)⟩

  theorem dioph_pfun_vec {n} (f : vector3 ℕ n →. ℕ) : dioph_pfun f ↔ dioph (λv : vector3 ℕ (succ n), f.graph (v ∘ fs, v fz)) :=
  ⟨λh, reindex_dioph h (fz :: fs), λh, reindex_dioph h (none :: some)⟩

  theorem dioph_fn_compn {α : Type} : ∀ {n} {S : set (α ⊕ fin2 n → ℕ)} (d : dioph S) {f : vector3 ((α → ℕ) → ℕ) n} (df : vector_allp dioph_fn f),
    dioph (λv : α → ℕ, S (v ⊗ λi, f i v))
  | 0 S d f := λdf, ext (reindex_dioph d (id ⊗ fin2.elim0)) $ λv,
    by refine eq.to_iff (congr_arg S $ funext $ λs, _); {cases s with a b, refl, cases b}
  | (succ n) S d f := f.cons_elim $ λf fl, by simp; exact λ df dfl,
    have dioph (λv, S (v ∘ inl ⊗ f (v ∘ inl) :: v ∘ inr)),
    from ext (dioph_fn_comp1 (reindex_dioph d (some ∘ inl ⊗ none :: some ∘ inr)) (reindex_dioph_fn df inl)) $
      λv, by {refine eq.to_iff (congr_arg S $ funext $ λs, _); cases s with a b, refl, cases b; refl},
    have dioph (λv, S (v ⊗ f v :: λ (i : fin2 n), fl i v)),
    from @dioph_fn_compn n (λv, S (v ∘ inl ⊗ f (v ∘ inl) :: v ∘ inr)) this _ dfl,
    ext this $ λv, by rw [
      show cons (f v) (λ (i : fin2 n), fl i v) = λ (i : fin2 (succ n)), (f :: fl) i v,
      from funext $ λs, by cases s with a b; refl]

  theorem dioph_comp {n} {S : set (vector3 ℕ n)} (d : dioph S) 
    (f : vector3 ((α → ℕ) → ℕ) n) (df : vector_allp dioph_fn f) : dioph (λv, S (λi, f i v)) :=
  dioph_fn_compn (reindex_dioph d inr) df

  theorem dioph_fn_comp {n} {f : vector3 ℕ n → ℕ} (df : dioph_fn f) 
    (g : vector3 ((α → ℕ) → ℕ) n) (dg : vector_allp dioph_fn g) : dioph_fn (λv, f (λi, g i v)) :=
  dioph_comp ((dioph_fn_vec _).1 df) ((λv, v none) :: λi v, g i (v ∘ some)) $
  by simp; exact ⟨proj_dioph none, (vector_allp_iff_forall _ _).2 $ λi,
    reindex_dioph_fn ((vector_allp_iff_forall _ _).1 dg _) _⟩

  local notation x ` D∧ `:35 y := and_dioph x y
  local notation x ` D∨ `:35 y := or_dioph x y

  local notation `D∃`:30 := vec_ex1_dioph

  local prefix `&`:max := of_nat'
  @[reducible] def proj_dioph_of_nat {n : ℕ} (m : ℕ) [is_lt m n] : dioph_fn (λv : vector3 ℕ n, v &m) :=
  proj_dioph &m
  local prefix `D&`:100 := proj_dioph_of_nat

  theorem const_dioph (n : ℕ) : dioph_fn (const (α → ℕ) n) :=
  abs_poly_dioph (poly.const n)
  local prefix `D.`:100 := const_dioph

  variables {f g : (α → ℕ) → ℕ} (df : dioph_fn f) (dg : dioph_fn g)
  include df dg

  theorem dioph_comp2 {S : ℕ → ℕ → Prop} (d : dioph (λv:vector3 ℕ 2, S (v &0) (v &1))) :
    dioph (λv, S (f v) (g v)) :=
  dioph_comp d [f, g] (by exact ⟨df, dg⟩)

  theorem dioph_fn_comp2 {h : ℕ → ℕ → ℕ} (d : dioph_fn (λv:vector3 ℕ 2, h (v &0) (v &1))) :
    dioph_fn (λv, h (f v) (g v)) :=
  dioph_fn_comp d [f, g] (by exact ⟨df, dg⟩)

  theorem eq_dioph : dioph (λv, f v = g v) :=
  dioph_comp2 df dg $ of_no_dummies _ (poly.proj &0 - poly.proj &1)
    (λv, (int.coe_nat_eq_coe_nat_iff _ _).symm.trans
    ⟨@sub_eq_zero_of_eq ℤ _ (v &0) (v &1), eq_of_sub_eq_zero⟩)
  local infix ` D= `:50 := eq_dioph

  theorem add_dioph : dioph_fn (λv, f v + g v) :=
  dioph_fn_comp2 df dg $ abs_poly_dioph (poly.proj &0 + poly.proj &1)
  local infix ` D+ `:80 := add_dioph

  theorem mul_dioph : dioph_fn (λv, f v * g v) :=
  dioph_fn_comp2 df dg $ abs_poly_dioph (poly.proj &0 * poly.proj &1)
  local infix ` D* `:90 := mul_dioph

  theorem le_dioph : dioph (λv, f v ≤ g v) :=
  dioph_comp2 df dg $ ext (D∃2 $ D&1 D+ D&0 D= D&2) (λv, ⟨λ⟨x, hx⟩, le.intro hx, le.dest⟩)
  local infix ` D≤ `:50 := le_dioph

  theorem lt_dioph : dioph (λv, f v < g v) := df D+ (D. 1) D≤ dg
  local infix ` D< `:50 := lt_dioph

  theorem ne_dioph : dioph (λv, f v ≠ g v) :=
  ext (df D< dg D∨ dg D< df) $ λv, ne_iff_lt_or_gt.symm
  local infix ` D≠ `:50 := ne_dioph

  theorem sub_dioph : dioph_fn (λv, f v - g v) :=
  dioph_fn_comp2 df dg $ (dioph_fn_vec _).2 $
  ext (D&1 D= D&0 D+ D&2 D∨ D&1 D≤ D&2 D∧ D&0 D= D.0) $ (vector_all_iff_forall _).1 $ λx y z,
  show (y = x + z ∨ y ≤ z ∧ x = 0) ↔ y - z = x, from
  ⟨λo, by { cases o with ae h,
    rw [ae, nat.add_sub_cancel],
    cases h with yz x0,
    rw [x0, nat.sub_eq_zero_of_le yz]
  }, λh, by {
    rw ← h,
    cases le_total y z with yz zy,
    exact or.inr ⟨yz, nat.sub_eq_zero_of_le yz⟩,
    exact or.inl (nat.sub_add_cancel zy).symm,
  }⟩
  local infix ` D- `:80 := sub_dioph

  theorem dvd_dioph : dioph (λv, f v ∣ g v) :=
  dioph_comp (D∃2 $ D&2 D= D&1 D* D&0) [f, g] (by exact ⟨df, dg⟩)
  local infix ` D∣ `:50 := dvd_dioph

  theorem mod_dioph : dioph_fn (λv, f v % g v) :=
  have dioph (λv : vector3 ℕ 3, (v &2 = 0 ∨ v &0 < v &2) ∧ ∃ (x : ℕ), v &0 + v &2 * x = v &1),
  from (D&2 D= D.0 D∨ D&0 D< D&2) D∧ (D∃3 $ D&1 D+ D&3 D* D&0 D= D&2),
  dioph_fn_comp2 df dg $ (dioph_fn_vec _).2 $ ext this $ (vector_all_iff_forall _).1 $ λz x y,
  show ((y = 0 ∨ z < y) ∧ ∃ c, z + y * c = x) ↔ x % y = z, from
  ⟨λ⟨h, c, hc⟩, begin rw ← hc; simp; cases h with x0 hl, rw [x0, mod_zero], exact mod_eq_of_lt hl end,
  λe, by rw ← e; exact ⟨or_iff_not_imp_left.2 $ λh, mod_lt _ (nat.pos_of_ne_zero h), x / y, mod_add_div _ _⟩⟩
  local infix ` D% `:80 := mod_dioph

  theorem modeq_dioph {h : (α → ℕ) → ℕ} (dh : dioph_fn h) : dioph (λv, f v ≡ g v [MOD h v]) :=
  df D% dh D= dg D% dh
  local notation `D≡` := modeq_dioph

  theorem div_dioph : dioph_fn (λv, f v / g v) :=
  have dioph (λv : vector3 ℕ 3, v &2 = 0 ∧ v &0 = 0 ∨ v &0 * v &2 ≤ v &1 ∧ v &1 < (v &0 + 1) * v &2),
  from (D&2 D= D.0 D∧ D&0 D= D.0) D∨ D&0 D* D&2 D≤ D&1 D∧ D&1 D< (D&0 D+ D.1) D* D&2,
  dioph_fn_comp2 df dg $ (dioph_fn_vec _).2 $ ext this $ (vector_all_iff_forall _).1 $ λz x y,
  show y = 0 ∧ z = 0 ∨ z * y ≤ x ∧ x < (z + 1) * y ↔ x / y = z,
  by refine iff.trans _ eq_comm; exact y.eq_zero_or_pos.elim
    (λy0, by rw [y0, nat.div_zero]; exact
      ⟨λo, (o.resolve_right $ λ⟨_, h2⟩, not_lt_zero _ h2).right, λz0, or.inl ⟨rfl, z0⟩⟩)
    (λypos, iff.trans ⟨λo, o.resolve_left $ λ⟨h1, _⟩, ne_of_gt ypos h1, or.inr⟩
      (le_antisymm_iff.trans $ and_congr (nat.le_div_iff_mul_le _ _ ypos) $
        iff.trans ⟨lt_succ_of_le, le_of_lt_succ⟩ (div_lt_iff_lt_mul _ _ ypos)).symm)
  local infix ` D/ `:80 := div_dioph

  omit df dg
  open pell

  theorem pell_dioph : dioph (λv:vector3 ℕ 4, ∃ h : v &0 > 1,
    xn h (v &1) = v &2 ∧ yn h (v &1) = v &3) :=
  have dioph {v : vector3 ℕ 4 |
  v &0 > 1 ∧ v &1 ≤ v &3 ∧
  (v &2 = 1 ∧ v &3 = 0 ∨
  ∃ (u w s t b : ℕ),
    v &2 * v &2 - (v &0 * v &0 - 1) * v &3 * v &3 = 1 ∧
    u * u - (v &0 * v &0 - 1) * w * w = 1 ∧
    s * s - (b * b - 1) * t * t = 1 ∧
    b > 1 ∧ (b ≡ 1 [MOD 4 * v &3]) ∧ (b ≡ v &0 [MOD u]) ∧
    w > 0 ∧ v &3 * v &3 ∣ w ∧
    (s ≡ v &2 [MOD u]) ∧
    (t ≡ v &1 [MOD 4 * v &3]))}, from
  D.1 D< D&0 D∧ D&1 D≤ D&3 D∧
  ((D&2 D= D.1 D∧ D&3 D= D.0) D∨
   (D∃4 $ D∃5 $ D∃6 $ D∃7 $ D∃8 $
    D&7 D* D&7 D- (D&5 D* D&5 D- D.1) D* D&8 D* D&8 D= D.1 D∧
    D&4 D* D&4 D- (D&5 D* D&5 D- D.1) D* D&3 D* D&3 D= D.1 D∧
    D&2 D* D&2 D- (D&0 D* D&0 D- D.1) D* D&1 D* D&1 D= D.1 D∧
    D.1 D< D&0 D∧ (D≡ (D&0) (D.1) (D.4 D* D&8)) D∧ (D≡ (D&0) (D&5) D&4) D∧
    D.0 D< D&3 D∧ D&8 D* D&8 D∣ D&3 D∧
    (D≡ (D&2) (D&7) D&4) D∧
    (D≡ (D&1) (D&6) (D.4 D* D&8)))),
  dioph.ext this $ λv, matiyasevic.symm

  theorem xn_dioph : dioph_pfun (λv:vector3 ℕ 2, ⟨v &0 > 1, λh, xn h (v &1)⟩) :=
  have dioph (λv:vector3 ℕ 3, ∃ y, ∃ h : v &1 > 1, xn h (v &2) = v &0 ∧ yn h (v &2) = y), from
  let D_pell := @reindex_dioph _ (fin2 4) _ pell_dioph [&2, &3, &1, &0] in D∃3 D_pell,
  (dioph_pfun_vec _).2 $ dioph.ext this $ λv, ⟨λ⟨y, h, xe, ye⟩, ⟨h, xe⟩, λ⟨h, xe⟩, ⟨_, h, xe, rfl⟩⟩

  include df dg
  theorem pow_dioph : dioph_fn (λv, f v ^ g v) :=
  have dioph {v : vector3 ℕ 3 |
  v &2 = 0 ∧ v &0 = 1 ∨ v &2 > 0 ∧
  (v &1 = 0 ∧ v &0 = 0 ∨ v &1 > 0 ∧
  ∃ (w a t z x y : ℕ),
    (∃ (a1 : a > 1), xn a1 (v &2) = x ∧ yn a1 (v &2) = y) ∧
    (x ≡ y * (a - v &1) + v &0 [MOD t]) ∧
    2 * a * v &1 = t + (v &1 * v &1 + 1) ∧
    v &0 < t ∧ v &1 ≤ w ∧ v &2 ≤ w ∧
    a * a - ((w + 1) * (w + 1) - 1) * (w * z) * (w * z) = 1)}, from
  let D_pell := @reindex_dioph _ (fin2 9) _ pell_dioph [&4, &8, &1, &0] in
  (D&2 D= D.0 D∧ D&0 D= D.1) D∨ (D.0 D< D&2 D∧
  ((D&1 D= D.0 D∧ D&0 D= D.0) D∨ (D.0 D< D&1 D∧
   (D∃3 $ D∃4 $ D∃5 $ D∃6 $ D∃7 $ D∃8 $ D_pell D∧
    (D≡ (D&1) (D&0 D* (D&4 D- D&7) D+ D&6) (D&3)) D∧
    D.2 D* D&4 D* D&7 D= D&3 D+ (D&7 D* D&7 D+ D.1) D∧
    D&6 D< D&3 D∧ D&7 D≤ D&5 D∧ D&8 D≤ D&5 D∧
    D&4 D* D&4 D- ((D&5 D+ D.1) D* (D&5 D+ D.1) D- D.1) D* (D&5 D* D&2) D* (D&5 D* D&2) D= D.1)))),
  dioph_fn_comp2 df dg $ (dioph_fn_vec _).2 $ dioph.ext this $ λv, iff.symm $
  eq_pow_of_pell.trans $ or_congr iff.rfl $ and_congr iff.rfl $ or_congr iff.rfl $ and_congr iff.rfl $
  ⟨λ⟨w, a, t, z, a1, h⟩, ⟨w, a, t, z, _, _, ⟨a1, rfl, rfl⟩, h⟩,
   λ⟨w, a, t, z, ._, ._, ⟨a1, rfl, rfl⟩, h⟩, ⟨w, a, t, z, a1, h⟩⟩  

end
end dioph
