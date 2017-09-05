import data.stream data.lazy_list data.seq.computation logic.basic
universes u v w

/-
coinductive seq (α : Type u) : Type u
| nil : seq α
| cons : α → seq α → seq α
-/

def seq (α : Type u) : Type u := { f : stream (option α) // ∀ {n}, f n = none → f (n+1) = none }

def seq1 (α) := α × seq α

namespace seq
variables {α : Type u} {β : Type v} {γ : Type w}

def nil : seq α := ⟨stream.const none, λn h, rfl⟩

def cons (a : α) : seq α → seq α
| ⟨f, al⟩ := ⟨some a :: f, λn h, by {cases n with n, contradiction, exact al h}⟩

def nth : seq α → ℕ → option α := subtype.val

def omap (f : β → γ) : option (α × β) → option (α × γ)
| none          := none
| (some (a, b)) := some (a, f b)
attribute [simp] omap

def head (s : seq α) : option α := nth s 0

def tail : seq α → seq α
| ⟨f, al⟩ := ⟨f.tail, λ n, al⟩

protected def mem (a : α) (s : seq α) := some a ∈ s.1

instance : has_mem α (seq α) :=
⟨seq.mem⟩

theorem le_stable (s : seq α) {m n} (h : m ≤ n) :
  s.1 m = none → s.1 n = none :=
by {cases s with f al, induction h with n h IH, exacts [id, λ h2, al (IH h2)]}

theorem not_mem_nil (a : α) : a ∉ @nil α :=
λ ⟨n, (h : some a = none)⟩, by injection h

theorem mem_cons (a : α) : ∀ (s : seq α), a ∈ cons a s
| ⟨f, al⟩ := stream.mem_cons (some a) _

theorem mem_cons_of_mem (y : α) {a : α} : ∀ {s : seq α}, a ∈ s → a ∈ cons y s
| ⟨f, al⟩ := stream.mem_cons_of_mem (some y)

theorem eq_or_mem_of_mem_cons {a b : α} : ∀ {s : seq α}, a ∈ cons b s → a = b ∨ a ∈ s
| ⟨f, al⟩ h := (stream.eq_or_mem_of_mem_cons h).imp_left (λh, by injection h)

@[simp] theorem mem_cons_iff {a b : α} {s : seq α} : a ∈ cons b s ↔ a = b ∨ a ∈ s :=
⟨eq_or_mem_of_mem_cons, λo, by cases o with e m;
  [{rw e, apply mem_cons}, exact mem_cons_of_mem _ m]⟩

def destruct (s : seq α) : option (seq1 α) :=
(λa', (a', s.tail)) <$> nth s 0

theorem destruct_eq_nil {s : seq α} : destruct s = none → s = nil :=
begin
  dsimp [destruct],
  ginduction nth s 0 with f0; intro h,
  { apply subtype.eq, apply funext,
    dsimp [nil], intro n,
    induction n with n IH, exacts [f0, s.2 IH] },
  { contradiction }
end

theorem destruct_eq_cons {s : seq α} {a s'} : destruct s = some (a, s') → s = cons a s' :=
begin
  dsimp [destruct],
  ginduction nth s 0 with f0 a'; intro h,
  { contradiction },
  { unfold has_map.map at h, dsimp [option.map, option.bind] at h,
    cases s with f al,
    injections with _ h1 h2,
    rw ←h2, apply subtype.eq, dsimp [tail, cons],
    rw h1 at f0, rw ←f0,
    exact (stream.eta f).symm }
end

@[simp] theorem destruct_nil : destruct (nil : seq α) = none := rfl

@[simp] theorem destruct_cons (a : α) : ∀ s, destruct (cons a s) = some (a, s)
| ⟨f, al⟩ := begin
  unfold cons destruct has_map.map,
  apply congr_arg (λ s, some (a, s)),
  apply subtype.eq, dsimp [tail], rw [stream.tail_cons]
end

theorem head_eq_destruct (s : seq α) : head s = prod.fst <$> destruct s :=
by unfold destruct head; cases nth s 0; refl

@[simp] theorem head_nil : head (nil : seq α) = none := rfl

@[simp] theorem head_cons (a : α) (s) : head (cons a s) = some a :=
by rw [head_eq_destruct, destruct_cons]; refl

@[simp] theorem tail_nil : tail (nil : seq α) = nil := rfl

@[simp] theorem tail_cons (a : α) (s) : tail (cons a s) = s :=
by cases s with f al; apply subtype.eq; dsimp [tail, cons]; rw [stream.tail_cons]

def cases_on {C : seq α → Sort v} (s : seq α)
  (h1 : C nil) (h2 : ∀ x s, C (cons x s)) : C s := begin
  ginduction destruct s with H,
  { rw destruct_eq_nil H, apply h1 },
  { cases a with a s', rw destruct_eq_cons H, apply h2 }
end

theorem mem_rec_on {C : seq α → Prop} {a s} (M : a ∈ s)
  (h1 : ∀ b s', (a = b ∨ C s') → C (cons b s')) : C s :=
begin
  cases M with k e, unfold stream.nth at e,
  induction k with k IH generalizing s,
  { have TH : s = cons a (tail s),
    { apply destruct_eq_cons,
      unfold destruct nth has_map.map, rw ←e, refl },
    rw TH, apply h1 _ _ (or.inl rfl) },
  revert e, apply s.cases_on _ (λ b s', _); intro e,
  { injection e },
  { rw [show (cons b s').val (nat.succ k) = s'.val k, by cases s'; refl] at e,
    apply h1 _ _ (or.inr (IH e)) }
end

def corec.F (f : β → option (α × β)) : option β → option α × option β
| none     := (none, none)
| (some b) := match f b with none := (none, none) | some (a, b') := (some a, some b') end

def corec (f : β → option (α × β)) (b : β) : seq α :=
begin
  refine ⟨stream.corec' (corec.F f) (some b), λn h, _⟩,
  rw stream.corec'_eq,
  change stream.corec' (corec.F f) (corec.F f (some b)).2 n = none,
  revert h, generalize : some b = o, revert o,
  induction n with n IH; intro o,
  { change (corec.F f o).1 = none → (corec.F f (corec.F f o).2).1 = none,
    cases o with b; intro h, { refl },
    dsimp [corec.F] at h, dsimp [corec.F],
    cases f b with s, { refl },
    { cases s with a b', contradiction } },
  { rw [stream.corec'_eq (corec.F f) (corec.F f o).2,
        stream.corec'_eq (corec.F f) o],
    exact IH (corec.F f o).2 }
end

@[simp] def corec_eq (f : β → option (α × β)) (b : β) :
  destruct (corec f b) = omap (corec f) (f b) :=
begin
  dsimp [corec, destruct, nth],
  change stream.corec' (corec.F f) (some b) 0 with (corec.F f (some b)).1,
  unfold has_map.map, dsimp [corec.F],
  ginduction f b with h s, { refl },
  cases s with a b', dsimp [corec.F, option.bind],
  apply congr_arg (λ b', some (a, b')),
  apply subtype.eq,
  dsimp [corec, tail],
  rw [stream.corec'_eq, stream.tail_cons],
  dsimp [corec.F], rw h, refl
end

def of_list (l : list α) : seq α :=
⟨list.nth l, λn h, begin
  induction l with a l IH generalizing n, refl,
  dsimp [list.nth], cases n with n; dsimp [list.nth] at h,
  { contradiction },
  { apply IH _ h }
end⟩

instance coe_list : has_coe (list α) (seq α) := ⟨of_list⟩

section bisim
  variable (R : seq α → seq α → Prop)

  local infix ~ := R

  def bisim_o : option (seq1 α) → option (seq1 α) → Prop
  | none          none            := true
  | (some (a, s)) (some (a', s')) := a = a' ∧ R s s'
  | _             _               := false
  attribute [simp] bisim_o

  def is_bisimulation := ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ → bisim_o R (destruct s₁) (destruct s₂)

  -- If two streams are bisimilar, then they are equal
  theorem eq_of_bisim (bisim : is_bisimulation R) {s₁ s₂} (r : s₁ ~ s₂) : s₁ = s₂ :=
  begin
    apply subtype.eq,
    apply stream.eq_of_bisim (λx y, ∃ s s' : seq α, s.1 = x ∧ s'.1 = y ∧ R s s'),
    dsimp [stream.is_bisimulation],
    intros t₁ t₂ e,
    exact match t₁, t₂, e with ._, ._, ⟨s, s', rfl, rfl, r⟩ :=
      suffices head s = head s' ∧ R (tail s) (tail s'), from
      and.imp id (λr, ⟨tail s, tail s',
        by cases s; refl, by cases s'; refl, r⟩) this,
      begin
        have := bisim r, revert r this,
        apply cases_on s _ _; intros; apply cases_on s' _ _; intros; intros r this,
        { constructor, refl, assumption },
        { rw [destruct_nil, destruct_cons] at this,
          exact false.elim this },
        { rw [destruct_nil, destruct_cons] at this,
          exact false.elim this },
        { rw [destruct_cons, destruct_cons] at this,
          rw [head_cons, head_cons, tail_cons, tail_cons],
          cases this with h1 h2,
          constructor, rw h1, exact h2 }
      end
    end,
    exact ⟨s₁, s₂, rfl, rfl, r⟩
  end
end bisim

theorem coinduction : ∀ {s₁ s₂ : seq α}, head s₁ = head s₂ →
  (∀ (β : Type u) (fr : seq α → β),
    fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂)) → s₁ = s₂
| ⟨f₁, a₁⟩ ⟨f₂, a₂⟩ hh ht :=
  subtype.eq (stream.coinduction hh (λ β fr, ht β (λs, fr s.1)))

theorem coinduction2 (s) (f g : seq α → seq β)
  (H : ∀ s, bisim_o (λ (s1 s2 : seq β), ∃ (s : seq α), s1 = f s ∧ s2 = g s)
    (destruct (f s)) (destruct (g s)))
  : f s = g s :=
begin
  refine eq_of_bisim (λ s1 s2, ∃ s, s1 = f s ∧ s2 = g s) _ ⟨s, rfl, rfl⟩,
  intros s1 s2 h, cases h with s h, cases h with h1 h2,
  rw [h1, h2], apply H
end

def of_stream (s : stream α) : seq α :=
⟨s.map some, λn h, by contradiction⟩

instance coe_stream : has_coe (stream α) (seq α) := ⟨of_stream⟩

def of_lazy_list : lazy_list α → seq α :=
corec (λl, match l with
  | lazy_list.nil := none
  | lazy_list.cons a l' := some (a, l' ())
  end)

instance coe_lazy_list : has_coe (lazy_list α) (seq α) := ⟨of_lazy_list⟩

meta def to_lazy_list : seq α → lazy_list α | s :=
match destruct s with
| none := lazy_list.nil
| some (a, s') := lazy_list.cons a (to_lazy_list s')
end

meta def force_to_list (s : seq α) : list α := (to_lazy_list s).to_list

def append (s₁ s₂ : seq α) : seq α :=
@corec α (seq α × seq α) (λ⟨s₁, s₂⟩,
  match destruct s₁ with
  | none := omap (λs₂, (nil, s₂)) (destruct s₂)
  | some (a, s₁') := some (a, s₁', s₂)
  end) (s₁, s₂)

def map (f : α → β) : seq α → seq β | ⟨s, al⟩ :=
⟨s.map (option.map f),
λn, begin
  dsimp [stream.map, stream.nth],
  ginduction s n with e; intro,
  { rw al e, assumption }, { contradiction }
end⟩

def join : seq (seq1 α) → seq α :=
corec (λS, match destruct S with
  | none := none
  | some ((a, s), S') := some (a, match destruct s with
    | none := S'
    | some s' := cons s' S'
    end)
  end)

def drop (s : seq α) : ℕ → seq α
| 0     := s
| (n+1) := tail (drop n)
attribute [simp] drop

def take : ℕ → seq α → list α
| 0     s := []
| (n+1) s := match destruct s with
  | none := []
  | some (x, r) := list.cons x (take n r)
  end

def split_at : ℕ → seq α → list α × seq α
| 0     s := ([], s)
| (n+1) s := match destruct s with
  | none := ([], nil)
  | some (x, s') := let (l, r) := split_at n s' in (list.cons x l, r)
  end

def zip_with (f : α → β → γ) : seq α → seq β → seq γ
| ⟨f₁, a₁⟩ ⟨f₂, a₂⟩ := ⟨λn,
    match f₁ n, f₂ n with
    | some a, some b := some (f a b)
    | _, _ := none
    end,
  λn, begin
    ginduction f₁ n with h1,
    { intro H, rw a₁ h1, refl },
    ginduction f₂ n with h2; dsimp [seq.zip_with._match_1]; intro H,
    { rw a₂ h2, cases f₁ (n + 1); refl },
    { contradiction }
  end⟩

def zip : seq α → seq β → seq (α × β) := zip_with prod.mk

def unzip (s : seq (α × β)) : seq α × seq β := (map prod.fst s, map prod.snd s)

def to_list (s : seq α) (h : ∃ n, ¬ (nth s n).is_some) : list α :=
take (nat.find h) s

def to_stream (s : seq α) (h : ∀ n, (nth s n).is_some) : stream α :=
λn, option.get (h n)

def to_list_or_stream (s : seq α) [decidable (∃ n, ¬ (nth s n).is_some)] :
  list α ⊕ stream α :=
if h : ∃ n, ¬ (nth s n).is_some
then sum.inl (to_list s h)
else sum.inr (to_stream s (λn, decidable.by_contradiction (λ hn, h ⟨n, hn⟩)))

@[simp] theorem nil_append (s : seq α) : append nil s = s :=
begin
  apply coinduction2, intro s,
  dsimp [append], rw [corec_eq],
  dsimp [append], apply cases_on s _ _,
  { trivial },
  { intros x s,
    rw [destruct_cons], dsimp,
    exact ⟨rfl, s, rfl, rfl⟩ }
end

@[simp] theorem cons_append (a : α) (s t) : append (cons a s) t = cons a (append s t) :=
destruct_eq_cons $ begin
  dsimp [append], rw [corec_eq],
  dsimp [append], rw [destruct_cons],
  dsimp [append], refl
end

@[simp] theorem append_nil (s : seq α) : append s nil = s :=
begin
  apply coinduction2 s, intro s,
  apply cases_on s _ _,
  { trivial },
  { intros x s,
    rw [cons_append, destruct_cons, destruct_cons], dsimp,
    exact ⟨rfl, s, rfl, rfl⟩ }
end

@[simp] theorem append_assoc (s t u : seq α) :
  append (append s t) u = append s (append t u) :=
begin
  apply eq_of_bisim (λs1 s2, ∃ s t u,
    s1 = append (append s t) u ∧ s2 = append s (append t u)),
  { intros s1 s2 h, exact match s1, s2, h with ._, ._, ⟨s, t, u, rfl, rfl⟩ := begin
      apply cases_on s; simp,
      { apply cases_on t; simp,
        { apply cases_on u; simp,
          { intros x u, refine ⟨nil, nil, u, _, _⟩; simp } },
        { intros x t, refine ⟨nil, t, u, _, _⟩; simp } },
      { intros x s, exact ⟨s, t, u, rfl, rfl⟩ }
    end end },
  { exact ⟨s, t, u, rfl, rfl⟩ }
end

@[simp] theorem map_nil (f : α → β) : map f nil = nil := rfl

@[simp] theorem map_cons (f : α → β) (a) : ∀ s, map f (cons a s) = cons (f a) (map f s)
| ⟨s, al⟩ := by apply subtype.eq; dsimp [cons, map]; rw stream.map_cons; refl

@[simp] theorem map_id : ∀ (s : seq α), map id s = s
| ⟨s, al⟩ := begin
  apply subtype.eq; dsimp [map],
  rw [option.map_id, stream.map_id]; refl
end

@[simp] theorem map_tail (f : α → β) : ∀ s, map f (tail s) = tail (map f s)
| ⟨s, al⟩ := by apply subtype.eq; dsimp [tail, map]; rw stream.map_tail; refl

theorem map_comp (f : α → β) (g : β → γ) : ∀ (s : seq α), map (g ∘ f) s = map g (map f s)
| ⟨s, al⟩ := begin
  apply subtype.eq; dsimp [map],
  rw stream.map_map,
  apply congr_arg (λ f : _ → option γ, stream.map f s),
  apply funext, intro, cases x with x; refl
end

@[simp] theorem map_append (f : α → β) (s t) : map f (append s t) = append (map f s) (map f t) :=
begin
  apply eq_of_bisim (λs1 s2, ∃ s t,
    s1 = map f (append s t) ∧ s2 = append (map f s) (map f t)) _ ⟨s, t, rfl, rfl⟩,
  intros s1 s2 h, exact match s1, s2, h with ._, ._, ⟨s, t, rfl, rfl⟩ := begin
    apply cases_on s; simp,
    { apply cases_on t; simp,
      { intros x t, refine ⟨nil, t, _, _⟩; simp } },
    { intros x s, refine ⟨s, t, rfl, rfl⟩ }
  end end
end

@[simp] theorem map_nth (f : α → β) : ∀ s n, nth (map f s) n = (nth s n).map f
| ⟨s, al⟩ n := rfl

instance : functor seq :=
{ map := @map, id_map := @map_id, map_comp := @map_comp }

@[simp] theorem join_nil : join nil = (nil : seq α) := destruct_eq_nil rfl

@[simp] theorem join_cons_nil (a : α) (S) :
  join (cons (a, nil) S) = cons a (join S) :=
destruct_eq_cons $ by simp [join]

@[simp] theorem join_cons_cons (a b : α) (s S) :
  join (cons (a, cons b s) S) = cons a (join (cons (b, s) S)) :=
destruct_eq_cons $ by simp [join]

@[simp] theorem join_cons (a : α) (s S) :
  join (cons (a, s) S) = cons a (append s (join S)) :=
begin
  apply eq_of_bisim (λs1 s2, s1 = s2 ∨
    ∃ a s S, s1 = join (cons (a, s) S) ∧
      s2 = cons a (append s (join S))) _ (or.inr ⟨a, s, S, rfl, rfl⟩),
  intros s1 s2 h,
  exact match s1, s2, h with
  | _, _, (or.inl $ eq.refl s) := begin
      apply cases_on s, { trivial },
      { intros x s, rw [destruct_cons], exact ⟨rfl, or.inl rfl⟩ }
    end
  | ._, ._, (or.inr ⟨a, s, S, rfl, rfl⟩) := begin
      apply cases_on s,
      { simp },
      { intros x s, simp, refine or.inr ⟨x, s, S, rfl, rfl⟩ }
    end
  end
end

@[simp] theorem join_append (S T : seq (seq1 α)) :
  join (append S T) = append (join S) (join T) :=
begin
  apply eq_of_bisim (λs1 s2, ∃ s S T,
    s1 = append s (join (append S T)) ∧
    s2 = append s (append (join S) (join T))),
  { intros s1 s2 h, exact match s1, s2, h with ._, ._, ⟨s, S, T, rfl, rfl⟩ := begin
      apply cases_on s; simp,
      { apply cases_on S; simp,
        { apply cases_on T, { simp },
          { intros s T, cases s with a s; simp,
            refine ⟨s, nil, T, _, _⟩; simp } },
        { intros s S, cases s with a s; simp,
          exact ⟨s, S, T, rfl, rfl⟩ } },
      { intros x s, exact ⟨s, S, T, rfl, rfl⟩ }
    end end },
  { refine ⟨nil, S, T, _, _⟩; simp }
end

@[simp] def of_list_nil : of_list [] = (nil : seq α) := rfl

@[simp] def of_list_cons (a : α) (l) :
  of_list (a :: l) = cons a (of_list l) :=
begin
  apply subtype.eq, simp [of_list, cons],
  apply funext, intro n, cases n; simp [list.nth, stream.cons]
end

@[simp] def of_stream_cons (a : α) (s) :
  of_stream (a :: s) = cons a (of_stream s) :=
by apply subtype.eq; simp [of_stream, cons]; rw stream.map_cons

@[simp] def of_list_append (l l' : list α) :
  of_list (l ++ l') = append (of_list l) (of_list l') :=
by induction l; simp [*]

@[simp] def of_stream_append (l : list α) (s : stream α) :
  of_stream (l ++ₛ s) = append (of_list l) (of_stream s) :=
by induction l; simp [*, stream.nil_append_stream, stream.cons_append_stream]

def to_list' {α} (s : seq α) : computation (list α) :=
@computation.corec (list α) (list α × seq α) (λ⟨l, s⟩,
  match destruct s with
  | none         := sum.inl l.reverse
  | some (a, s') := sum.inr (a::l, s')
  end) ([], s)

theorem dropn_add (s : seq α) (m) : ∀ n, drop s (m + n) = drop (drop s m) n
| 0     := rfl
| (n+1) := congr_arg tail (dropn_add n)

theorem dropn_tail (s : seq α) (n) : drop (tail s) n = drop s (n + 1) :=
by rw add_comm; symmetry; apply dropn_add

theorem nth_tail : ∀ (s : seq α) n, nth (tail s) n = nth s (n + 1)
| ⟨f, al⟩ n := rfl

@[simp] theorem head_dropn (s : seq α) (n) : head (drop s n) = nth s n :=
begin
  induction n with n IH generalizing s, { refl },
  rw [nat.succ_eq_add_one, ←nth_tail, ←dropn_tail], apply IH
end

theorem mem_map (f : α → β) {a : α} : ∀ {s : seq α}, a ∈ s → f a ∈ map f s
| ⟨g, al⟩ := stream.mem_map (option.map f)

theorem exists_of_mem_map {f} {b : β} : ∀ {s : seq α}, b ∈ map f s → ∃ a, a ∈ s ∧ f a = b
| ⟨g, al⟩ h := let ⟨o, om, oe⟩ := stream.exists_of_mem_map h in
  by cases o; injection oe; exact ⟨a, om, h⟩

def of_mem_append {s₁ s₂ : seq α} {a : α} (h : a ∈ append s₁ s₂) : a ∈ s₁ ∨ a ∈ s₂ :=
begin
  have := h, revert this,
  generalize e : append s₁ s₂ = ss, intro h, revert s₁,
  apply mem_rec_on h _,
  intros b s' o s₁,
  apply s₁.cases_on _ (λ c t₁, _); intros m e;
  have := congr_arg destruct e; simp at this; injections with i1 i2 i3,
  { simp at m, exact or.inr m },
  { simp at m, cases m with e' m,
    { rw e', exact or.inl (mem_cons _ _) },
    { rw i2, cases o with e' IH,
      { rw e', exact or.inl (mem_cons _ _) },
      { exact or.imp_left (mem_cons_of_mem _) (IH m i3) } } }
end

def mem_append_left {s₁ s₂ : seq α} {a : α} (h : a ∈ s₁) : a ∈ append s₁ s₂ :=
by apply mem_rec_on h; intros; simp [*]

end seq

namespace seq1
variables {α : Type u} {β : Type v} {γ : Type w}
open seq

def to_seq : seq1 α → seq α
| (a, s) := cons a s

instance coe_seq : has_coe (seq1 α) (seq α) := ⟨to_seq⟩

def map (f : α → β) : seq1 α → seq1 β
| (a, s) := (f a, seq.map f s)

theorem map_id : ∀ (s : seq1 α), map id s = s | ⟨a, s⟩ := by simp [map]

def join : seq1 (seq1 α) → seq1 α
| ((a, s), S) := match destruct s with
  | none := (a, seq.join S)
  | some s' := (a, seq.join (cons s' S))
  end

@[simp] theorem join_nil (a : α) (S) : join ((a, nil), S) = (a, seq.join S) := rfl

@[simp] theorem join_cons (a b : α) (s S) :
  join ((a, cons b s), S) = (a, seq.join (cons (b, s) S)) :=
by dsimp [join]; rw [destruct_cons]; refl

def ret (a : α) : seq1 α := (a, nil)

def bind (s : seq1 α) (f : α → seq1 β) : seq1 β :=
join (map f s)

@[simp] theorem join_map_ret (s : seq α) : seq.join (seq.map ret s) = s :=
by apply coinduction2 s; intro s; apply cases_on s; simp [ret]

@[simp] theorem bind_ret (f : α → β) : ∀ s, bind s (ret ∘ f) = map f s
| ⟨a, s⟩ := begin
  dsimp [bind, map], change (λx, ret (f x)) with (ret ∘ f),
  rw [map_comp], simp [function.comp, ret]
end

@[simp] theorem ret_bind (a : α) (f : α → seq1 β) : bind (ret a) f = f a :=
begin
  simp [ret, bind, map],
  cases f a with a s,
  apply cases_on s; intros; simp
end

@[simp] theorem map_join' (f : α → β) (S) :
  seq.map f (seq.join S) = seq.join (seq.map (map f) S) :=
begin
  apply eq_of_bisim (λs1 s2,
    ∃ s S, s1 = append s (seq.map f (seq.join S)) ∧
      s2 = append s (seq.join (seq.map (map f) S))),
  { intros s1 s2 h, exact match s1, s2, h with ._, ._, ⟨s, S, rfl, rfl⟩ := begin
      apply cases_on s; simp,
      { apply cases_on S; simp,
        { intros x S, cases x with a s; simp [map],
          exact ⟨_, _, rfl, rfl⟩ } },
      { intros x s, refine ⟨s, S, rfl, rfl⟩ }
    end end },
  { refine ⟨nil, S, _, _⟩; simp }
end

@[simp] theorem map_join (f : α → β) : ∀ S, map f (join S) = join (map (map f) S)
| ((a, s), S) := by apply cases_on s; intros; simp [map]

@[simp] theorem join_join (SS : seq (seq1 (seq1 α))) :
  seq.join (seq.join SS) = seq.join (seq.map join SS) :=
begin
  apply eq_of_bisim (λs1 s2,
    ∃ s SS, s1 = seq.append s (seq.join (seq.join SS)) ∧
      s2 = seq.append s (seq.join (seq.map join SS))),
  { intros s1 s2 h, exact match s1, s2, h with ._, ._, ⟨s, SS, rfl, rfl⟩ := begin
      apply cases_on s; simp,
      { apply cases_on SS; simp,
        { intros S SS, cases S with s S; cases s with x s; simp [map],
          apply cases_on s; simp,
          { exact ⟨_, _, rfl, rfl⟩ },
          { intros x s,
            refine ⟨cons x (append s (seq.join S)), SS, _, _⟩; simp } } },
      { intros x s, exact ⟨s, SS, rfl, rfl⟩ }
    end end },
  { refine ⟨nil, SS, _, _⟩; simp }
end

@[simp] theorem bind_assoc (s : seq1 α) (f : α → seq1 β) (g : β → seq1 γ) :
  bind (bind s f) g = bind s (λ (x : α), bind (f x) g) :=
begin
  cases s with a s,
  simp [bind, map],
  rw [←map_comp],
  change (λ x, join (map g (f x))) with (join ∘ ((map g) ∘ f)),
  rw [map_comp _ join],
  generalize : seq.map (map g ∘ f) s = SS,
  cases map g (f a) with s S,
  cases s with a s,
  apply cases_on s; intros; apply cases_on S; intros; simp,
  { cases x with x t, apply cases_on t; intros; simp },
  { cases x_1 with y t; simp }
end

instance : monad seq1 :=
{ map  := @map,
  pure := @ret,
  bind := @bind,
  id_map := @map_id,
  bind_pure_comp_eq_map := @bind_ret,
  pure_bind := @ret_bind,
  bind_assoc := @bind_assoc }

end seq1
