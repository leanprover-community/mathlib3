/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

An experimental variant on the `ring` tactic that uses computational
reflection instead of proof generation. Useful for kernel benchmarking.
-/
import tactic.ring data.num.lemmas
import tactic.converter.interactive

namespace tactic.ring2

@[derive has_reflect]
inductive {u} tree (α : Type u) : Type u
| nil {} : tree
| node : α → tree → tree → tree

def tree.get {α} [has_zero α] : pos_num → tree α → α
| _                tree.nil            := 0
| pos_num.one      (tree.node a t₁ t₂) := a
| (pos_num.bit0 n) (tree.node a t₁ t₂) := t₁.get n
| (pos_num.bit1 n) (tree.node a t₁ t₂) := t₂.get n

def tree.of_rbnode {α} : rbnode α → tree α
| rbnode.leaf               := tree.nil
| (rbnode.red_node l a r)   :=
  tree.node a (tree.of_rbnode l) (tree.of_rbnode r)
| (rbnode.black_node l a r) :=
  tree.node a (tree.of_rbnode l) (tree.of_rbnode r)

def tree.index_of {α} (lt : α → α → Prop) [decidable_rel lt]
  (x : α) : tree α → option pos_num
| tree.nil := none
| (tree.node a t₁ t₂) :=
  match cmp_using lt x a with
  | ordering.lt := pos_num.bit0 <$> tree.index_of t₁
  | ordering.eq := some pos_num.one
  | ordering.gt := pos_num.bit1 <$> tree.index_of t₂
  end

meta def tree.reflect' (u : level) (α : expr) : tree expr → expr
| tree.nil := (expr.const ``tree.nil [u] : expr) α
| (tree.node a t₁ t₂) :=
  (expr.const ``tree.node [u] : expr) α a t₁.reflect' t₂.reflect'

@[derive has_reflect]
inductive csring_expr
| atom : pos_num → csring_expr
| const : num → csring_expr
| add : csring_expr → csring_expr → csring_expr
| mul : csring_expr → csring_expr → csring_expr
| pow : csring_expr → num → csring_expr

namespace csring_expr

def eval {α} [comm_semiring α] (t : tree α) : csring_expr → α
| (atom n)  := @tree.get _ ⟨0⟩ n t
| (const n) := n
| (add x y) := eval x + eval y
| (mul x y) := eval x * eval y
| (pow x n) := eval x ^ (n : ℕ)

end csring_expr

@[derive decidable_eq]
inductive horner_expr
| const : znum → horner_expr
| horner : horner_expr → pos_num → num → horner_expr → horner_expr

namespace horner_expr

def is_cs : horner_expr → Prop
| (const n) := ∃ m:num, n = m.to_znum
| (horner a x n b) := is_cs a ∧ is_cs b

instance : has_zero horner_expr := ⟨const 0⟩
instance : has_one horner_expr := ⟨const 1⟩

def atom (n : pos_num) : horner_expr := horner 1 n 1 0

def repr : horner_expr → string
| (const n) := _root_.repr n
| (horner a x n b) :=
    "(" ++ repr a ++ ") * x" ++ _root_.repr x ++ "^"
        ++ _root_.repr n ++ " + " ++ repr b
instance : has_repr horner_expr := ⟨repr⟩

def horner' (a : horner_expr)
  (x : pos_num) (n : num) (b : horner_expr) : horner_expr :=
match a with
| const q := if q = 0 then b else horner a x n b
| horner a₁ x₁ n₁ b₁ :=
  if x₁ = x ∧ b₁ = 0 then horner a₁ x (n₁ + n) b
  else horner a x n b
end

def add_const (k : znum) (e : horner_expr) : horner_expr :=
if k = 0 then e else begin
  induction e with n a x n b A B,
  { exact const (k + n) },
  { exact horner a x n B }
end

def add_aux (a₁ : horner_expr) (A₁ : horner_expr → horner_expr) (x₁ : pos_num) :
  horner_expr → num → horner_expr → (horner_expr → horner_expr) → horner_expr
| (const n₂)           n₁ b₁ B₁ := add_const n₂ (horner a₁ x₁ n₁ b₁)
| (horner a₂ x₂ n₂ b₂) n₁ b₁ B₁ :=
  let e₂ := horner a₂ x₂ n₂ b₂ in
  match pos_num.cmp x₁ x₂ with
  | ordering.lt := horner a₁ x₁ n₁ (B₁ e₂)
  | ordering.gt := horner a₂ x₂ n₂ (add_aux b₂ n₁ b₁ B₁)
  | ordering.eq :=
    match num.sub' n₁ n₂ with
    | znum.zero := horner' (A₁ a₂) x₁ n₁ (B₁ b₂)
    | (znum.pos k) := horner (add_aux a₂ k 0 id) x₁ n₂ (B₁ b₂)
    | (znum.neg k) := horner (A₁ (horner a₂ x₁ k 0)) x₁ n₁ (B₁ b₂)
    end
  end

def add : horner_expr → horner_expr → horner_expr
| (const n₁)           e₂ := add_const n₁ e₂
| (horner a₁ x₁ n₁ b₁) e₂ := add_aux a₁ (add a₁) x₁ e₂ n₁ b₁ (add b₁)
/-begin
  induction e₁ with n₁ a₁ x₁ n₁ b₁ A₁ B₁ generalizing e₂,
  { exact add_const n₁ e₂ },
  exact match e₂ with e₂ := begin
    induction e₂ with n₂ a₂ x₂ n₂ b₂ A₂ B₂ generalizing n₁ b₁;
    let e₁ := horner a₁ x₁ n₁ b₁,
    { exact add_const n₂ e₁ },
    let e₂ := horner a₂ x₂ n₂ b₂,
    exact match pos_num.cmp x₁ x₂ with
    | ordering.lt := horner a₁ x₁ n₁ (B₁ e₂)
    | ordering.gt := horner a₂ x₂ n₂ (B₂ n₁ b₁)
    | ordering.eq :=
      match num.sub' n₁ n₂ with
      | znum.zero := horner' (A₁ a₂) x₁ n₁ (B₁ b₂)
      | (znum.pos k) := horner (A₂ k 0) x₁ n₂ (B₁ b₂)
      | (znum.neg k) := horner (A₁ (horner a₂ x₁ k 0)) x₁ n₁ (B₁ b₂)
      end
    end
  end end
end-/

def neg (e : horner_expr) : horner_expr :=
begin
  induction e with n a x n b A B,
  { exact const (-n) },
  { exact horner A x n B }
end

def mul_const (k : znum) (e : horner_expr) : horner_expr :=
if k = 0 then 0 else if k = 1 then e else begin
  induction e with n a x n b A B,
  { exact const (n * k) },
  { exact horner A x n B }
end

def mul_aux (a₁ x₁ n₁ b₁) (A₁ B₁ : horner_expr → horner_expr) :
  horner_expr → horner_expr
| (const n₂) := mul_const n₂ (horner a₁ x₁ n₁ b₁)
| e₂@(horner a₂ x₂ n₂ b₂) :=
  match pos_num.cmp x₁ x₂ with
  | ordering.lt := horner (A₁ e₂) x₁ n₁ (B₁ e₂)
  | ordering.gt := horner (mul_aux a₂) x₂ n₂ (mul_aux b₂)
  | ordering.eq := let haa := horner' (mul_aux a₂) x₁ n₂ 0 in
    if b₂ = 0 then haa else haa.add (horner (A₁ b₂) x₁ n₁ (B₁ b₂))
  end

def mul : horner_expr → horner_expr → horner_expr
| (const n₁)              := mul_const n₁
| e₁@(horner a₁ x₁ n₁ b₁) := mul_aux a₁ x₁ n₁ b₁ (mul a₁) (mul b₁).
/-begin
  induction e₁ with n₁ a₁ x₁ n₁ b₁ A₁ B₁ generalizing e₂,
  { exact mul_const n₁ e₂ },
  induction e₂ with n₂ a₂ x₂ n₂ b₂ A₂ B₂;
  let e₁ := horner a₁ x₁ n₁ b₁,
  { exact mul_const n₂ e₁ },
  let e₂ := horner a₂ x₂ n₂ b₂,
  cases pos_num.cmp x₁ x₂,
  { exact horner (A₁ e₂) x₁ n₁ (B₁ e₂) },
  { let haa := horner' A₂ x₁ n₂ 0,
    exact if b₂ = 0 then haa else
      haa.add (horner (A₁ b₂) x₁ n₁ (B₁ b₂)) },
  { exact horner A₂ x₂ n₂ B₂ }
end-/

instance : has_add horner_expr := ⟨add⟩
instance : has_neg horner_expr := ⟨neg⟩
instance : has_mul horner_expr := ⟨mul⟩

def pow (e : horner_expr) : num → horner_expr
| 0 := 1
| (num.pos p) := begin
  induction p with p ep p ep,
  { exact e },
  { exact (ep.mul ep).mul e },
  { exact ep.mul ep }
end

def inv (e : horner_expr) : horner_expr := 0

def of_csexpr : csring_expr → horner_expr
| (csring_expr.atom n)  := atom n
| (csring_expr.const n) := const n.to_znum
| (csring_expr.add x y) := (of_csexpr x).add (of_csexpr y)
| (csring_expr.mul x y) := (of_csexpr x).mul (of_csexpr y)
| (csring_expr.pow x n) := (of_csexpr x).pow n

def cseval {α} [comm_semiring α] (t : tree α) : horner_expr → α
| (const n)        := n.abs
| (horner a x n b) := tactic.ring.horner (cseval a) (t.get x) n (cseval b)

theorem cseval_atom {α} [comm_semiring α] (t : tree α)
  (n : pos_num) : (atom n).is_cs ∧ cseval t (atom n) = t.get n :=
⟨⟨⟨1, rfl⟩, ⟨0, rfl⟩⟩, (tactic.ring.horner_atom _).symm⟩

theorem cseval_add_const {α} [comm_semiring α] (t : tree α)
  (k : num) {e : horner_expr} (cs : e.is_cs) :
  (add_const k.to_znum e).is_cs ∧
    cseval t (add_const k.to_znum e) = k + cseval t e :=
begin
  simp [add_const],
  cases k; simp! *,
  simp [show znum.pos k ≠ 0, from dec_trivial],
  induction e with n a x n b A B; simp *,
  { rcases cs with ⟨n, rfl⟩,
    refine ⟨⟨n + num.pos k, by simp; refl⟩, _⟩,
    cases n; simp! },
  { rcases B cs.2 with ⟨csb, h⟩, simp! [*, cs.1],
    rw [← tactic.ring.horner_add_const, add_comm], refl }
end

theorem cseval_horner' {α} [comm_semiring α] (t : tree α)
  (a x n b) (h₁ : is_cs a) (h₂ : is_cs b) :
  (horner' a x n b).is_cs ∧ cseval t (horner' a x n b) =
    tactic.ring.horner (cseval t a) (t.get x) n (cseval t b) :=
begin
  cases a with n₁ a₁ x₁ n₁ b₁; simp [horner']; split_ifs,
  { simp! [*, tactic.ring.horner] },
  { exact ⟨⟨h₁, h₂⟩, rfl⟩ },
  { refine ⟨⟨h₁.1, h₂⟩, eq.symm _⟩, simp! *,
    apply tactic.ring.horner_horner, simp },
  { exact ⟨⟨h₁, h₂⟩, rfl⟩ }
end

theorem cseval_add {α} [comm_semiring α] (t : tree α)
  {e₁ e₂ : horner_expr} (cs₁ : e₁.is_cs) (cs₂ : e₂.is_cs) :
  (add e₁ e₂).is_cs ∧
  cseval t (add e₁ e₂) = cseval t e₁ + cseval t e₂ :=
begin
  induction e₁ with n₁ a₁ x₁ n₁ b₁ A₁ B₁ generalizing e₂; simp!,
  { rcases cs₁ with ⟨n₁, rfl⟩,
    simpa using cseval_add_const t n₁ cs₂ },
  induction e₂ with n₂ a₂ x₂ n₂ b₂ A₂ B₂ generalizing n₁ b₁,
  { rcases cs₂ with ⟨n₂, rfl⟩,
    simp! [cseval_add_const t n₂ cs₁] },
  cases cs₁ with csa₁ csb₁, cases id cs₂ with csa₂ csb₂,
  simp!, have C := pos_num.cmp_to_nat x₁ x₂,
  cases pos_num.cmp x₁ x₂; simp!,
  { rcases B₁ csb₁ cs₂ with ⟨csh, h⟩,
    refine ⟨⟨csa₁, csh⟩, eq.symm _⟩,
    apply tactic.ring.horner_add_const,
    exact h.symm },
  { cases C,
    have B0 : is_cs 0 → ∀ {e₂ : horner_expr}, is_cs e₂ →
      is_cs (add 0 e₂) ∧ cseval t (add 0 e₂) = cseval t 0 + cseval t e₂ :=
      λ _ e₂ c, ⟨c, (zero_add _).symm⟩,
     cases e : num.sub' n₁ n₂ with k k; simp!,
    { have : n₁ = n₂,
      { have := congr_arg (coe : znum → ℤ) e,
        simp at this,
        have := sub_eq_zero.1 this,
        rw [← num.to_nat_to_int, ← num.to_nat_to_int] at this,
        exact num.to_nat_inj.1 (int.coe_nat_inj this) },
      subst n₂,
      rcases cseval_horner' _ _ _ _ _ _ _ with ⟨csh, h⟩,
      { refine ⟨csh, h.trans (eq.symm _)⟩,
        simp *,
        apply tactic.ring.horner_add_horner_eq; try {refl},
        simp },
      all_goals {simp! *} },
    { simp [B₁ csb₁ csb₂],
      rcases A₂ csa₂ _ _ B0 ⟨csa₁, 0, rfl⟩ with ⟨csh, h⟩,
      refine ⟨csh, eq.symm _⟩,
      rw [show id = add 0, from rfl, h],
      apply tactic.ring.horner_add_horner_gt,
      { change (_ + k : ℕ) = _,
        rw [← int.coe_nat_inj', int.coe_nat_add,
          eq_comm, ← sub_eq_iff_eq_add'],
        simpa using congr_arg (coe : znum → ℤ) e },
      all_goals { apply add_comm } },
    { have : (horner a₂ x₁ (num.pos k) 0).is_cs := ⟨csa₂, 0, rfl⟩,
      simp [B₁ csb₁ csb₂, A₁ csa₁ this],
      symmetry, apply tactic.ring.horner_add_horner_lt,
      { change (_ + k : ℕ) = _,
          rw [← int.coe_nat_inj', int.coe_nat_add,
            eq_comm, ← sub_eq_iff_eq_add', ← neg_inj', neg_sub],
        simpa using congr_arg (coe : znum → ℤ) e },
      { refl }, { apply add_comm } } },
  { rcases B₂ csb₂ _ _ B₁ ⟨csa₁, csb₁⟩ with ⟨csh, h⟩,
    refine ⟨⟨csa₂, csh⟩, eq.symm _⟩,
    apply tactic.ring.const_add_horner,
    simp [h] }
end

theorem cseval_mul_const {α} [comm_semiring α] (t : tree α)
  (k : num) {e : horner_expr} (cs : e.is_cs) :
  (mul_const k.to_znum e).is_cs ∧
    cseval t (mul_const k.to_znum e) = cseval t e * k :=
begin
  simp [mul_const],
  split_ifs with h h,
  { cases (num.to_znum_inj.1 h : k = 0),
    exact ⟨⟨0, rfl⟩, (mul_zero _).symm⟩ },
  { cases (num.to_znum_inj.1 h : k = 1),
    exact ⟨cs, (mul_one _).symm⟩ },
  induction e with n a x n b A B; simp *,
  { rcases cs with ⟨n, rfl⟩,
    suffices, refine ⟨⟨n * k, this⟩, _⟩,
    swap, {cases n; cases k; refl},
    rw [show _, from this], simp! },
  { cases cs, simp! *,
    symmetry, apply tactic.ring.horner_mul_const; refl }
end

theorem cseval_mul {α} [comm_semiring α] (t : tree α)
  {e₁ e₂ : horner_expr} (cs₁ : e₁.is_cs) (cs₂ : e₂.is_cs) :
  (mul e₁ e₂).is_cs ∧
  cseval t (mul e₁ e₂) = cseval t e₁ * cseval t e₂ :=
begin
  induction e₁ with n₁ a₁ x₁ n₁ b₁ A₁ B₁ generalizing e₂; simp!,
  { rcases cs₁ with ⟨n₁, rfl⟩,
    simpa [mul_comm] using cseval_mul_const t n₁ cs₂ },
  induction e₂ with n₂ a₂ x₂ n₂ b₂ A₂ B₂,
  { rcases cs₂ with ⟨n₂, rfl⟩,
    simpa! using cseval_mul_const t n₂ cs₁ },
  cases cs₁ with csa₁ csb₁, cases id cs₂ with csa₂ csb₂,
  simp!, have C := pos_num.cmp_to_nat x₁ x₂,
  cases A₂ csa₂ with csA₂ hA₂,
  cases pos_num.cmp x₁ x₂; simp!,
  { simp [A₁ csa₁ cs₂, B₁ csb₁ cs₂],
    symmetry, apply tactic.ring.horner_mul_const; refl },
  { cases cseval_horner' t _ x₁ n₂ 0 csA₂ ⟨0, rfl⟩ with csh₁ h₁,
    cases C, split_ifs,
    { subst b₂,
      refine ⟨csh₁, h₁.trans (eq.symm _)⟩,
      apply tactic.ring.horner_mul_horner_zero; try {refl},
      simp! [hA₂] },
    { cases A₁ csa₁ csb₂ with csA₁ hA₁,
      cases cseval_add t csh₁ _ with csh₂ h₂,
      { refine ⟨csh₂, h₂.trans (eq.symm _)⟩,
        apply tactic.ring.horner_mul_horner; try {refl},
        simp! * },
      exact ⟨csA₁, (B₁ csb₁ csb₂).1⟩ } },
  { simp [A₂ csa₂, B₂ csb₂], rw [mul_comm, eq_comm],
    apply tactic.ring.horner_const_mul,
    {apply mul_comm}, {refl} },
end

theorem cseval_pow {α} [comm_semiring α] (t : tree α)
  {x : horner_expr} (cs : x.is_cs) :
  ∀ (n : num), (pow x n).is_cs ∧
    cseval t (pow x n) = cseval t x ^ (n : ℕ)
| 0 := ⟨⟨1, rfl⟩, (pow_zero _).symm⟩
| (num.pos p) := begin
  simp [pow], induction p with p ep p ep,
  { simp * },
  { simp [pow_bit1],
    cases cseval_mul t ep.1 ep.1 with cs₀ h₀,
    cases cseval_mul t cs₀ cs with cs₁ h₁,
    simp * },
  { simp [pow_bit0],
    cases cseval_mul t ep.1 ep.1 with cs₀ h₀,
    simp * }
end

theorem cseval_of_csexpr {α} [comm_semiring α] (t : tree α) :
  ∀ (r : csring_expr), (of_csexpr r).is_cs ∧ cseval t (of_csexpr r) = r.eval t
| (csring_expr.atom n)  := cseval_atom _ _
| (csring_expr.const n) := ⟨⟨n, rfl⟩, by cases n; refl⟩
| (csring_expr.add x y) :=
  let ⟨cs₁, h₁⟩ := cseval_of_csexpr x,
      ⟨cs₂, h₂⟩ := cseval_of_csexpr y,
      ⟨cs, h⟩ := cseval_add t cs₁ cs₂ in ⟨cs, by simp! [h, *]⟩
| (csring_expr.mul x y) :=
  let ⟨cs₁, h₁⟩ := cseval_of_csexpr x,
      ⟨cs₂, h₂⟩ := cseval_of_csexpr y,
      ⟨cs, h⟩ := cseval_mul t cs₁ cs₂ in ⟨cs, by simp! [h, *]⟩
| (csring_expr.pow x n) :=
  let ⟨cs, h⟩ := cseval_of_csexpr x,
      ⟨cs, h⟩ := cseval_pow t cs n in ⟨cs, by simp! [h, *]⟩

end horner_expr

theorem correctness {α} [comm_semiring α] (t : tree α) (r₁ r₂ : csring_expr)
  (H : horner_expr.of_csexpr r₁ = horner_expr.of_csexpr r₂) :
  r₁.eval t = r₂.eval t :=
by repeat {rw ← (horner_expr.cseval_of_csexpr t _).2}; rw H

meta def reflect_expr : expr → csring_expr × dlist expr
| `(%%e₁ + %%e₂) :=
  let (r₁, l₁) := reflect_expr e₁, (r₂, l₂) := reflect_expr e₂ in
  (r₁.add r₂, l₁ ++ l₂)
/-| `(%%e₁ - %%e₂) :=
  let (r₁, l₁) := reflect_expr e₁, (r₂, l₂) := reflect_expr e₂ in
  (r₁.add r₂.neg, l₁ ++ l₂)
| `(- %%e) := let (r, l) := reflect_expr e in (r.neg, l)-/
| `(%%e₁ * %%e₂) :=
  let (r₁, l₁) := reflect_expr e₁, (r₂, l₂) := reflect_expr e₂ in
  (r₁.mul r₂, l₁ ++ l₂)
/-| `(has_inv.inv %%e) := let (r, l) := reflect_expr e in (r.neg, l)
| `(%%e₁ / %%e₂) :=
  let (r₁, l₁) := reflect_expr e₁, (r₂, l₂) := reflect_expr e₂ in
  (r₁.mul r₂.inv, l₁ ++ l₂)-/
| e@`(%%e₁ ^ %%e₂) :=
  match reflect_expr e₁, expr.to_nat e₂ with
  | (r₁, l₁), some n₂ := (r₁.pow (num.of_nat' n₂), l₁)
  | (r₁, l₁), none := (csring_expr.atom 1, dlist.singleton e)
  end
| e := match expr.to_nat e with
  | some n := (csring_expr.const (num.of_nat' n), dlist.empty)
  | none := (csring_expr.atom 1, dlist.singleton e)
  end

meta def csring_expr.replace (t : tree expr) : csring_expr → state_t (list expr) option csring_expr
| (csring_expr.atom _)  := do e ← get,
  p ← monad_lift (t.index_of (<) e.head),
  put e.tail, pure (csring_expr.atom p)
| (csring_expr.const n) := pure (csring_expr.const n)
| (csring_expr.add x y) := csring_expr.add <$> x.replace <*> y.replace
| (csring_expr.mul x y) := csring_expr.mul <$> x.replace <*> y.replace
| (csring_expr.pow x n) := (λ x, csring_expr.pow x n) <$> x.replace
--| (csring_expr.neg x)   := csring_expr.neg <$> x.replace
--| (csring_expr.inv x)   := csring_expr.inv <$> x.replace

end tactic.ring2

namespace tactic
namespace interactive
open interactive interactive.types lean.parser
open tactic.ring2

local postfix `?`:9001 := optional

/-- Tactic for solving equations in the language of rings.
  This variant on the `ring` tactic uses kernel computation instead
  of proof generation. -/
meta def ring2 : tactic unit :=
do `[repeat {rw ← nat.pow_eq_pow}],
  `(%%e₁ = %%e₂) ← target,
  α ← infer_type e₁,
  expr.sort (level.succ u) ← infer_type α,
  let (r₁, l₁) := reflect_expr e₁,
  let (r₂, l₂) := reflect_expr e₂,
  let L := (l₁ ++ l₂).to_list,
  let s := tree.of_rbnode (rbtree_of L).1,
  (r₁, L) ← (state_t.run (r₁.replace s) L : option _),
  (r₂, _) ← (state_t.run (r₂.replace s) L : option _),
  let se : expr := s.reflect' u α,
  let er₁ : expr := reflect r₁,
  let er₂ : expr := reflect r₂,
  cs ← mk_app ``comm_semiring [α] >>= mk_instance,
  e ← to_expr ```(correctness %%se %%er₁ %%er₂ rfl)
    <|> fail ("ring2 tactic failed, using abstract equality:\n"
      ++ repr (horner_expr.of_csexpr r₁) ++
      "\n  =?=\n" ++ repr (horner_expr.of_csexpr r₂)),
  tactic.exact e

end interactive
end tactic

namespace conv.interactive
open conv

meta def ring2 : conv unit := discharge_eq_lhs tactic.interactive.ring2

end conv.interactive
