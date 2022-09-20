/-
Copyright (c) 2022 Mario Carneiro, Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Praneeth Kolichala
-/
import computability.computability_tactic2
import computability.primrec.stack_recursion
import computability.primrec.catalan

/-!
# Lemmas about primitive recursive functions

In this file, we prove a large family of basic functions on lists and trees
primitive recursive.
-/

open tencodable (encode decode)
open function

variables {α β γ δ ε : Type} [tencodable α]
  [tencodable β] [tencodable γ] [tencodable δ] [tencodable ε]

/-- TODO: Move -/
@[simp] lemma _root_.function.has_uncurry.base_eq_self {α β : Type*} (f : α → β) :
  ↿f = f := rfl

namespace primrec

@[primrec] lemma prod_mk : primrec (@prod.mk α β) := primrec.id

@[primrec] lemma cons : primrec (@list.cons α) := primrec.id

@[primrec] protected lemma encode : primrec (@encode α _) := primrec.id

protected lemma iff_comp_encode {f : α → β} : primrec f ↔ primrec (λ x, encode (f x)) := iff.rfl

attribute [primrec] primcodable.prim

@[primrec] lemma prod_rec {f : α → β × γ} {g : α → β → γ → δ} (hf : primrec f) (hg : primrec g) :
  @primrec α δ (α → δ) _ _ _ (λ x, @prod.rec β γ (λ _, δ) (g x) (f x)) :=
by { primrec using (λ x, g x (f x).1 (f x).2), cases f x; refl, }

lemma of_equiv {α β} [tencodable α] (e : β ≃ α) :
  @primrec β α _ (tencodable.of_equiv α e) _ _ ⇑e :=
⟨_, unit_tree.primrec.id, λ _, rfl⟩

lemma of_equiv_symm {α β} [tencodable α] (e : β ≃ α) :
  @primrec α β _ _ (tencodable.of_equiv α e) _ ⇑e.symm :=
⟨_, unit_tree.primrec.id, λ _, by simp [tencodable.of_equiv_encode]⟩

section unit_tree

@[primrec] lemma tree_left : primrec unit_tree.left := ⟨_, unit_tree.primrec.left, λ _, rfl⟩
@[primrec] lemma tree_right : primrec unit_tree.right := ⟨_, unit_tree.primrec.right, λ _, rfl⟩
@[primrec] lemma tree_node : primrec unit_tree.node := ⟨_, unit_tree.primrec.id, λ _, rfl⟩

lemma eq_nil : primrec_pred (=unit_tree.nil) :=
⟨_, unit_tree.primrec.id.ite (unit_tree.primrec.const $ encode tt)
  (unit_tree.primrec.const $ encode ff), λ x, by cases x; simp [has_uncurry.uncurry]⟩

end unit_tree

section bool

@[primrec] lemma coe_sort : primrec_pred (λ b : bool, (b : Prop)) :=
by { rw [← primrec1_iff_primrec_pred], simpa using primrec.id, }

@[primrec] lemma to_bool {P : α → Prop} [decidable_pred P] (hP : primrec_pred P) :
  primrec (λ x, to_bool (P x)) :=
by { rw [← primrec1_iff_primrec, primrec1_iff_primrec_pred'], exact hP, }

@[primrec] protected lemma band : primrec (&&) :=
by { primrec using (λ b₁ b₂, if b₁ then b₂ else ff), cases b₁; simp, }

@[primrec] protected lemma bnot : primrec bnot :=
by { primrec using (λ b, if b then ff else tt), cases b; refl, }

@[primrec] protected lemma and {P₁ P₂ : α → Prop} (h₁ : primrec_pred P₁) (h₂ : primrec_pred P₂) :
  primrec_pred (λ x, (P₁ x) ∧ (P₂ x)) :=
by { classical, simp_rw [← primrec1_iff_primrec_pred', bool.to_bool_and], primrec, }

@[primrec] protected lemma not {P : α → Prop} (h : primrec_pred P) : primrec_pred (λ x, ¬(P x)) :=
by { classical, simp_rw [← primrec1_iff_primrec_pred', bool.to_bool_not], primrec, }

lemma eq_const_aux : ∀ (x : unit_tree), primrec_pred (=x)
| unit_tree.nil := eq_nil
| (unit_tree.node a b) :=
begin
  have := (eq_const_aux a).comp tree_left, have := (eq_const_aux b).comp tree_right, have := eq_nil,
  primrec using (λ y, ¬(y = unit_tree.nil) ∧ y.left = a ∧ y.right = b),
  cases y; simp,
end

end bool

section finite_branching

@[primrec] lemma eq_const {f : α → β} (hf : primrec f) (y : β) :
  primrec_pred (λ x, (f x) = y) :=
by simpa using (eq_const_aux (encode y)).comp hf

@[primrec] lemma tree_cases {f : α → unit_tree} {g : α → β}
  {h : α → unit_tree → unit_tree → β} (hf : primrec f) (hg : primrec g) (hh : primrec h) :
  @primrec α β (α → β) _ _ _ (λ x, @unit_tree.cases_on (λ _, β) (f x) (g x) (h x)) :=
begin
  primrec using (λ x, if f x = unit_tree.nil then g x else h x (f x).left (f x).right),
  cases f x; simp,
end

lemma of_fin_cases [nonempty γ] (S : finset α)
  {f : α → β → γ} (hf : ∀ {x}, x ∈ S → primrec (f x)) :
  ∃ f' : α → β → γ, primrec f' ∧ ∀ {x}, x ∈ S → f x = f' x :=
begin
  classical, inhabit γ,
  induction S using finset.induction with x xs x_nmem ih,
  { refine ⟨λ _ _, default, by primrec, _⟩, simp, },
  rcases ih (λ _ h, hf (finset.mem_insert.mpr (or.inr h))) with ⟨f', pf, hf'⟩,
  set g := f x, have : primrec g := by { apply hf, simp, },
  refine ⟨λ x' y, if x' = x then g y else f' x' y, by primrec, _⟩,
  intro x', split_ifs with H, { simp [H], }, { simpa [H] using hf', },
end

@[primrec] lemma of_to_empty [H : is_empty β] (f : α → β) : primrec f :=
⟨_, unit_tree.primrec.const default, λ x, H.elim' (f x)⟩

lemma of_from_fintype [fintype α] {f : α → β → γ} (hf : ∀ x, primrec (f x)) : primrec f :=
begin
  casesI is_empty_or_nonempty γ, { apply of_to_empty, },
  obtain ⟨f', pf, hf'⟩ := of_fin_cases (@finset.univ α _) (λ x _, hf x),
  convert pf, apply funext, simpa using @hf',
end

lemma iff_fintype [fintype α] {f : α → β → γ} :
  primrec f ↔ ∀ x, primrec (f x) :=
⟨λ h x, (comp₂ h (primrec.const x) id'), of_from_fintype⟩

lemma of_from_fintype' [fintype α] (f : α → β) : primrec f :=
let H : primrec (λ x (_ : unit), f x) := of_from_fintype (λ x, primrec.const _)
 in comp₂ H primrec.id (primrec.const ())

lemma iff_fintype' {δ : Type} [fintype α] [has_uncurry δ β γ] {f : α → δ} :
  primrec f ↔ ∀ x, primrec (f x) := @iff_fintype _ _ _ _ _ _ _ (λ a b, ↿(f a) b)

@[primrec] protected lemma bor : primrec bor := of_from_fintype' _
@[primrec] protected lemma or {P Q : α → Prop} (hP : primrec_pred P) (hQ : primrec_pred Q) :
  primrec_pred (λ x, (P x) ∨ (Q x)) :=
by { classical, simp_rw [← primrec1_iff_primrec_pred', bool.to_bool_or], primrec, }

end finite_branching

section option

@[primrec] lemma option_elim {f : α → option β} {g : α → γ} {h : α → β → γ} :
  primrec f → primrec g → primrec h → primrec (λ x, (f x).elim (g x) (h x)) :=
begin
  rintros ⟨f', pf, hf⟩ ⟨g', pg, hg⟩ ⟨h', ph, hh⟩, replace hh := λ x₁ x₂, hh (x₁, x₂),
  refine ⟨λ x, if f' x = unit_tree.nil then g' x else h' (x.node (f' x).right), _, _⟩,
  { rw tree.primrec.iff_primrec at *, primrec, },
  intro x, simp only [hf, hg, has_uncurry.uncurry, id],
  cases f x, { simp [encode], }, { simpa [encode] using hh _ _, },
end

@[primrec] lemma option_rec {f : α → option β} {g : α → γ} {h : α → β → γ} (hf : primrec f)
  (hg : primrec g) (hh : primrec h) :
  @primrec α γ (α → γ) _ _ _ (λ x : α, @option.rec β (λ _, γ) (g x) (h x) (f x)) :=
by { convert option_elim hf hg hh, ext x, cases f x; refl, }

attribute [primrec] primrec.some

lemma congr_some {f : α → β} : primrec f ↔ primrec (λ x, some (f x)) :=
⟨λ hf, by primrec, λ ⟨f', pf, hf⟩, ⟨_, unit_tree.primrec.right.comp pf, λ _, by { simp [hf], refl, }⟩⟩

lemma congr_some' {γ : Type} [has_uncurry γ α β] {f : γ} :
  primrec f ↔ primrec (λ x, some (↿f x)) := congr_some

@[primrec] lemma option_bind {f : α → option β} {g : α → β → option γ} (hf : primrec f)
  (hg : primrec g) : primrec (λ x, (f x).bind (g x)) :=
by { delta option.bind, delta id_rhs, primrec, }

@[primrec] lemma option_map {f : α → option β} {g : α → β → γ} (hf : primrec f) (hg : primrec g) :
  primrec (λ x, (f x).map (g x)) :=
by { delta option.map, primrec, }

end option

section sum

@[primrec] lemma sum_elim {f : α → β ⊕ γ} {g : α → β → δ} {h : α → γ → δ} :
  primrec f → primrec g → primrec h → primrec (λ x, (f x).elim (g x) (h x)) :=
begin
  rintros ⟨f', pf, hf⟩ ⟨g', pg, hg⟩ ⟨h', ph, hh⟩, simp only [prod.forall] at hg hh,
  refine ⟨λ x, if (f' x).left = unit_tree.nil then g' (x.node (f' x).right)
               else h' (x.node (f' x).right), _, _⟩,
  { rw tree.primrec.iff_primrec at *, primrec, },
  intro x, simp only [hf, encode, tencodable.of_sum, tencodable.to_sum, has_uncurry.uncurry, id],
  cases f x, { simpa using hg _ _, }, { simpa using hh _ _, }
end

@[primrec] lemma sum_inl : primrec (@sum.inl α β) :=
⟨_, unit_tree.primrec.nil.pair unit_tree.primrec.id, by simp [encode]⟩
@[primrec] lemma sum_inr : primrec (@sum.inr α β) :=
⟨_, (unit_tree.primrec.const unit_tree.non_nil).pair unit_tree.primrec.id, by simp [encode]⟩

@[primrec] lemma sum_rec {f : α → β ⊕ γ} {g : α → β → δ} {h : α → γ → δ} (hf : primrec f)
  (hg : primrec g) (hh : primrec h) :
  @primrec α δ (α → δ) _ _ _ (λ x, @sum.rec β γ (λ _, δ) (g x) (h x) (f x)) := sum_elim hf hg hh

@[primrec] lemma sum_get_right : primrec (@sum.get_right α β) :=
by { delta sum.get_right, delta id_rhs, primrec, }
@[primrec] lemma sum_get_left : primrec (@sum.get_left α β) :=
by { delta sum.get_left, delta id_rhs, primrec, }

end sum

section primcodable
variables {α' β' γ' : Type} [primcodable α'] [primcodable β'] [primcodable γ']

instance : primcodable (option α') :=
{ prim := by { simp only [decode], delta tencodable.to_option, delta id_rhs, primrec, } }

instance : primcodable (α' × β') :=
{ prim := by { simp only [decode], primrec, } }

instance : primcodable (α' ⊕ β') :=
{ prim := by { simp only [decode], delta tencodable.to_sum, primrec, } }

def primcodable.of_equiv {β} (α) [primcodable α] (e : β ≃ α) : primcodable β :=
{ prim := by { apply (primcodable.prim α).option_map; primrec, exact of_equiv_symm _, },
  ..tencodable.of_equiv α e, }

end primcodable

section list

@[primrec] lemma list_cases {f : α → list β} {g : α → γ} {h : α → β → list β → γ} :
  primrec f → primrec g → primrec h →
  @primrec α γ (α → γ) _ _ _ (λ x, @list.cases_on β (λ _, γ) (f x) (g x) (h x)) :=
begin
  rintros ⟨f', pf, hf⟩ ⟨g', pg, hg⟩ ⟨h', ph, hh⟩, replace hh := λ x₁ x₂ x₃, hh (x₁, x₂, x₃),
  use λ x, if f' x = unit_tree.nil then g' x else h' (encode (x, (f' x).left, (f' x).right)),
  split, { rw tree.primrec.iff_primrec at *, primrec, },
  intro x, simp only [hf, hg, has_uncurry.uncurry, id],
  cases f x, { simp [encode], }, { simpa [encode] using hh _ _ _, },
end

@[primrec] lemma head' : primrec (@list.head' α) :=
by { delta list.head', delta id_rhs, primrec, }

@[primrec] lemma tail : primrec (@list.tail α) :=
by { delta list.tail, delta id_rhs, primrec, }

end list

section nat

@[primrec] lemma succ : primrec nat.succ :=
⟨_, unit_tree.primrec.nil.pair unit_tree.primrec.id, λ x, by simp [tencodable.encode_succ]⟩

lemma iterate_aux (n : α → unit_tree) (f : α → α) :
  primrec n → primrec f → primrec (λ x, f^[(n x).nodes] x)
| ⟨n', pn, hn⟩ ⟨f', pf, hf⟩ :=
⟨_, unit_tree.primrec.prec pn pf, λ x, begin
 simp only [hn, has_uncurry.uncurry, id, encode],
 induction (encode $ n x).nodes; simp [*, function.iterate_succ'],
end⟩

lemma iterate_aux' {n : α → unit_tree} {f : α → β → β} {g : α → β} (hn : primrec n)
  (hf : primrec f) (hg : primrec g) : primrec (λ x, (f x)^[(decode ℕ (n x)).iget] (g x)) :=
begin
  have := iterate_aux (λ xy, n (prod.fst xy)) (λ xy, (xy.1, f xy.1 xy.2)) (by primrec) (by primrec),
  convert (snd.comp this).comp (primrec.id.pair hg),
  ext x, generalize : g x = y, dsimp only [id, decode],
  induction (n x).nodes with n ih generalizing y, { simp, }, simp [← ih],
end

@[primrec] lemma iterate {n : α → ℕ} {f : α → β → β} {g : α → β} (hn : primrec n)
  (hf : primrec f) (hg : primrec g) : primrec (λ x, (f x)^[n x] (g x)) :=
by simpa using iterate_aux' (primrec.encode.comp hn) hf hg

local attribute [simp] nat.succ_iterate nat.pred_iterate

@[primrec] lemma nodes : primrec unit_tree.nodes :=
by simpa using iterate_aux' primrec.id
    (show primrec (λ _ : unit_tree, nat.succ), by primrec)
    (primrec.const 0)

instance : primcodable ℕ :=
{ prim := primrec.some.comp nodes, }

@[primrec] lemma add : primrec ((+) : ℕ → ℕ → ℕ) :=
by { primrec using (λ x y, nat.succ^[y] x), simp, }

@[primrec] lemma mul : primrec ((*) : ℕ → ℕ → ℕ) :=
by { primrec using (λ x y, (+x)^[y] 0), induction y; simp [iterate_succ', nat.mul_succ, *], }

@[primrec] lemma pred : primrec nat.pred :=
⟨_, unit_tree.primrec.right, λ n, by cases n; refl⟩

@[primrec] lemma tsub : primrec (@has_sub.sub ℕ _) :=
by { primrec using (λ x y, nat.pred^[y] x), simp, }

@[primrec] lemma nat_le : primrec_pred ((≤) : ℕ → ℕ → Prop) :=
by { primrec using (λ x y, x - y = 0), simp, }

end nat

section stack_recursion

variables {base : γ → α → β} {pre₁ pre₂ : γ → unit_tree → unit_tree→  α → α}
  {post : γ → β → β → unit_tree → unit_tree → α → β}

@[primrec] lemma prec_stack_iterate {start : γ → list (unit_tree.iterator_stack α β)}
  (hb : primrec base) (hp₁ : primrec pre₁) (hp₂ : primrec pre₂)
  (hp : primrec post) (hs : primrec start) :
   primrec (λ x : γ, unit_tree.stack_step (base x) (pre₁ x) (pre₂ x) (post x) (start x)) :=
by { delta unit_tree.stack_step, delta id_rhs, primrec, }

@[primrec] lemma tree_stack_rec {start : γ → unit_tree} {arg : γ → α}
  (hb : primrec base) (hp₁ : primrec pre₁) (hp₂ : primrec pre₂)
  (hp : primrec post) (hs : primrec start) (hs' : primrec arg) :
  primrec (λ x, unit_tree.stack_rec (base x) (pre₁ x) (pre₂ x) (post x) (start x) (arg x)) :=
begin
  rw [congr_some],
  primrec using λ x, ((unit_tree.stack_step (base x) (pre₁ x)
    (pre₂ x) (post x))^[5 * (start x).nodes + 1] [sum.inl (start x, arg x, none)])
    .head'.bind sum.get_right,
  rw unit_tree.stack_step_iterate'; refl,
end

lemma ptree_eq : primrec_pred (@eq unit_tree) :=
begin
  suffices : primrec (λ (x y : unit_tree), (x = y : bool)),
  { rw primrec_pred, simp only [primrec, has_uncurry.uncurry] at this, convert this, ext, congr, },
  primrec using λ x y, x.stack_rec (λ y' : unit_tree, (y' = unit_tree.nil : bool))
    (λ _ _ y', y'.left) (λ _ _ y', y'.right)
    (λ b₁ b₂ _ _ y, !(y = unit_tree.nil : bool) && (b₁ && b₂)) y,
  induction x with l r ih₁ ih₂ generalizing y; cases y; simp [*],
end

@[primrec] lemma eq : primrec_pred (@eq α) :=
by { have := ptree_eq, primrec using (λ x y, encode x = encode y), simp, }

end stack_recursion

@[primrec] lemma nat_lt : primrec_pred ((<) : ℕ → ℕ → Prop) :=
by { primrec using (λ x y, x ≤ y ∧ x ≠ y), rw lt_iff_le_and_ne, }

section list

@[primrec] lemma equiv_list : primrec ⇑tencodable.equiv_list :=
⟨_, unit_tree.primrec.id, by simp⟩

@[primrec] lemma equiv_list_symm : primrec ⇑tencodable.equiv_list.symm :=
⟨_, unit_tree.primrec.id, by simp⟩

@[primrec] lemma list_rec {base : δ → α → β} {pre : δ → γ → list γ → α → α}
  {post : δ → β → γ → list γ → α → β} {start : δ → list γ} {arg : δ → α} :
  primrec base → primrec pre → primrec post → primrec start → primrec arg →
  primrec (λ x : δ, (start x).stack_rec (base x) (pre x) (post x) (arg x)) :=
begin
  rintros ⟨base', pb, hb⟩ ⟨pre', ppr, hpr⟩ ⟨post', ppo, hpo⟩ ⟨start', ps, hs⟩ ⟨arg', pa, ha⟩,
  replace hb := λ x₁ x₂, hb (x₁, x₂), replace hpr := λ x₁ x₂ x₃ x₄, hpr (x₁, x₂, x₃, x₄), replace hpo := λ x₁ x₂ x₃ x₄ x₅, hpo (x₁, x₂, x₃, x₄, x₅),
  refine ⟨λ x : unit_tree, (start' x).stack_rec (λ a : unit_tree, base' (x.node a)) default
    (λ l r a, pre' (x.node $ l.node $ r.node $ a))
    (λ _ ih l r a, post' (x.node $ ih.node $ l.node $ r.node a)) (arg' x), _, _⟩,
  { rw tree.primrec.iff_primrec at *, simp_rw pi.default_def, primrec, },
  intro x,
  simp only [tencodable.encode_prod, has_uncurry.uncurry, id] at hb hpr hpo,
  simp only [ha, hs, has_uncurry.uncurry, id, pi.default_def],
  generalize : arg x = y, induction (start x) with hd tl ih generalizing y,
  { simp [tencodable.encode_nil, hb], },
  { simp [tencodable.encode_cons, hpr, hpo, ih], },
end

-- TODO: Given `stack_rec`, if we had a "custom" equation compiler,
-- we could easily automate all these lemmas, because they just involve
-- restating the standard Lean definition in terms of `stack_rec`

@[primrec] lemma foldr {f : γ → α → β → β} {start : γ → β} {ls : γ → list α}
  (hf : primrec f) (hs : primrec start) (hls : primrec ls) :
  primrec (λ x, (ls x).foldr (f x) (start x)) :=
begin
  primrec using (λ x, (ls x).stack_rec (λ _ : unit, (start x)) (λ _ _ _, ())
    (λ ih hd tl _, f x hd ih) ()),
  induction ls x; simp [*],
end

@[primrec] lemma append : primrec ((++) : list α → list α → list α) :=
by { primrec using (λ l₁ l₂, l₁.foldr (λ hd acc, hd :: acc) l₂), induction l₁; simp [*], }

@[primrec] lemma reverse : primrec (@list.reverse α) :=
by { primrec using (λ l, l.foldr (λ hd acc, acc ++ [hd]) []), induction l; simp [*], }

@[primrec] lemma map {f : γ → α → β} {ls : γ → list α} (hf : primrec f) (hls : primrec ls) :
  primrec (λ x, (ls x).map (f x)) :=
by { primrec using (λ x, (ls x).foldr (λ hd acc, f x hd :: acc) []), induction ls x; simp [*], }

@[primrec] lemma all_some : primrec (@list.all_some α) :=
begin
  primrec using (λ l, l.foldr (λ hd' acc', hd'.bind (λ hd, acc'.map (λ acc, hd :: acc))) (some [])),
  induction l with hd, { simp, }, cases hd; simp [*],
end

@[primrec] lemma nth : primrec (@list.nth α) :=
begin
  primrec using (λ l n, l.stack_rec (λ n : ℕ, (@none α)) (λ hd tl n, n.pred)
    (λ ih hd tl n, if n = 0 then some hd else ih) n),
  induction l generalizing n, { refl, }, cases n; simp [*],
end

@[primrec] lemma list_length : primrec (@list.length α) :=
by { primrec using (λ l, l.foldr (λ _ n, n + 1) 0), induction l; simp [*], }

@[primrec] lemma list_foldl {f : γ → β → α → β} {start : γ → β} {ls : γ → list α}
  (hf : primrec f) (hstart : primrec start) (hls : primrec ls) :
  primrec (λ x, (ls x).foldl (f x) (start x)) :=
begin
  primrec using (λ x, (ls x).stack_rec (@id β) (λ hd _ acc, f x acc hd)
    (λ ih hd tl acc, ih) (start x)),
  generalize : start x = y, induction (ls x) generalizing y; simp [*],
end

@[primrec] lemma list_join : primrec (@list.join α) :=
by { primrec using λ l, l.foldr (++) [], induction l; simp [*], }

@[primrec] lemma list_product : primrec (@list.product α β) :=
by { delta list.product, delta list.bind, primrec, }

@[primrec] lemma reduce_option : primrec (@list.reduce_option α) :=
begin
  primrec using λ l, l.foldr (λ hd acc, hd.elim acc (λ hd', hd' :: acc)) [],
  induction l with hd, { simp, }, cases hd; simp [*],
end

@[primrec] lemma filter {f : α → list β} {P : α → β → Prop} [∀ x, decidable_pred (P x)]
  (hf : primrec f) (hP : primrec_pred P) :
  primrec (λ x, (f x).filter (P x)) :=
begin
  primrec using λ x, (f x).foldr (λ hd acc, if P x hd then hd :: acc else acc) [],
  induction f x with hd, { simp, }, simp [*, list.filter],
end

instance {α : Type} [primcodable α] : primcodable (list α) :=
{ prim := by { simp only [decode], primrec, } }

end list

section subtype

@[primrec] lemma subtype_coe {P : α → Prop} [decidable_pred P] : primrec (coe : {x // P x} → α) :=
⟨_, unit_tree.primrec.id, λ _, rfl⟩

lemma of_subtype_coe {P : α → Prop} [decidable_pred P] {f : β → {x // P x}} :
  primrec f ↔ primrec (λ x, (f x : α)) := iff.rfl

@[primrec] lemma subtype_mk {f : α → β} {P : β → Prop} [decidable_pred P] (hP : ∀ x, P (f x))
  (hf : primrec f) : primrec (λ x, subtype.mk (f x) (hP x)) := hf

@[primrec] protected lemma dite {P : α → Prop} [decidable_pred P] {f : ∀ (x : α), P x → β}
  {g : ∀ (x : α), ¬P x → β} : primrec_pred P → primrec (λ x : {a // P a}, f x x.prop) →
  primrec (λ x : {a // ¬P a}, g x x.prop) → primrec (λ x, if H : P x then f x H else g x H)
| ⟨P', pP, hP⟩ ⟨f', pf, hf⟩ ⟨g', pg, hg⟩ :=
⟨λ x, if P' x = encode tt then f' x else g' x, by { rw tree.primrec.iff_primrec at *, primrec, },
begin
  intro x,
  simp only [hP, function.has_uncurry.base_eq_self, tencodable.encode_inj, to_bool_iff],
  split_ifs with H,
  { simp [encode] at hf, simp [hf, H], },
  { simp [encode] at hg, simp [hg, H], }
end⟩

def subtype_primcodable {α : Type} [primcodable α] {P : α → Prop} [decidable_pred P]
  (hP : primrec_pred P) : primcodable {x // P x} :=
{ prim := by { simp only [decode], primrec, } }

section vector

instance {n} {α : Type} [primcodable α] : primcodable (vector α n) :=
subtype_primcodable (by primrec)

@[primrec] lemma vector_mk {n} {f : α → list β} (P : ∀ x, (f x).length = n) (hf : primrec f) :
  primrec (λ x, (⟨f x, P x⟩ : vector β n)) := subtype_mk P hf

@[primrec] lemma vector_to_list {n} : primrec (@vector.to_list α n) := subtype_coe

end vector

section fin

instance {n} : primcodable (fin n) :=
@@primcodable.of_equiv _ (subtype_primcodable (by primrec)) fin.equiv_subtype

@[primrec] lemma fin_mk {n} {f : α → ℕ} (P : ∀ x, f x < n) (hf : primrec f) :
  primrec (λ x, (⟨f x, P x⟩ : fin n)) := hf

@[primrec] lemma fin_coe {n} : primrec (coe : fin n → ℕ) :=
⟨_, unit_tree.primrec.id, λ _, rfl⟩

@[primrec] lemma vector_nth {n} : primrec (@vector.nth α n) :=
begin
  rw congr_some',
  primrec using (λ xn, xn.1.to_list.nth xn.2),
  cases xn with x m,
  simp [has_uncurry.uncurry, vector.nth_eq_nth_le, list.some_nth_le_eq],
end

@[primrec] lemma vector_map {n} {l : α → vector β n} {f : α → β → γ}
  (hl : primrec l) (hf : primrec f) : primrec (λ x, (l x).map (f x)) :=
by { primrec using λ x, subtype.mk ((l x).to_list.map (f x)) (by simp), cases l x, refl, }

lemma of_fn {n : ℕ} {f : fin n → α → β} (hf : ∀ i, primrec (f i)) :
  primrec (λ x, vector.of_fn (λ i, f i x)) :=
begin
  have hf' : primrec f := of_from_fintype hf,
  primrec using λ x, (vector.of_fn id).map (λ i, f i x),
  ext, simp,
end

@[primrec] lemma vector_head {n} : primrec (@vector.head α n) :=
by { rw congr_some, simp_rw ← vector.head'_to_list, primrec, }

@[primrec] lemma vector_tail {n} : primrec (@vector.tail α n) :=
by { primrec using λ l, subtype.mk l.to_list.tail (by simp), rcases l with ⟨_|_, _⟩; refl, }

@[primrec] lemma vector_cons {n} : primrec (@vector.cons α n) :=
by { primrec using λ x v, ⟨x :: v.to_list, by simp⟩, cases v, refl, }

end fin

end subtype

section nat_rec

@[primrec] lemma repeat : primrec (@list.repeat α) :=
by { primrec using λ x n, (list.cons x)^[n] [], induction n; simp [iterate_succ', *], }

def _root_.nat.elim {C : Sort*} : C → (ℕ → C → C) → ℕ → C := @nat.rec (λ _, C)
@[simp] lemma _root_.nat.elim_zero {C : Sort*} (base : C) (ih : ℕ → C → C) :
  nat.elim base ih 0 = base := rfl
@[simp] lemma _root_.nat.elim_succ {C : Sort*} (base : C) (ih : ℕ → C → C) (n : ℕ) :
  nat.elim base ih (n + 1) = ih n (nat.elim base ih n) := rfl

@[primrec] lemma nat_stack_rec {n : γ → ℕ} {base : γ → α → β} {pre : γ → ℕ → α → α} {post : γ → β → ℕ → α → β}
  {arg : γ → α}  (hn : primrec n) (hb : primrec base) (hpr : primrec pre) (hpo : primrec post)
  (harg : primrec arg) : primrec (λ x, (n x).stack_rec (base x) (pre x) (post x) (arg x)) :=
begin
  primrec using λ x, (list.repeat () $ n x).stack_rec (base x) (λ _ tl y, pre x tl.length y)
    (λ ih _ tl y, post x ih tl.length y) (arg x),
  generalize : arg x = y, induction n x with n ih generalizing y,
  { simp, }, { simp [ih], }
end

@[primrec] lemma nat_elim {n : γ → ℕ} {base : γ → β} {ih : γ → ℕ → β → β} (hn : primrec n)
  (hb : primrec base) (hih : primrec ih) : primrec (λ x, (n x).elim (base x) (ih x)) :=
begin
  primrec using λ x, (n x).stack_rec (λ _ : unit, base x) (λ _, id) (λ ih' n' _, ih x n' ih') (),
  induction n x with n ih; simp [*],
end

@[primrec] lemma height_le_list : primrec unit_tree.height_le_list :=
begin
  primrec using λ n, n.elim [unit_tree.nil]
   (λ n ih, unit_tree.nil :: ((ih ×ˢ ih).map $ λ x, x.1.node x.2)),
  induction n; simp [*, unit_tree.height_le_list],
end

def _root_.tencodable.height_le (α : Type) [tencodable α] (n : ℕ) : list α :=
((unit_tree.height_le_list n).map (decode α)).reduce_option

@[primrec] lemma height_le {α : Type} [primcodable α] : primrec (tencodable.height_le α) :=
by { delta tencodable.height_le, primrec, }

lemma _root_.tencodable.mem_height_le {n : ℕ} {x : α}
  (h : (encode x).height ≤ n) : x ∈ tencodable.height_le α n :=
begin
  simp [tencodable.height_le, list.reduce_option],
  exact ⟨encode x, h, tencodable.encodek _⟩,
end

lemma filter_eq_eq_repeat_count {α : Type*} [decidable_eq α] (l : list α) (y : α) :
  l.filter (=y) = list.repeat y (l.count y) :=
begin
  induction l with hd tl ih, { refl, },
  by_cases H : hd = y,
  { simpa [H], }, { simpa [H, list.count_cons_of_ne (ne.symm H)], }
end

lemma _root_.list.repeat_head' {α : Type*} (x : α) (n : ℕ) (hn : n ≠ 0) :
  (list.repeat x n).head' = some x :=
by { cases n, { contradiction, }, refl, }

/-- A function is primitive recursive if its graph is and if the output is
  bounded by a primitive recursive function -/
lemma primrec_of_primrec_graph {β : Type} [primcodable β] {f : α → β}
  (hf : primrec_pred (λ x y, y = f x)) (g : α → ℕ) (hg : primrec g)
  (hfg : ∀ x, (encode (f x)).height ≤ g x) : primrec f :=
begin
  classical,
  rw congr_some,
  primrec using λ x, ((tencodable.height_le β (g x)).filter (λ y, y = (f x))).head',
  rw [filter_eq_eq_repeat_count _ (f x), list.repeat_head'],
  rw ← pos_iff_ne_zero,
  simpa using (tencodable.mem_height_le (hfg x)),
end

end nat_rec

end primrec

namespace nat
open vector

local attribute [primrec] primrec.of_fn

inductive primrec' : ∀ {n}, (vector ℕ n → ℕ) → Prop
| zero : @primrec' 0 (λ _, 0)
| succ : @primrec' 1 (λ v, succ v.head)
| nth {n} (i : fin n) : primrec' (λ v, v.nth i)
| comp {m n f} (g : fin n → vector ℕ m → ℕ) :
  primrec' f → (∀ i, primrec' (g i)) →
  primrec' (λ a, f (of_fn (λ i, g i a)))
| prec {n f g} : @primrec' n f → @primrec' (n+2) g →
  primrec' (λ v : vector ℕ (n+1),
    v.head.elim (f v.tail) (λ y IH, g (y ::ᵥ IH ::ᵥ v.tail)))

lemma primrec'.to_primrec {n} {f : vector ℕ n → ℕ} (hf : primrec' f) : primrec f :=
by induction hf; primrec

protected def primrec (f : ℕ → ℕ) : Prop := primrec' (λ x : vector ℕ 1, f x.head)

lemma nat.primrec.to_primrec {f : ℕ → ℕ} (hf : nat.primrec f) : primrec f :=
by simpa using (primrec'.to_primrec hf).comp (show primrec (λ n, n ::ᵥ vector.nil), by primrec)

namespace primrec'

theorem of_eq {n} {f g : vector ℕ n → ℕ}
  (hf : primrec' f) (H : ∀ i, f i = g i) : primrec' g :=
(funext H : f = g) ▸ hf

theorem const {n} : ∀ m, @primrec' n (λ v, m)
| 0     := zero.comp fin.elim0 (λ i, i.elim0)
| (m+1) := succ.comp _ (λ i, const m)

theorem head {n : ℕ} : @primrec' n.succ head :=
(nth 0).of_eq $ λ v, by simp [nth_zero]

theorem tail {n f} (hf : @primrec' n f) : @primrec' n.succ (λ v, f v.tail) :=
(hf.comp _ (λ i, @nth _ i.succ)).of_eq $
λ v, by rw [← of_fn_nth v.tail]; congr; funext i; simp

-- TODO: Finish this section

end primrec'

end nat
