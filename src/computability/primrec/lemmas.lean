/-
Copyright (c) 2022 Mario Carneiro, Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Praneeth Kolichala
-/
import computability.computability_tactic2
import computability.primrec.stack_recursion

/-!
# Lemmas about primitive recursive functions

In this file, we prove a large family of basic functions on lists and trees
primitive recursive.
-/

open tencodable (encode decode)
open function

variables {α β γ δ ε : Type} [tencodable α]
  [tencodable β] [tencodable γ] [tencodable δ] [tencodable ε]

namespace primrec

@[primrec] lemma prod_mk : primrec (@prod.mk α β) := primrec.id

@[primrec] lemma cons : primrec (@list.cons α) := primrec.id

@[primrec] protected lemma encode : primrec (@encode α _) := primrec.id

protected lemma iff_comp_encode {f : α → β} : primrec f ↔ primrec (λ x, encode (f x)) := iff.rfl

attribute [primrec] primcodable.prim

@[primrec] lemma prod_rec {f : α → β × γ} {g : α → β → γ → δ} (hf : primrec f) (hg : primrec g) :
  @primrec α δ (α → δ) _ _ _ (λ x, @prod.rec β γ (λ _, δ) (g x) (f x)) :=
by { primrec using (λ x, g x (f x).1 (f x).2), cases f x; refl, }

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

@[primrec] lemma and {P₁ P₂ : α → Prop} (h₁ : primrec_pred P₁) (h₂ : primrec_pred P₂) :
  primrec_pred (λ x, (P₁ x) ∧ (P₂ x)) :=
by { classical, simp_rw [← primrec1_iff_primrec_pred', bool.to_bool_and], primrec, }

@[primrec] lemma not {P : α → Prop} (h : primrec_pred P) : primrec_pred (λ x, ¬(P x)) :=
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

@[primrec] lemma option_bind {f : α → option β} {g : α → β → option γ} (hf : primrec f)
  (hg : primrec g) : primrec (λ x, (f x).bind (g x)) :=
by { delta option.bind, delta id_rhs, primrec, }

@[primrec] lemma option_map {f : α → option β} {g : α → β → γ} (hf : primrec f) (hg : primrec g) :
  primrec (λ x, (f x).map (g x)) :=
by { delta option.map, primrec, }

end option

section sum

/-- TODO: Move -/
@[simp] lemma _root_.function.has_uncurry.base_eq_self {α β : Type*} (f : α → β) :
  ↿f = f := rfl

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

/- TODO: Move -/
@[simp] lemma _root_.nat.succ_iterate (n m : ℕ) : nat.succ^[m] n = n + m :=
by induction m; simp [nat.add_succ, function.iterate_succ', *]

@[primrec] lemma nodes : primrec unit_tree.nodes :=
by simpa using iterate_aux' primrec.id
    (show primrec (λ _ : unit_tree, nat.succ), by primrec)
    (primrec.const 0)

@[primrec] lemma add : primrec ((+) : ℕ → ℕ → ℕ) :=
by { primrec using (λ x y, nat.succ^[y] x), simp, }

@[primrec] lemma mul : primrec ((*) : ℕ → ℕ → ℕ) :=
by { primrec using (λ x y, (+x)^[y] 0), induction y; simp [function.iterate_succ', nat.mul_succ, *], }

@[primrec] lemma pred : primrec nat.pred :=
⟨_, unit_tree.primrec.right, λ n, by cases n; refl⟩

end nat

section stack_recursion

variables {base : γ → α → β} {pre₁ pre₂ : γ → unit_tree → unit_tree→  α → α}
  {post : γ → β → β → unit_tree → unit_tree → α → β}

@[primrec] lemma prec_stack_iterate {start : γ → list (unit_tree.iterator_stack α β)}
  (hb : primrec base) (hp₁ : primrec pre₁) (hp₂ : primrec pre₂)
  (hp : primrec post) (hs : primrec start) :
   primrec (λ x : γ, unit_tree.stack_step (base x) (pre₁ x) (pre₂ x) (post x) (start x)) :=
by { delta unit_tree.stack_step, delta id_rhs, sorry { primrec, }, }

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

section list

@[primrec] lemma ptree_equiv_list : primrec ⇑tencodable.equiv_list :=
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

end list

end primrec
