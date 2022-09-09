import computability.computability_tactic
import computability.primrec.stack_recursion

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

section tree

@[primrec] lemma tree_left : primrec (@tree.left unit) := ⟨_, tree.primrec.left, λ _, rfl⟩
@[primrec] lemma tree_right : primrec (@tree.right unit) := ⟨_, tree.primrec.right, λ _, rfl⟩

lemma tree_node_eq : ∀ (x : unit × tree unit × tree unit), (encode x).right = ↿(@tree.node unit) x
| ((), a, b) := rfl
@[primrec] lemma tree_node : primrec (@tree.node unit) := ⟨_, tree.primrec.right, tree_node_eq⟩

lemma eq_nil : primrec_pred (λ y : tree unit, y = tree.nil) :=
⟨_, tree.primrec.id.ite (tree.primrec.const $ encode tt) (tree.primrec.const $ encode ff),
λ x, by cases x; simp [has_uncurry.uncurry]⟩

end tree

section bool

@[primrec] lemma coe_sort : primrec_pred (λ b : bool, (b : Prop)) :=
by { rw [← primrec1_iff_primrec_pred], simpa using primrec.id, }

@[primrec] lemma to_bool {P : α → Prop} [decidable_pred P] (hP : primrec_pred P) :
  primrec (λ x, to_bool (P x)) :=
by { rw [← primrec1_iff_primrec, primrec1_iff_primrec_pred'], exact hP, }

@[primrec] lemma band : primrec (&&) :=
by { primrec using (λ b₁ b₂, if b₁ then b₂ else ff), cases b₁; simp, }

@[primrec] lemma bnot : primrec bnot :=
by { primrec using (λ b, if b then ff else tt), cases b; refl, }

@[primrec] lemma and {P₁ P₂ : α → Prop} (h₁ : primrec_pred P₁) (h₂ : primrec_pred P₂) :
  primrec_pred (λ x, (P₁ x) ∧ (P₂ x)) :=
by { classical, simp_rw [← primrec1_iff_primrec_pred', bool.to_bool_and], primrec, }

@[primrec] lemma not {P : α → Prop} (h : primrec_pred P) : primrec_pred (λ x, ¬(P x)) :=
by { classical, simp_rw [← primrec1_iff_primrec_pred', bool.to_bool_not], primrec, }

lemma eq_const_aux : ∀ (x : tree unit), primrec_pred (=x)
| tree.nil := eq_nil
| (tree.node () a b) :=
begin
  have := (eq_const_aux a).comp tree_left, have := (eq_const_aux b).comp tree_right, have := eq_nil,
  primrec using (λ y, ¬(y = tree.nil) ∧ y.left = a ∧ y.right = b),
  cases y; simp,
end

end bool

@[primrec] lemma eq_const {f : α → β} (hf : primrec f) (y : β) :
  primrec_pred (λ x, (f x) = y) :=
by simpa using (eq_const_aux (encode y)).comp hf

@[primrec tree.rec] lemma tree_cases {f : α → tree unit} {g : α → β}
  {h : α → unit → tree unit → tree unit → β} (hf : primrec f) (hg : primrec g) (hh : primrec h) :
  @primrec α β (α → β) _ _ _ (λ x, @tree.cases_on unit (λ _, β) (f x) (g x) (h x)) :=
begin
  primrec using (λ x, if f x = tree.nil then g x else h x () (f x).left (f x).right),
  rcases f x with _|⟨U, _, _⟩, { simp, }, simp [punit_eq_star U],
end

namespace option

@[primrec] lemma option_elim {f : α → option β} {g : α → γ} {h : α → β → γ} :
  primrec f → primrec g → primrec h → primrec (λ x, (f x).elim (g x) (h x)) :=
begin
  rintros ⟨f', pf, hf⟩ ⟨g', pg, hg⟩ ⟨h', ph, hh⟩, replace hh := λ x₁ x₂, hh (x₁, x₂),
  refine ⟨λ x, if f' x = tree.nil then g' x else h' (tree.node () x (f' x).right), _, _⟩,
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
⟨λ hf, by primrec, λ ⟨f', pf, hf⟩, ⟨_, tree.primrec.right.comp pf, λ _, by { simp [hf], refl, }⟩⟩

@[primrec] lemma option_bind {f : α → option β} {g : α → β → option γ} (hf : primrec f)
  (hg : primrec g) : primrec (λ x, (f x).bind (g x)) :=
by { primrec using (λ x, (f x).elim none (g x)), cases f x; simp, }

@[primrec] lemma option_map {f : α → option β} {g : α → β → γ} (hf : primrec f) (hg : primrec g) :
  primrec (λ x, (f x).map (g x)) :=
by { primrec using (λ x, (f x).bind (λ y, some (g x y))), cases f x; simp, }

end option

section sum

/-- TODO: Move -/
@[simp] lemma _root_.function.has_uncurry.base_eq_self {α β : Type*} (f : α → β) :
  ↿f = f := rfl

@[primrec] lemma sum_elim {f : α → β ⊕ γ} {g : α → β → δ} {h : α → γ → δ} :
  primrec f → primrec g → primrec h → primrec (λ x, (f x).elim (g x) (h x)) :=
begin
  rintros ⟨f', pf, hf⟩ ⟨g', pg, hg⟩ ⟨h', ph, hh⟩, simp only [prod.forall] at hg hh,
  refine ⟨λ x, if (f' x).left = tree.nil then g' (tree.node () x (f' x).right)
               else h' (tree.node () x (f' x).right), _, _⟩,
  { rw tree.primrec.iff_primrec at *, primrec, },
  intro x, simp only [hf, encode, tencodable.of_sum, tencodable.to_sum, has_uncurry.uncurry, id],
  cases f x, { simpa using hg _ _, }, { simpa using hh _ _, }
end

@[primrec] lemma sum_inl : primrec (@sum.inl α β) :=
⟨_, tree.primrec.nil.pair tree.primrec.id, by simp [encode]⟩
@[primrec] lemma sum_inr : primrec (@sum.inr α β) :=
⟨_, (tree.primrec.const tree.non_nil).pair tree.primrec.id, by simp [encode]⟩

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

@[primrec list.rec] lemma list_cases {f : α → list β} {g : α → γ} {h : α → β → list β → γ} :
  primrec f → primrec g → primrec h →
  @primrec α γ (α → γ) _ _ _ (λ x, @list.cases_on β (λ _, γ) (f x) (g x) (h x)) :=
begin
  rintros ⟨f', pf, hf⟩ ⟨g', pg, hg⟩ ⟨h', ph, hh⟩, replace hh := λ x₁ x₂ x₃, hh (x₁, x₂, x₃),
  use λ x, if f' x = tree.nil then g' x else h' (encode (x, (f' x).left, (f' x).right)), split,
  { rw tree.primrec.iff_primrec at *, primrec, },
  intro x, simp only [hf, hg, has_uncurry.uncurry, id],
  cases f x, { simp [encode], }, { simpa [encode] using hh _ _ _, },
end

section stack_recursion
variables {base : γ → α → β} {pre₁ pre₂ : γ → tree unit → α → α}
  {post : γ → β → β → tree unit → α → β}

@[primrec] lemma prec_stack_iterate {start : γ → list (tree.iterator_stack α β)}
  (hb : primrec base) (hp₁ : primrec pre₁) (hp₂ : primrec pre₂)
  (hp : primrec post) (hs : primrec start) :
   primrec (λ x : γ, tree.stack_step (base x) (pre₁ x) (pre₂ x) (post x) (start x)) :=
by { delta tree.stack_step, delta id_rhs,  }

end stack_recursion

end list

end primrec
