/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import set_theory.game.state
import algebra.pi_instances
import tactic.tidy

/-!

-/

def finset.join {α : Type*} [decidable_eq α] (s : finset (finset α)) : finset α :=
s.bind id

structure geometry :=
(boxes : Type)
[decidable_boxes : decidable_eq boxes]
(edges : Type)
[decidable_edges : decidable_eq edges]
(adj : boxes → finset edges)  -- perhaps this should be an embedding

attribute [instance] geometry.decidable_boxes geometry.decidable_edges

@[simps]
def square : geometry :=
{ boxes := ℤ × ℤ,
  edges := (ℤ × ℤ) ⊕ (ℤ × ℤ), -- horizontal and vertical edges
  adj := λ x, [sum.inl x, sum.inr x, sum.inl (x + (0,1)), sum.inr (x + (1,0))].to_finset }

variables (G : geometry)

@[derive decidable_eq]
structure prelayout :=
(boxes : finset G.boxes)
(edges : finset G.edges)
(edges_in_boxes : ∀ e ∈ edges, ∃ f ∈ boxes, e ∈ G.adj f)

@[derive decidable_eq]
structure layout extends prelayout G :=
(boxes_incomplete : ∀ f ∈ boxes, ∃ e ∈ G.adj f, e ∉ edges)

variables {G}

namespace prelayout

def remaining_edges (L : prelayout G) : finset G.edges :=
(L.boxes.image G.adj).bind id \ L.edges

@[simp]
lemma mem_remaining_edges (L : prelayout G) (e : G.edges) :
  e ∈ L.remaining_edges ↔ ∃ f ∈ L.boxes, e ∈ G.adj f ∧ e ∉ L.edges :=
begin
  dsimp [remaining_edges],
  simp only [exists_prop, id.def, finset.mem_bind, finset.mem_sdiff, finset.mem_image],
  split,
  { rintros ⟨⟨es, ⟨⟨f, ⟨fm, rfl⟩⟩, em⟩⟩, nm⟩,
    tauto, }, -- Perhaps tauto should use the `rfl` trick?
  { tauto, }
end

end prelayout

namespace layout

abbreviation remaining_edges (L : layout G) : finset G.edges :=
L.to_prelayout.remaining_edges

end layout

namespace prelayout

def discard_complete_boxes (L : prelayout G) : layout G × finset G.boxes :=
begin
  let boxes := L.boxes.filter (λ f, ∃ e ∈ G.adj f, e ∉ L.edges),
  let discarded_boxes := L.boxes \ boxes,
  refine ⟨_, discarded_boxes⟩,
  let edges := L.edges.filter (λ e, ∃ f ∈ boxes, e ∈ G.adj f),
  refine_struct { boxes := boxes, edges := edges, .. },
  { intros e H,
    simp only [exists_prop, finset.mem_filter] at H,
    simp only [exists_prop, finset.mem_filter],
    exact H.2, },
  { intros f H,
    simp only [exists_prop, finset.mem_filter] at H,
    -- This could be improved:
    rcases H with ⟨fm, ⟨e, ⟨m, nm⟩⟩⟩,
    refine ⟨e, m, _⟩,
    simp only [not_exists, and_imp, exists_prop, not_and, finset.mem_filter, exists_imp_distrib],
    intro m',
    exfalso,
    exact nm m', },
end

@[simp]
lemma discard_complete_boxes_remaining_edges (L : prelayout G) :
  L.discard_complete_boxes.1.remaining_edges = L.remaining_edges :=
begin
  ext,
  simp only [exists_prop, mem_remaining_edges],
  split,
  { simp only [and_imp, exists_imp_distrib],
    intros f fm am anm,
    use f,
    split,
    { sorry, }, -- should be easy
    { split,
      { exact am, },
      { sorry } } }, -- the work is here
  { simp only [and_imp, exists_imp_distrib],
    intros f fm am anm,
    use f,
    split,
    { apply (finset.mem_filter).2,
      tauto, },
    { split,
      { exact am, },
      sorry, } } -- should be easy
end

end prelayout

namespace layout

def nz : ℕ ↪ ℤ := ⟨λ n, n, (by tidy)⟩
def nnzz : ℕ × ℕ ↪ ℤ × ℤ := function.embedding.prod_congr nz nz

def rectangular (x y : ℕ) : layout square :=
{ boxes := ((finset.range x).product (finset.range y)).map nnzz,
  edges := ∅,
  edges_in_boxes := by tidy,
  boxes_incomplete := λ f m, ⟨sum.inl f, ⟨(by simp), (by tidy)⟩⟩ }


def add_edge_aux (L : layout G) {e : G.edges} (h : e ∈ L.remaining_edges) : prelayout G :=
{ boxes := L.boxes,
  edges := insert e L.edges,
  edges_in_boxes := sorry, }

@[simp]
lemma add_edge_aux_remaining_edges (L : layout G) {e : G.edges} (h : e ∈ L.remaining_edges) :
  (L.add_edge_aux h).remaining_edges = L.remaining_edges.erase e :=
sorry

/-- Return the new dots-and-boxes layout, along with the set of boxes which were completed. -/
def add_edge (L : layout G) {e : G.edges} (h : e ∈ L.remaining_edges) :
  layout G × finset G.boxes :=
(L.add_edge_aux h).discard_complete_boxes

@[simp]
lemma add_edge_remaining_edges (L : layout G) {e : G.edges} (h : e ∈ L.remaining_edges) :
  (L.add_edge h).1.remaining_edges = L.remaining_edges.erase e :=
by simp [add_edge]

@[simp]
lemma add_edge_remaining_edges_card_lt (L : layout G) {e : G.edges} (h : e ∈ L.remaining_edges) :
  (L.add_edge h).1.remaining_edges.card < L.remaining_edges.card :=
begin
  simp only [add_edge_remaining_edges],
  exact finset.card_erase_lt_of_mem h,
end

@[simp]
lemma add_edge_remaining_edges_card (L : layout G) {e : G.edges} (h : e ∈ L.remaining_edges) :
  (L.add_edge h).1.remaining_edges.card = L.remaining_edges.card - 1 :=
begin
  simp only [add_edge_remaining_edges],
  rw finset.card_erase_of_mem h,
  refl,
end


-- section inductive_type

-- /- We could alternatively define an inductive type here... -/

-- inductive with_edge_sequence : layout G → layout G → Type
-- | single {L : layout G} {e : G.edges} (h : e ∈ L.remaining_edges) : with_edge_sequence L (L.add_edge h).1
-- | cons {L L' : layout G}
--   {e : G.edges} (h : e ∈ L'.remaining_edges) (S : with_edge_sequence L L') : with_edge_sequence L (L'.add_edge h).1

-- def with_edge_sequence.edges_list {L : layout G} : Π L', with_edge_sequence L L' → list G.edges
-- | _ (@with_edge_sequence.single _ _ e _) := [e]
-- | L' (@with_edge_sequence.cons _ L L'' e _ S) := e :: with_edge_sequence.edges_list L'' S

-- def edge_sequence (L : layout G) : Type := Σ L', with_edge_sequence L L'

-- instance fintype_edge_sequence (L : layout G) : fintype (L.edge_sequence) := sorry

-- def add_edge_sequence_boxes : ∀ {L L' : layout G}, with_edge_sequence L L' → finset G.boxes
-- | L _ (with_edge_sequence.single h) := (L.add_edge h).2
-- | _ _ (@with_edge_sequence.cons _ L L' e h S) := add_edge_sequence_boxes S ∪ (L'.add_edge h).2

-- def add_edge_sequence (L : layout G) : edge_sequence L → layout G × finset G.boxes
-- | ⟨L', S⟩ := ⟨L', add_edge_sequence_boxes S⟩

-- end inductive_type

section list_with_predicate

def fold_condition {α β : Type} {P : α → β → Prop} (o : Π a b, P a b → α) : Π (a : α) (bs : list β), Prop
| a [] := true
| a (b :: bs) := ∃ (h : P a b), fold_condition (o a b h) bs

def edges_admissible (L : layout G) (edges : list G.edges) : Prop :=
fold_condition (λ (L : layout G) (e : G.edges) (h : e ∈ L.remaining_edges), (L.add_edge h).1) L edges

def add_admissible_edges : Π (L : layout G) (edges : list G.edges) (S : edges_admissible L edges), layout G × list (finset G.boxes)
| L [] _ := (L, ∅)
| L (e :: es) Q :=
  begin
    set P := by { apply @layout.add_edge _ L e, cases Q, exact Q_w, },
    set P' := by { apply @add_admissible_edges P.1 es, cases Q, exact Q_h, },
    exact (P'.1, P.2 :: P'.2)
  end

lemma remaining_edges_add_admissible_edges_card_le (L : layout G) (edges : list G.edges) (S : edges_admissible L edges) :
  (L.add_admissible_edges edges S).1.remaining_edges.card ≤ L.remaining_edges.card :=
begin
  induction edges generalizing L,
  { exact le_refl _, },
  { dsimp [add_admissible_edges],
    apply le_trans,
    apply edges_ih,
    apply le_of_lt,
    apply add_edge_remaining_edges_card_lt, }
end

structure edge_sequence' (L : layout G) : Type :=
(edges : list G.edges)
(admissible : edges_admissible L edges)

def edge_sequence'_to_fun (L : layout G) (S : L.edge_sequence') :
  (unit ⊕ (Σ' (e : G.edges) (h : e ∈ L.remaining_edges), (L.add_edge h).1.edge_sequence')) :=
match S.edges, S.admissible with
| [], _ := sum.inl unit.star
| (e :: es), Q := sum.inr ⟨e, ⟨begin cases Q, exact Q_w, end, begin refine { edges := es, .. }, cases Q, exact Q_h, end⟩⟩
end

def edge_sequence'_inv_fun (L : layout G) : Π (S : unit ⊕ (Σ' (e : G.edges) (h : e ∈ L.remaining_edges), (L.add_edge h).1.edge_sequence')), L.edge_sequence'
| (sum.inl punit.star) := { edges := [], admissible := sorry, }
| (sum.inr ⟨e, ⟨h, S⟩⟩) := { edges := e :: S.edges, admissible := sorry, }

def edge_sequence'_equiv (L : layout G) :
  L.edge_sequence' ≃
    (unit ⊕ (Σ' (e : G.edges) (h : e ∈ L.remaining_edges), (L.add_edge h).1.edge_sequence')) :=
{ to_fun := edge_sequence'_to_fun L,
  inv_fun := edge_sequence'_inv_fun L,
  left_inv := sorry,
  right_inv := sorry, }.

instance finset.to_set.fintype {α : Type*} (s : finset α) : fintype (s.to_set) :=
fintype.of_finset s $ λ _, iff.rfl

def sigma_finset_to_set_equiv_psigma_mem
  {α : Type*} (s : finset α) (Z : Π (a : α), a ∈ s → Type*) :
  (Σ (a : ↥(finset.to_set s)), Z a.1 a.2) ≃ Σ' (a : α) (h : a ∈ s), Z a h :=
{ to_fun := λ p, ⟨p.1.1, ⟨p.1.2, p.2⟩⟩,
  inv_fun := λ p, ⟨⟨p.1, p.2.1⟩, p.2.2⟩,
  left_inv := by { rintros ⟨⟨_, _⟩, _⟩, refl },
  right_inv := by { rintros ⟨_, ⟨_, _⟩⟩, refl, } }.

def fintype_sigma_mem_finset {α : Type*} (s : finset α) (Z : Π a (h : a ∈ s), Type*)
  [F : ∀ a (h : a ∈ s), fintype (Z a h)] : fintype (Σ' a (h : a ∈ s), Z a h) :=
fintype.of_equiv (Σ a : s.to_set, Z a.1 a.2) (sigma_finset_to_set_equiv_psigma_mem _ _)

/-- This is a ridiculously convoluted statement, tuned to what we're faced with here... -/
def fintype_edge_sequence'_aux {α : Type*} {W : α → Type*} {Y : α → Type*} {Z : α → Type*}
  (f : Π a, finset (Z a))
  (n : Π {a b} (h : b ∈ f a), α)
  (w : α → ℕ) (h : ∀ {a b} (h : b ∈ f a), w (n h) < w a)
  (e : Π a, W a ≃ Y a ⊕ (Σ' b (h : b ∈ f a), W (n h)))
  [∀ a, fintype (Y a)] :
  Π (a : α), fintype (W a) | a :=
begin
  have : fintype (Y a ⊕ Σ' (b : Z a) (h : b ∈ f a), W (n h)),
  { apply @fintype.sum (Y a) _ (by apply_instance) _,
    apply @fintype_sigma_mem_finset (Z a) _ (λ a h, W (n h)) (λ a h, fintype_edge_sequence'_aux (n h)), },
  resetI,
  apply fintype.of_equiv _ (e a).symm,
end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf w⟩], dec_tac := `[solve_by_elim]}

instance fintype_edge_sequence' (L : layout G) : fintype (L.edge_sequence') :=
fintype_edge_sequence'_aux
  (λ L : layout G, L.remaining_edges)
  (λ L e h, (L.add_edge h).1)
  (λ L : layout G, L.remaining_edges.card)
  add_edge_remaining_edges_card_lt
  edge_sequence'_equiv
  L

@[derive fintype]
def edge_sequence (L : layout G) : Type :=
{ S : edge_sequence' L //
  S.edges ≠ [] ∧
  (L.add_admissible_edges S.edges S.admissible).2.reverse.tail.all (λ C, C ≠ ∅) ∧
  ((L.add_admissible_edges S.edges S.admissible).2.reverse.head = ∅ ∨ L.remaining_edges \ S.edges.to_finset = ∅) }

def add_edge_sequence (L : layout G) (S : edge_sequence L) : layout G × list (finset G.boxes) :=
L.add_admissible_edges S.1.edges S.1.admissible

lemma remaining_edges_add_edge_sequence_card_lt (L : layout G) (S : edge_sequence L) :
  (L.add_edge_sequence S).1.remaining_edges.card < L.remaining_edges.card :=
begin
  rcases S with ⟨⟨edges, admissible⟩, ⟨nonempty, _, _⟩⟩,
  cases edges with e es,
  { simp at nonempty, cases nonempty, },
  { dsimp [add_edge_sequence, add_admissible_edges],
    apply lt_of_le_of_lt,
    apply remaining_edges_add_admissible_edges_card_le,
    apply add_edge_remaining_edges_card_lt, }
end

end list_with_predicate

end layout

open pgame


def with_scoring (α : Type) : Type := α ⊕ (ℕ × ℕ)

class has_scoring (α : Type) :=
(score : α → ℕ × ℕ)

def score {α : Type} [has_scoring α] (a : α) : ℕ × ℕ :=
has_scoring.score a

instance state_with_scoring (α : Type) [decidable_eq α] [pgame.state α] [has_scoring α] : state (with_scoring α) :=
{ turn_bound := λ s, match s with
  | (sum.inl a) := state.turn_bound a + (score a).1 + (score a).2
  | (sum.inr (L, R)) := L + R
  end,
  L := λ s, match s with
  | (sum.inl a) := let L := state.L a in if L = ∅ then finset.singleton (sum.inr (score a - (1, 0))) else L.map (function.embedding.inl)
  | (sum.inr (L, R)) := if 0 < L then finset.singleton (sum.inr (L - 1, R)) else ∅
  end,
  R := λ s, match s with
  | (sum.inl a) := let R := state.R a in if R = ∅ then finset.singleton (sum.inr (score a - (0, 1))) else R.map (function.embedding.inl)
  | (sum.inr (L, R)) := if 0 < R then finset.singleton (sum.inr (L, R - 1)) else ∅
  end,
  left_bound := sorry,
  right_bound := sorry,
}

namespace dots_and_boxes

/--
A dots and boxes board consists of:
* `scores : ℕ × ℕ`, representing the number of claimed boxes for each player so far,
* `layout : layout square`, describing the remaining boxes and edges adjacent to them.
. -/
@[derive decidable_eq]
structure board :=
(scores : ℕ × ℕ)
(layout : layout square)

namespace board

@[derive fintype]
def moves (G : board) : Type := G.layout.edge_sequence
def move_left (G : board) (m : G.moves) : board :=
let P := G.layout.add_edge_sequence m in
{ scores := (G.scores.1 + (P.2.map finset.card).sum, G.scores.2),
  layout := P.1 }
def move_right (G : board) (m : G.moves) : board :=
let P := G.layout.add_edge_sequence m in
{ scores := (G.scores.1, G.scores.2 + (P.2.map finset.card).sum),
  layout := P.1 }

@[simp]
lemma move_left_layout (G : board) (m : G.moves) :
  (G.move_left m).layout = (G.layout.add_edge_sequence m).1 := rfl
@[simp]
lemma move_right_layout (G : board) (m : G.moves) :
  (G.move_right m).layout = (G.layout.add_edge_sequence m).1 := rfl

end board

open board

/-- The instance describing allowed moves in dots and boxes. -/
instance state : state board :=
{ turn_bound := λ G, G.layout.remaining_edges.card,
  L := λ G, finset.univ.image (move_left G),
  R := λ G, finset.univ.image (move_right G),
  left_bound := λ s t m,
  begin
    simp only [finset.mem_image] at m,
    rcases m with ⟨m, ⟨h, rfl⟩⟩, clear h,
    simp only [move_left_layout],
    apply layout.remaining_edges_add_edge_sequence_card_lt,
  end,
  right_bound := λ s t m,
  begin
    simp only [finset.mem_image] at m,
    rcases m with ⟨m, ⟨h, rfl⟩⟩, clear h,
    simp only [move_right_layout],
    apply layout.remaining_edges_add_edge_sequence_card_lt,
  end, }

instance : has_scoring board := ⟨board.scores⟩

end dots_and_boxes

/-- Construct a pre-game from a dots and boxes board. -/
def dots_and_boxes (b : dots_and_boxes.board) : pgame := @pgame.of _ (state_with_scoring dots_and_boxes.board) (sum.inl b : with_scoring dots_and_boxes.board)

/-- All games of dots and boxes are short, because it's hard to beat Kevin. -/
instance short_dots_and_boxes (b : dots_and_boxes.board) : short (dots_and_boxes b) :=
by { dsimp [dots_and_boxes], apply_instance }

/-- The one-by-one dots and boxes board, in which Right collects the only box, on their second move. -/
@[derive short]
def dots_and_boxes.one : pgame := dots_and_boxes
{ layout := layout.rectangular 1 1,
  scores := (0,0) }

-- We're not there yet! Is it just because we have `sorry`? Or did we mess up somewhere?

run_cmd tactic.whnf `(by apply_instance : decidable (dots_and_boxes.one ≤ 1)) >>= tactic.trace

#eval to_bool (dots_and_boxes.one ≈ -1)
