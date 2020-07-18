import data.fintype.basic data.finset data.prod algebra.big_operators
import tactic

open_locale classical
noncomputable theory

@[ext] structure bigraph (α β:Type*):=
(A: finset α)
(B: finset β)
(E:α → β → Prop)

variables {α :Type*} {β :Type*}




def uncurried (G:bigraph α β):(α × β) → Prop:=
  function.uncurry (G.E)

@[simp] lemma recurry (G:bigraph α β){x : α × β}:
  (uncurried G) x=G.E x.fst x.snd:=
begin
  unfold uncurried,
  unfold function.uncurry,
end

def swap_inputs (E:α → β → Prop): β → α → Prop:=
  function.curry ((function.uncurry E) ∘ prod.swap)

@[simp] lemma swap_inputs' (E:α → β → Prop){a:α}{b:β}:
  swap_inputs E b a=E a b:=
begin
  unfold swap_inputs,
  simp only [eq_iff_iff], 
  unfold function.uncurry,
  unfold function.curry,
  simp,
end

@[simp] lemma swap_inputs_invol (E:α → β → Prop):
  swap_inputs (swap_inputs E)=E:=
begin
  ext,
  simp,
end

def bigraph.swap (G:bigraph α β):bigraph β α:=
{
  A:=G.B,
  B:=G.A,
  E:=swap_inputs G.E,
}

@[simp] lemma bigraph.A_swap (G:bigraph α β):
  G.swap.A=G.B:=rfl

@[simp] lemma bigraph.B_swap (G:bigraph α β):
  G.swap.B=G.A:=rfl

@[simp] lemma bigraph.E_swap (G:bigraph α β):
  G.swap.E=swap_inputs G.E:=rfl

@[simp] lemma bigraph.swap_swap (G:bigraph α β):
  G.swap.swap=G:=
begin
  ext,
  unfold bigraph.swap,
  unfold bigraph.swap,
  dsimp; simp,
end

def edges  (G:bigraph α β): finset (α × β):=
  finset.filter (uncurried G) (finset.product G.A G.B)

@[simp] lemma mem_edges (G:bigraph α β){x:(α × β)}:
  x ∈ edges G ↔ (x.fst ∈ G.A ∧ x.snd ∈ G.B) ∧ G.E x.fst x.snd := by { unfold edges, simp }

def card_edges (G:bigraph α β): ℕ :=
  (edges G).card

lemma mem_edges_swap (G:bigraph α β) {x : β × α} :
  x ∈ edges G.swap ↔ x.swap ∈ edges G := by {simp, tauto}


lemma edges_swap (G:bigraph α β):
  edges G.swap = finset.image prod.swap (edges G):=
begin
  ext, rw [finset.mem_image, mem_edges_swap],
  split, 
  { intro h1, use [a.swap, h1], simp },
  rintro ⟨ _, _, h⟩, 
  rw ← h, rwa prod.swap_swap,
end

lemma card_edges_symm (G:bigraph α β):
  card_edges (bigraph.swap G)=card_edges G:=
begin
  change (edges (bigraph.swap G)).card=(edges G).card,
  apply nat.le_antisymm, 
  { rw edges_swap, apply finset.card_image_le },
  rw ← bigraph.swap_swap G,
  rw bigraph.swap_swap G.swap,
  rw edges_swap,
  apply finset.card_image_le,
end

def left_fiber (G:bigraph α β)(b: β): finset α:=
  finset.filter (λ (a1:α), (uncurried G) (a1, b)) G.A

def right_fiber (G:bigraph α β)(a:α): finset β:=
  finset.filter (λ (b1:β), (uncurried G) (a, b1)) G.B

def left_fiber' (G:bigraph α β)(b: β): finset (α × β):=
  finset.image (λ a:α, (a,b)) (left_fiber G b)

def right_fiber' (G:bigraph α β)(a:α): finset (α × β):=
  finset.image (λ b:β, (a,b)) (right_fiber G a)

@[simp] lemma mem_left_fiber (G : bigraph α β) {b : β} {x : α}:
x ∈ (left_fiber G b) ↔ x ∈ G.A ∧ G.E x b := by { unfold left_fiber, simp }


@[simp] lemma mem_right_fiber (G : bigraph α β) {a : α} {x : β} :
x ∈ (right_fiber G a) ↔ x ∈ G.B ∧ G.E a x := by { unfold right_fiber, simp }


@[simp] lemma left_fiber_swap (G : bigraph α β) {a : α} :
left_fiber G.swap a=right_fiber G a := by { ext, simp }


@[simp] lemma right_fiber_swap (G : bigraph α β) {b : β} :
right_fiber G.swap b = left_fiber G b := by { ext, simp }

@[simp] lemma mem_left_fiber' (G : bigraph α β) {b : β} {x : α × β} :
x ∈ (left_fiber' G b) ↔  (x.fst ∈ G.A ∧ x.snd = b) ∧ G.E x.fst x.snd:=
begin
  unfold left_fiber', tidy,
  -- here's a human proof that runs a little faster than tidy:
  -- simp only [exists_prop, mem_left_fiber, finset.mem_image],
  -- split, 

  -- simp only [and_imp, exists_imp_distrib],
  -- intros h1 h2 h3 h4,
  -- rw ← h4, tauto,

  -- simp,
  -- intros h1 h2 h3,
  -- use x.fst,
  -- rw ← h2, 
  -- simp; tauto,
end
-- can the following be proven with swap and the above?
@[simp] lemma mem_right_fiber' (G:bigraph α β) {a:α} {x : α × β} :
x ∈ (right_fiber' G a) ↔ (x.fst = a ∧ x.snd ∈ G.B) ∧ G.E x.fst x.snd :=
begin
  unfold right_fiber', tidy,
  -- here's a human proof that runs a little faster than tidy:

  -- simp,
  -- split,

  -- simp,
  -- intros b h2 h3 h4,
  -- rw ← h4,
  -- simp,
  -- tauto,

  -- simp,
  -- intros h1 h2 h3,
  -- use x.snd,
  -- rw ← h1,
  -- simp,
  -- tauto,
end

@[simp] lemma left_fiber'_swap (G : bigraph α β) {a : α} :
left_fiber' G.swap a = finset.image prod.swap (right_fiber' G a) :=
begin
  have h : right_fiber' G a = finset.image (λ b:β,(a,b)) (right_fiber G a) := by refl,
  rw [h, finset.image_image],
  have h2 : left_fiber' G.swap a = finset.image (λ b:β,(b,a)) (left_fiber G.swap a) := by refl,
  simp [h2]; refl,
end

@[simp] lemma right_fiber'_swap (G:bigraph α β){b:β}:
  right_fiber' G.swap b = finset.image prod.swap (left_fiber' G b):=
begin
  have h : left_fiber' G b = finset.image (λ a:α,(a,b)) (left_fiber G b),
    refl,
  rw h,
  rw finset.image_image,
  have h:right_fiber' G.swap b = finset.image (λ a:α,(b,a)) (right_fiber G.swap b),
    refl,
  rw h,
  simp,
  refl,
end

@[simp] lemma card_left_fiber_eq_' {G:bigraph α β}{b: β}:
  (left_fiber G b).card=(left_fiber' G b).card:=
begin
  symmetry,
  apply finset.card_image_of_injective,
  unfold function.injective,
  intros a1 a2 h,
  change (a1,b).fst=(a2,b).fst,
  rw h,
end

lemma card_left_fiber_fun_eq_' {G:bigraph α β}:
  (λ (b:β), (left_fiber G b).card)=λ (b:β),(left_fiber' G b).card:=by simp

lemma disjoint_left_fiber' (G:bigraph α β){b1 b2: β}:
  b1 ≠ b2 → disjoint (left_fiber' G b1) (left_fiber' G b2):=
begin
  intro neq,
  rw finset.disjoint_iff_inter_eq_empty,
  ext,
  simp,
  intros h1 h2 h3 h4 h5 h6,
  apply neq,
  rw ← h2,
  rw ← h5,
end

lemma edges_eq_bind_left_fibers (G:bigraph α β):
  edges G=(G.B).bind (λ (b : β), left_fiber' G b):=
begin
  ext,
  simp,
  split,
  simp,
  intros h1 h2 h3,
  use a.snd,
  tauto,
  simp,
  intros x h1 h2 h3 h4,
  rw h3,
  rw h3 at h4,
  tauto,
end


lemma edges_eq_bind_right_fibers (G:bigraph α β):
  edges G=(G.A).bind (λ (a : α), right_fiber' G a):=
begin
  transitivity finset.image prod.swap (edges G.swap),
  rw ← bigraph.swap_swap G,
  rw bigraph.swap_swap G.swap,
  rw edges_swap,
  rw edges_eq_bind_left_fibers,
  rw finset.bind_image,
  simp,
  refine congr rfl _,
  ext,
  rw finset.image_image,
  rw prod.swap_swap_eq,
  rw finset.image_id,
end


theorem sum_left_fibers (G:bigraph α β):
  card_edges G = G.B.sum(λ (b1:β), (left_fiber G b1).card):=
begin
  rw card_left_fiber_fun_eq_',
  change (edges G).card = G.B.sum(λ (b1:β), (left_fiber' G b1).card),
  rw edges_eq_bind_left_fibers,
  apply finset.card_bind,
  intros x hx y hy neq,
  apply disjoint_left_fiber' G neq,
end

theorem sum_right_fibers (G : bigraph α β):
  card_edges G = G.A.sum(λ (a1:α), (right_fiber G a1).card):=
begin
  transitivity G.A.sum(λ (a1:α), (left_fiber G.swap a1).card),
  transitivity card_edges G.swap,
  rw card_edges_symm,
  apply sum_left_fibers,
  simp,
end

variable (G : bigraph α β)

def left_regular (d : ℕ) : Prop :=
  ∀ (b : β), b ∈ G.B→ (left_fiber G b).card = d

def right_regular (d:ℕ):Prop:=
  ∀ (a : α), a ∈ G.A → (right_fiber G a).card = d

def left_unique : Prop :=
  ∀ (b : β), b ∈ G.B→∃!(a : α), a ∈ G.A ∧ G.E a b

def right_unique : Prop :=
  ∀ (a : α), a ∈ G.A→∃!(b : β), b ∈ G.B ∧ G.E a b

@[simp] lemma right_regular_swap (d  :ℕ) : right_regular G.swap d ↔ left_regular G d :=
begin
  unfold left_regular,
  unfold right_regular,
  simp,
end

@[simp] lemma left_regular_swap {d : ℕ} : left_regular G.swap d ↔ right_regular G d :=
begin
  unfold left_regular,
  unfold right_regular,
  simp,
end

@[simp] lemma right_unique_swap : right_unique G.swap ↔ left_unique G :=
begin
  unfold left_unique,
  unfold right_unique,
  refl,
end

@[simp] lemma left_unique_swap : left_unique G.swap ↔ right_unique G :=
begin
  unfold left_unique,
  unfold right_unique,
  refl,
end

@[simp] lemma left_unique_one_reg : left_unique G ↔ left_regular G 1 :=
begin
  transitivity ∀ b:β, b ∈ G.B → ∃!(a:α), a ∈ left_fiber G b,
  unfold left_unique,
  simp,
  unfold left_regular,
  apply forall_congr,
  intro x,
  apply imp_congr_right,
  intro hx,
  rw finset.card_eq_one,
  rw finset.singleton_iff_unique_mem,
end

@[simp] lemma right_unique_one_reg : right_unique G ↔ right_regular G 1 :=
begin
  rw ← left_unique_swap,
  rw ← left_regular_swap,
  apply left_unique_one_reg,
end

theorem card_edges_of_lreg {l : ℕ} (hl : left_regular G l) : card_edges G = l * G.B.card:=
by {rwa [sum_left_fibers, mul_comm l, finset.sum_const_nat]}

theorem card_edges_of_lunique :
  left_unique G → card_edges G = G.B.card :=
begin
  rw left_unique_one_reg,
  intro h,
  have h1 := card_edges_of_lreg G h,
  simp at h1,
  apply h1,
end

theorem card_edges_of_rreg {r : ℕ} (hr : right_regular G r) : card_edges G = r * G.A.card :=
by { rwa [sum_right_fibers, mul_comm r, finset.sum_const_nat] }

theorem card_edges_of_runique : right_unique G → card_edges G = G.A.card :=
begin
  rw right_unique_one_reg,
  intro h,
  have h1 := card_edges_of_rreg G h,
  simp at h1,
  apply h1,
end

theorem double_count_of_lreg_rreg {l r : ℕ} (hl : left_regular G l) (hr : right_regular G r) :
r * G.A.card = l * G.B.card :=
by { rwa [← card_edges_of_rreg _ hr, ← card_edges_of_lreg] }

theorem card_eq_of_lunique_runique (hl : left_unique G) (hr : right_unique G ) :
G.A.card = G.B.card :=
begin 
  simp only [right_unique_one_reg, left_unique_one_reg] at hl hr,
  have h := double_count_of_lreg_rreg _ hl hr, 
  revert h, simp,
end

lemma edges_disjoint_of_eq_disj_eq {A : finset α} {B1 B2 : finset β} {E : α → β → Prop} :
  disjoint B1 B2 → disjoint (edges ⟨A, B1, E⟩) (edges ⟨A, B2, E⟩) :=
begin
  intro disj,
  change disjoint (finset.filter (function.uncurry E)(A.product B1)) (finset.filter (function.uncurry E)(A.product B2)),
  apply finset.disjoint_filter_filter,
  rw finset.disjoint_iff_ne,
  intros a ha b hb,
  intro contra,
  rw finset.mem_product at *,
  rw finset.disjoint_iff_ne at disj,
  apply disj a.snd ha.right b.snd hb.right,
  rw contra,
end

lemma edges_union_of_eq_union_eq {A : finset α} {B1 B2 : finset β} {E : α→ β→ Prop} :
  edges ⟨ A, B1 ∪ B2, E⟩=edges ⟨A, B1, E⟩ ∪ edges ⟨A, B2, E⟩ :=
begin
  change finset.filter (function.uncurry E)(A.product (B1 ∪ B2)) = finset.filter (function.uncurry E)(A.product B1) ∪ finset.filter (function.uncurry E)(A.product B2),
  rw ← finset.filter_union,
  refine congr rfl _,
  ext,
  rw finset.mem_union,
  repeat {rw finset.mem_product},
  rw finset.mem_union,
  tauto,
end

theorem card_edges_add_of_eq_disj_union_eq {A : finset α} {B1 B2 : finset β} (h : disjoint B1 B2) (E : α → β → Prop) :
card_edges ⟨A, B1 ∪ B2, E⟩ = card_edges ⟨A, B1, E⟩ + card_edges ⟨A, B2, E⟩ :=
begin
  unfold card_edges,
  rw edges_union_of_eq_union_eq,
  apply finset.card_disjoint_union,
  exact edges_disjoint_of_eq_disj_eq h,
end