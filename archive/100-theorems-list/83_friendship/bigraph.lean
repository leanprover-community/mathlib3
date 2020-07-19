import algebra.big_operators

open_locale classical big_operators
noncomputable theory

universes u v
variables (α : Type u) (β : Type v)

@[ext] structure bigraph :=
(A : finset α)
(B : finset β)
(E : α → β → Prop)

variables {α} {β} (G : bigraph α β)

namespace bigraph

def uncurried : (α × β) → Prop := function.uncurry (G.E)
-- simp normal form is curried, then. do we want that?
@[simp] lemma recurry (x : α × β) : (uncurried G) x = G.E x.fst x.snd:=
by rw [uncurried, function.uncurry]

def swap_inputs (E : α → β → Prop) : β → α → Prop :=
  function.curry ((function.uncurry E) ∘ prod.swap)

@[simp] lemma swap_inputs' (E : α → β → Prop) (a : α) (b : β) :
  swap_inputs E b a = E a b:=
by simp [swap_inputs, function.uncurry, function.curry]

@[simp] lemma swap_inputs_invol (E : α → β → Prop):
  swap_inputs (swap_inputs E)=E:=
by ext; simp

def swap : bigraph β α :=
{ A := G.B,
  B := G.A,
  E := swap_inputs G.E }

@[simp] lemma A_swap : G.swap.A = G.B := rfl

@[simp] lemma B_swap : G.swap.B = G.A := rfl

@[simp] lemma E_swap : G.swap.E = swap_inputs G.E := rfl

@[simp] lemma swap_swap : G.swap.swap = G := by ext; simp [swap]

def edges : finset (α × β) := finset.filter (uncurried G) (finset.product G.A G.B)

-- i think mem_edges_iff is a more standard name in the library? not sure.
@[simp] lemma mem_edges (x : α × β) : x ∈ edges G ↔ (x.fst ∈ G.A ∧ x.snd ∈ G.B) ∧ G.E x.fst x.snd :=
by { unfold edges, simp }

def card_edges : ℕ := (edges G).card

lemma mem_edges_swap (x : β × α) :
  x ∈ edges G.swap ↔ x.swap ∈ edges G := by { simp, tauto }

lemma edges_swap : edges G.swap = finset.image prod.swap (edges G) :=
begin
  ext, rw [finset.mem_image, mem_edges_swap],
  split, { intro h1, use [a.swap, h1], simp },
  rintro ⟨ _, _, rfl⟩, rwa prod.swap_swap,
end

@[simp]
lemma card_edges_symm (G : bigraph α β) : card_edges G.swap = card_edges G :=
begin
  change (edges (swap G)).card = (edges G).card,
  apply nat.le_antisymm,
  { rw edges_swap, apply finset.card_image_le },
  convert finset.card_image_le, rotate 2, { exact prod.swap },
  rw ← edges_swap, simp,
end

def left_fiber (b : β) : finset α :=
  finset.filter (λ (a1:α), (uncurried G) (a1, b)) G.A

def right_fiber (a : α) : finset β :=
  finset.filter (λ (b1 : β), (uncurried G) (a, b1)) G.B

def left_fiber' (b : β) : finset (α × β) := finset.image (λ a:α, (a,b)) (left_fiber G b)

def right_fiber' (a : α) : finset (α × β) := finset.image (λ b:β, (a,b)) (right_fiber G a)

@[simp] lemma mem_left_fiber (b : β) {x : α} :
x ∈ (left_fiber G b) ↔ x ∈ G.A ∧ G.E x b := by { unfold left_fiber, simp }

@[simp] lemma mem_right_fiber (a : α) {x : β} :
x ∈ (right_fiber G a) ↔ x ∈ G.B ∧ G.E a x := by { unfold right_fiber, simp }

@[simp] lemma left_fiber_swap (a : α) :
left_fiber G.swap a = right_fiber G a := by { ext, simp }

@[simp] lemma right_fiber_swap (b : β) :
right_fiber G.swap b = left_fiber G b := by { ext, simp }

@[simp] lemma mem_left_fiber' (b : β) (x : α × β) :
x ∈ (left_fiber' G b) ↔ (x.fst ∈ G.A ∧ x.snd = b) ∧ G.E x.fst x.snd :=
by rw left_fiber'; tidy

-- can the following be proven with swap and the above?
@[simp] lemma mem_right_fiber' (a : α) (x : α × β) :
x ∈ (right_fiber' G a) ↔ (x.fst = a ∧ x.snd ∈ G.B) ∧ G.E x.fst x.snd :=
by rw right_fiber'; tidy

-- i'm now confused about the properties of our simp normal form.
-- Do we always want to get swap out of G.swap?
@[simp] lemma left_fiber'_swap (a : α) :
left_fiber' G.swap a = finset.image prod.swap (right_fiber' G a) :=
begin
  have h : right_fiber' G a = finset.image (prod.mk a) (right_fiber G a) := rfl,
  rw [h, finset.image_image],
  have h2 : left_fiber' G.swap a = finset.image (λ b:β,(b,a)) (left_fiber G.swap a) := rfl,
  simp [h2]; refl,
end

@[simp] lemma right_fiber'_swap (b : β):
  right_fiber' G.swap b = finset.image prod.swap (left_fiber' G b):=
by rw [left_fiber', finset.image_image, right_fiber', right_fiber_swap]; refl

@[simp] lemma card_left_fiber_eq_card_left_fiber' (b : β) :
  (left_fiber G b).card = (left_fiber' G b).card :=
by { symmetry, apply finset.card_image_of_injective, intros _ _, simp }

lemma disjoint_left_fiber' {b1 b2 : β} (h : b1 ≠ b2):
  disjoint (left_fiber' G b1) (left_fiber' G b2):=
begin
  rw finset.disjoint_iff_inter_eq_empty, ext,
  simp only [and_imp, finset.not_mem_empty, mem_left_fiber', not_and, iff_false, finset.mem_inter],
  rintros _ rfl _ _ _, contradiction,
end

-- is this a useful simp lemma if reversed?
lemma edges_eq_bind_left_fibers :
  edges G = (G.B).bind (λ (b : β), left_fiber' G b) :=
begin
  ext, simp only [exists_prop, mem_left_fiber', mem_edges, finset.mem_bind],
  split, { rw and_imp, intros, use a.snd, tauto },
  simp only [and_imp, exists_imp_distrib],
  rintros _ _ _ rfl, tauto,
end

lemma edges_eq_bind_right_fibers :
  edges G = (G.A).bind (λ (a : α), right_fiber' G a):=
begin
  rw [← swap_swap G, edges_swap, edges_eq_bind_left_fibers, finset.bind_image],
  simp only [B_swap, swap_swap, left_fiber'_swap],
  congr, ext, rw [finset.image_image, prod.swap_swap_eq, finset.image_id],
end

theorem sum_left_fibers :
  card_edges G = ∑ b in G.B, (left_fiber G b).card :=
begin
  rw card_edges,
  convert finset.card_bind _,
  swap, { simp }, { simp [edges_eq_bind_left_fibers] }, { apply_instance },
  intros _ _ _ _ h, exact disjoint_left_fiber' _ h,
end

theorem sum_right_fibers :
  card_edges G = ∑ a in G.A, (right_fiber G a).card :=
by { simp_rw ← left_fiber_swap, rw ← card_edges_symm, apply sum_left_fibers }

def left_regular (d : ℕ) : Prop :=
  ∀ b ∈ G.B, (left_fiber G b).card = d

def right_regular (d : ℕ) : Prop:=
  ∀ a ∈ G.A, (right_fiber G a).card = d

def left_unique : Prop :=
  ∀ b ∈ G.B, ∃!(a : α), a ∈ G.A ∧ G.E a b

def right_unique : Prop :=
  ∀ a ∈ G.A, ∃!(b : β), b ∈ G.B ∧ G.E a b

@[simp] lemma right_regular_swap (d  :ℕ) : right_regular G.swap d ↔ left_regular G d :=
by simp [left_regular, right_regular]

@[simp] lemma left_regular_swap {d : ℕ} : left_regular G.swap d ↔ right_regular G d :=
by simp [left_regular, right_regular]

@[simp] lemma right_unique_swap : right_unique G.swap ↔ left_unique G :=
by simp [left_unique, right_unique]

@[simp] lemma left_unique_swap : left_unique G.swap ↔ right_unique G :=
by simp [left_unique, right_unique]

@[simp] lemma left_unique_one_reg : left_unique G ↔ left_regular G 1 :=
begin
  apply forall_congr, intro, apply imp_congr_right,
  simp_rw [finset.card_eq_one], simp [finset.singleton_iff_unique_mem],
end

@[simp] lemma right_unique_one_reg : right_unique G ↔ right_regular G 1 :=
by rw [← left_unique_swap, ← left_regular_swap]; apply left_unique_one_reg

theorem card_edges_of_lreg {l : ℕ} (hl : left_regular G l) : card_edges G = l * G.B.card:=
by rwa [sum_left_fibers, mul_comm l, finset.sum_const_nat]

theorem card_edges_of_rreg {r : ℕ} (hr : right_regular G r) : card_edges G = r * G.A.card :=
by rwa [sum_right_fibers, mul_comm r, finset.sum_const_nat]

theorem card_edges_of_lunique (h : left_unique G) : card_edges G = G.B.card :=
by { rw left_unique_one_reg at h, convert card_edges_of_lreg _ h, simp }

theorem card_edges_of_runique (h : right_unique G) : card_edges G = G.A.card :=
by { rw right_unique_one_reg at h, convert card_edges_of_rreg _ h, simp }

theorem double_count_of_lreg_rreg {l r : ℕ} (hl : left_regular G l) (hr : right_regular G r) :
r * G.A.card = l * G.B.card :=
by rwa [← card_edges_of_rreg _ hr, ← card_edges_of_lreg]

theorem card_eq_of_lunique_runique (hl : left_unique G) (hr : right_unique G ) :
G.A.card = G.B.card :=
begin
  rw right_unique_one_reg at hr, rw left_unique_one_reg at hl,
  convert double_count_of_lreg_rreg _ hl hr; simp,
end
variables (E : α → β → Prop)

lemma edges_disjoint_of_eq_disj_eq {A : finset α} {B1 B2 : finset β} (h : disjoint B1 B2) :
  disjoint (edges ⟨A, B1, E⟩) (edges ⟨A, B2, E⟩) :=
begin
  apply finset.disjoint_filter_filter,
  rw finset.disjoint_iff_ne,
  rintros a _ _ _ rfl,
  rw finset.mem_product at *,
  rw finset.disjoint_iff_ne at h,
  apply h a.snd _ a.snd; tauto,
end

lemma edges_union {A : finset α} {B1 B2 : finset β} :
  edges ⟨ A, B1 ∪ B2, E⟩ = edges ⟨A, B1, E⟩ ∪ edges ⟨A, B2, E⟩ :=
begin
  erw ← finset.filter_union,
  suffices : A.product (B1 ∪ B2) = A.product B1 ∪ A.product B2, { rw ← this, refl },
  ext, simp [ finset.mem_union, finset.mem_product]; tauto,
end

theorem card_edges_add_of_eq_disj_union_eq {A : finset α} {B1 B2 : finset β} (h : disjoint B1 B2) (E : α → β → Prop) :
card_edges ⟨A, B1 ∪ B2, E⟩ = card_edges ⟨A, B1, E⟩ + card_edges ⟨A, B2, E⟩ :=
by { rw [card_edges, edges_union], simp [edges_disjoint_of_eq_disj_eq, h], refl }

end bigraph
