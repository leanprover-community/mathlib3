import geometry.tarski.basic

variables {α : Type*} [tarski_neutral α] {A B C D E F : α}

def name.add_suffix : name → string → name
| (name.mk_string n s) t := name.mk_string (n ++ t) s
| n _ := n

meta def expr.is_btw : expr → option (expr × expr × expr)
| `(btw %%A %%B %%C) := some (A, B, C)
| _ := none

meta def expr.is_btw_b : expr → bool :=
option.is_some ∘ expr.is_btw

/-- Attempts to run `f` on each pair `(x,y)` from the list. Succeeds if any one succeeds. -/
meta def list.on_pairs {α β : Type*} (f : α → α → tactic β) : list α → tactic β
| [] := failure
| (x :: xs) := list.mfirst (f x) xs <|> xs.on_pairs

namespace tactic

declare_trace tarski

meta def tarski_trace {α} [has_to_tactic_format α] (s : α) : tactic unit :=
tactic.when_tracing `tarski (tactic.trace s)

meta def assertv_if_new (h : name) (t : expr) (v : expr) : tactic expr :=
fail_if_success (find_assumption t) >> assertv h t v

meta def note_if_new (h : name) (t : option expr := none) (pr : expr) : tactic expr :=
let dv := λ t, assertv_if_new h t pr in option.cases_on t (infer_type pr >>= dv) dv

meta def note_anon_if_new (t : option expr := none) (pr : expr) : tactic expr :=
get_unused_name `h >>= λ h, note_if_new h t pr

meta def is_trivial_btw (e : expr) : bool :=
option.cases_on e.is_btw ff (λ ⟨A, B, C⟩, (A = B) || (B = C))

meta def is_refl (e : expr) : bool :=
option.cases_on e.is_eq ff (λ ⟨A, B⟩, A = B)

meta def clear_proofs_of_same_prop (e₁ e₂ : expr) : tactic unit :=
do
  t₁ ← infer_type e₁,
  t₂ ← infer_type e₂,
  is_prop t₁ >>= guardb,
  unify t₁ t₂,
  clear e₁

meta def clear_repeat : tactic unit :=
local_context >>= list.on_pairs clear_proofs_of_same_prop

meta def register_new (fn : name) (args : list expr) (pf : option expr := none)
  (nm : option name := none) :
  tactic unit :=
do pf ← (pf.cases_on' (mk_app fn args) return) <|> (tactic.trace "MK_APP FAILED" >> failed),
   nm ← get_unused_name (nm.cases_on' `h id),
   t ← infer_type pf,
   z ← note_if_new nm (some t) pf,
   pp_t ← pp t,
   tarski_trace (format!"added hypothesis {z} : {pp_t} by {fn} on {args}")

meta def btw_add_symm (e : expr × expr × expr × expr) : tactic unit :=
register_new `has_btw.btw.symm [e.1] none (mk_simple_name (e.1.to_string ++ "_symm"))

meta def btw_add_eq : expr × expr × expr × expr → tactic unit
| ⟨e, A, B, C⟩ :=
    guard (A = C) >> register_new `has_btw.btw.eq [e]

meta def btw_eqs : expr × expr × expr × expr → tactic unit
| ⟨e, A, B, C⟩ :=
  first
  [ (do new_goal ← mk_app `ne [A, B],
        e' ← find_assumption new_goal,
        pf ← to_expr ``(has_btw.btw.ne_of_ne_left %%e %%e'),
        register_new `has_btw.btw.ne_of_ne_left [e, e'] pf),
    (do new_goal ← tactic.mk_app `ne [B, C],
        e' ← tactic.find_assumption new_goal,
        pf ← to_expr ``(has_btw.btw.ne_of_ne_right %%e %%e'),
        register_new `has_btw.btw.ne_of_ne_right [e, e'] pf),
    (do new_goal ← tactic.mk_app `eq [A, C],
        e' ← tactic.find_assumption new_goal,
        register_new `has_btw.btw.eq_left_of_eq [e, e']),
    (do new_goal ← tactic.mk_app `eq [A, C],
        e' ← tactic.find_assumption new_goal,
        register_new `has_btw.btw.eq_right_of_eq [e, e']) ]

-- e₁ should have type btw A B C and e₂ should have type btw A C D
meta def new_left_common_aux (e₁ e₂ A B C D : expr) : tactic unit :=
if B = D
  then register_new `has_btw.btw.antisymm_right [e₁, e₂]
  else try (register_new `has_btw.btw.left_trans [e₁, e₂]) >>
       register_new `has_btw.btw.left_cancel [e₁, e₂]

meta def new_left_common :
  (expr × expr × expr × expr) × (expr × expr × expr × expr) → tactic unit
| ⟨⟨e₁, A, B, C⟩, ⟨e₂, D, E, F⟩⟩ :=
    guard (A = D) >>
      if C = E
        then new_left_common_aux e₁ e₂ A B C F
        else guard (B = F) >> (new_left_common_aux e₂ e₁ A E B C)

-- e₁ should have type btw A B D and e₂ should have type btw B C D
meta def new_right_common_aux (e₁ e₂ A B C D : expr) : tactic unit :=
if A = C
  then register_new `has_btw.btw.antisymm_left [e₁, e₂]
  else
      try (register_new `has_btw.btw.right_trans [e₁, e₂]) >>
      register_new `has_btw.btw.right_cancel [e₁, e₂]

meta def new_right_common :
  (expr × expr × expr × expr) × (expr × expr × expr × expr) → tactic unit
| ⟨⟨e₁, A, B, C⟩, ⟨e₂, D, E, F⟩⟩ :=
    guard (C = F) >>
      if B = D
        then new_right_common_aux e₁ e₂ A B C E
        else guard (A = E) >> new_right_common_aux e₂ e₁ D A C B

-- e₁ should have type btw A B C and e₂ should have type B C D
meta def new_middle_common_aux (e₁ e₂ A B C D : expr) : tactic unit :=
do
  new_goal ← tactic.mk_app `ne [B, C],
  e ← tactic.find_assumption new_goal,
  try (register_new `has_btw.btw.trans_left [e₁, e₂, e]),
  register_new `has_btw.btw.trans_right [e₁, e₂, e]

meta def new_middle_common :
  (expr × expr × expr × expr) × (expr × expr × expr × expr) → tactic unit
| ⟨⟨e₁, A, B, C⟩, ⟨e₂, D, E, F⟩⟩ :=
    (guard (B = D ∧ C = E) >> new_middle_common_aux e₁ e₂ A B C D) <|>
    (guard (A = E ∧ B = F) >> new_middle_common_aux e₂ e₁ D A B C)

meta def btw_forward (e₁ e₂ : expr × expr × expr × expr) : tactic unit :=
([new_left_common, new_right_common, new_middle_common]).mfirst ($ ⟨e₁, e₂⟩)

meta def indexed_extract_by_type {β : Type*} (f : expr → option β) :
  list expr → tactic (list (expr × β))
| [] := return []
| (x :: xs) := do
    t ← infer_type x,
    option.cases_on (f t) (indexed_extract_by_type xs)
      (λ y, (list.cons (x, y)) <$> indexed_extract_by_type xs)

meta def get_btw_hyps : tactic (list (expr × expr × expr × expr)) :=
local_context >>= indexed_extract_by_type expr.is_btw

meta def clear_trivials : tactic unit :=
first
[ local_context >>= indexed_extract_by_type expr.is_eq >>= list.mfirst
    (λ ⟨h, A, B⟩, clear h >> guard (A = B) >>
      tarski_trace (format!"clearing {A} = {B}")),
  local_context >>= indexed_extract_by_type expr.is_btw >>= list.mfirst
    (λ ⟨h, A, B, C⟩, clear h >> guard (A = B ∨ B = C) >>
      tarski_trace (format!"clearing btw {A} {B} {C}")) ]

meta def generate_hypotheses : tactic unit :=
do btws ← get_btw_hyps,
  first
  [ btws.on_pairs btw_forward,
    btws.mfirst btw_add_eq,
    btws.mfirst btw_eqs,
    btws.mfirst btw_add_symm ]

-- tries refl, assumption, btw_id_left and btw_id_right
meta def apply_basic : tactic unit :=
first
[ tactic.reflexivity >> tarski_trace "btw closed goal with refl",
  tactic.assumption >> tarski_trace "btw closed goal with assumption",
  applyc `tarski.btw_id_left >> tarski_trace "btw closed goal with btw_id_left",
  applyc `tarski.btw_id_right >> tarski_trace "btw closed goal with btw_id_right" ]

meta def my_subst : tactic unit :=
local_context >>= indexed_extract_by_type expr.is_eq >>= list.mfirst
  (λ ⟨h, A, B⟩, subst h >> tarski_trace (format!"substituting {A} = {B}"))

meta def btw_step : tactic unit :=
first
[ my_subst,
  apply_basic,
  clear_trivials,
  generate_hypotheses ]

meta def btw (hyps : list pexpr) : tactic unit :=
hyps.mmap' (λ e, i_to_expr e >>= try ∘ note_anon_if_new none) >> iterate_at_most' 100 btw_step

setup_tactic_parser

meta def interactive.btw (finishing : parse (tk "!")?) (show_term : parse (tk "?")?)
  (hyps : parse pexpr_list?) : tactic unit :=
let t := btw (hyps.get_or_else []) >>
  finishing.cases_on' (done <|> fail "btw couldn't find a proof") (λ _, skip)
in show_term.cases_on' t (λ _, tactic.interactive.show_term t)

end tactic

-- example (ABC : btw A B C) (ACD : btw A C D) : btw A B D :=
-- by btw

-- example (ABC : btw A B C) (ACD : btw A C D) : btw B C D :=
-- by btw

-- example (ABC : btw A B C) (ACB : btw A C B) : B = C :=
-- by btw

-- example (ABC : btw A B C) (ACB : btw A C B) : btw B C D :=
-- by btw

-- example : btw A A B :=
-- by btw

-- example (ABD : btw A B D) (BCD : btw B C D) : btw A B C :=
-- by btw

-- example (ABC : btw A B C) (BCD : btw B C D) (hBC : B ≠ C) : btw A C D :=
-- by btw

-- example (ABA : btw A B A) : A = B :=
-- by btw

-- example (ACD : btw A C D) (ABC : btw A B C) : btw B C D :=
-- by btw

-- example {x y z P Q : α} (xyz : btw x y z) (xPQ : btw x P Q) (xzP : btw x z P) : btw y P Q :=
-- by btw

-- set_option trace.tarski true

-- meta def register_new (fn : name) (args : list expr) (nm : option name := none) : tactic unit :=
-- do nm ← get_unused_name (nm.cases_on' `h id),
--    pf ← mk_app fn args <|> (tactic.trace "BTW ERROR: btw failed to construct proof" >> tactic.trace fn >> tactic.trace args >> failed),
--    t ← infer_type pf,
--    z ← note_if_new nm (some t) pf,
--    pp_t ← pp t,
--    tarski_trace (format!"added hypothesis {z} : {pp_t} by {fn} on {args}")

example (ABC : btw A B C) (h : A ≠ B) : A ≠ C :=
begin
  btw,


end
-- begin
--   -- let e₁ : expr :=
--   tactic.get_btw_hyps >>= list.mfirst tactic.btw_eqs,
-- end
-- by btw?

example (ABC : btw A B C) (h : B ≠ C) : A ≠ C :=
by btw

section btw

open tarski tarski_neutral

lemma segment_eq_of_btw_iff (h : ∀ X, btw A X B ↔ btw C X D) :
  A-ₛB = C-ₛD :=
begin
  rw [←quotient_mk_eq, ←quotient_mk_eq, sym2.eq_iff, or_iff_not_imp_right, not_and_distrib],
  rintro (nAD | nBC); split;
  btw [(h A).1 (by btw), (h B).1 (by btw), (h C).2 (by btw), (h D).2 (by btw)],
end

/-- Def 3.8 -/
def n_btw : list α → Prop
| [] := true
| (x :: l) := l.pairwise (btw x) ∧ n_btw l

@[simp] lemma n_btw_nil : n_btw ([] : list α) := trivial
lemma n_btw_cons (A : α) {l : list α} : n_btw (A :: l) ↔ l.pairwise (btw A) ∧ n_btw l := iff.rfl
@[simp] lemma n_btw_singleton : n_btw [A] := by simp [n_btw_cons]
@[simp] lemma n_btw_pair : n_btw [A, B] := by simp [n_btw_cons]
@[simp] lemma n_btw_three : n_btw [A, B, C] ↔ btw A B C := by simp [n_btw_cons]

lemma btw_of_n_btw_cons_cons {l : list α} (h : n_btw (A :: B :: l)) :
  ∀ C ∈ l, btw A B C :=
begin
  induction l,
  { simp },
  intro C,
  apply list.rel_of_pairwise_cons h.1,
end

/-- Lemma 3.10 -/
lemma n_btw_sublist {l₁ l₂ : list α} (h : l₁ <+ l₂) :
  n_btw l₂ → n_btw l₁ :=
begin
  induction h with _ _ _ _ _ _ _ _ t,
  { simp },
  { rintro ⟨_, h₂⟩,
    exact h_ih h₂ },
  { rintro ⟨h₁, h₂⟩,
    exact ⟨list.pairwise_of_sublist t h₁, h_ih h₂⟩ }
end

lemma n_btw_cons_cons_cons {l : list α} (hA : btw A B C) (hBC : B ≠ C) (h : n_btw (B :: C :: l)) :
  n_btw (A :: B :: C :: l) :=
begin
  rw [n_btw_cons],
  simp only [list.pairwise_cons, h, and_true, forall_eq_or_imp, list.mem_cons_iff, and_assoc],
  have : ∀ D ∈ l, btw A B D := λ D hD, hA.trans_left (btw_of_n_btw_cons_cons h D hD) hBC,
  refine ⟨hA, this, λ D hD, _, _⟩,
  { apply hA.trans_right (btw_of_n_btw_cons_cons h D hD) hBC },
  rw [n_btw_cons, list.pairwise_cons, and_assoc] at h,
  apply list.pairwise.imp_of_mem _ h.2.1,
  intros P Q hP hQ BPQ,
  exact (this P hP).trans_right BPQ ((h.1 P hP).ne_of_ne_left hBC),
end

lemma n_btw_append {l₁ l₂ : list α} :
  n_btw (l₁ ++ l₂) ↔
    n_btw l₁ ∧ n_btw l₂ ∧
    (∀ x₁ ∈ l₁, l₂.pairwise (btw x₁)) ∧ (∀ x₂ ∈ l₂, l₁.pairwise (λ a b, btw a b x₂)) :=
begin
  induction l₁ with x l₁ ih,
  { simp },
  simp only [list.cons_append, n_btw_cons, ih, list.pairwise_append, forall_eq_or_imp,
    list.mem_cons_iff, list.pairwise_cons, and_assoc, imp_and_distrib, forall_and_distrib],
  split,
  { rintro ⟨hl₁, hl₂, rl₁l₂, rl₁, rl₂, rl₁₂, rl₂₁⟩,
    exact ⟨hl₁, rl₁, rl₂, hl₂, rl₁₂, λ z hz y hy, rl₁l₂ _ hy _ hz, rl₂₁⟩ },
  { rintro ⟨hl₁, rl₁, rl₂, hl₂, rl₁₂, rl₁l₂, rl₂₁⟩,
    exact ⟨hl₁, hl₂, λ y hy z hz, rl₁l₂ _ hz _ hy, rl₁, rl₂, rl₁₂, rl₂₁⟩ },
end

lemma n_btw_reverse {l : list α} (hl : n_btw l) : n_btw l.reverse :=
begin
  induction l,
  { simp },
  simp [l_ih hl.2, hl.1, n_btw_append, btw_comm],
end

lemma n_btw_reverse_iff {l : list α} :
  n_btw l ↔ n_btw l.reverse :=
⟨n_btw_reverse, λ h, by simpa using (n_btw_reverse h)⟩

lemma n_btw_middle_aux (x y z : α) {l : list α} :
  btw x y z → n_btw (x :: z :: l) → n_btw (x :: y :: z :: l) :=
begin
  intros B h,
  simp only [n_btw_cons x, list.pairwise_cons, h.1, and_true, list.mem_cons_iff, true_and, h.2,
    forall_eq_or_imp, B, n_btw_cons y],
  refine ⟨λ a ha, B.left_trans (list.rel_of_pairwise_cons h.1 ha),
          λ a ha, B.left_cancel (list.rel_of_pairwise_cons h.1 ha), _⟩,
  apply list.pairwise.imp_of_mem _ (list.pairwise_of_pairwise_cons h.1),
  intros P Q hP hQ xPQ,
  btw [list.rel_of_pairwise_cons h.1 hP],
end

lemma list_of_points (n : ℕ) (h : ∃ (A B : α), A ≠ B) :
  ∃ (x y : α) (s : list α),
    (x :: y :: s).length = n + 2 ∧ n_btw (x :: y :: s) ∧ (x :: y :: s).nodup :=
begin
  induction n,
  { obtain ⟨A, B, nAB⟩ := h,
    exact ⟨A, B, [], by simp [nAB]⟩ },
  obtain ⟨X, Y, l, llength, lbtw, lnodup⟩ := n_ih,
  have nXY : X ≠ Y,
  { simp only [list.mem_cons_iff, list.nodup_cons, not_or_distrib] at lnodup,
    exact lnodup.1.1 },
  obtain ⟨E, hE₁, hE₂⟩ := exists_btw_cong Y X X Y,
  refine ⟨E, X, Y :: l, by simp [llength], n_btw_cons_cons_cons (by btw) nXY lbtw, _⟩,
  rw [list.nodup_cons, and_iff_left lnodup, list.mem_cons_iff, list.mem_cons_iff, not_or_distrib,
    not_or_distrib],
  refine ⟨(hE₂.symm.ne_of_ne nXY).symm, by btw, λ hl, nXY _⟩,
  -- btw!,
  btw [btw_of_n_btw_cons_cons lbtw _ hl],
  -- refine ⟨nXY.segment_construct_ne_snd, nXY.symm.segment_construct_ne_fst, λ hl, _⟩,
  -- exact nXY ((btw_of_n_btw_cons_cons lbtw _ hl).antisymm_left (segment_construct_btw Y X X Y)),
end

lemma finset_of_points (α : Type*) [tarski_neutral α] [nontrivial α] :
  ∀ (n : ℕ), ∃ {s : finset α}, s.card = n
| 0 := by simp
| 1 := let ⟨x, _⟩ := exists_pair_ne α in ⟨{x}, by simp⟩
| (n+2) :=
  let ⟨x, y, s, h₁, _, h₃⟩ := list_of_points n (exists_pair_ne α) in ⟨⟨x :: y :: s, h₃⟩, h₁⟩

/-- If a model of Tarski geometry is nontrivial, then it is infinite. -/
instance infinite_of_nontrivial [nontrivial α] : infinite α :=
begin
  constructor,
  introI h,
  obtain ⟨s : finset α, hs⟩ := finset_of_points α (fintype.card α + 1),
  apply not_lt_of_le (finset.card_le_univ s),
  rw hs,
  apply nat.lt_succ_self,
end

-- lemma n_btw_middle (x y z : α) (xyz : btw x y z) {l₁ l₂ : list α} :
--   n_btw (l₁ ++ x :: z :: l₂) → n_btw (l₁ ++ x :: y :: z :: l₂) :=
-- begin
--   rw [n_btw_append, n_btw_append],
--   rintro ⟨h₁, h₂, h₃, h₄⟩,
--   refine ⟨h₁, n_btw_middle_aux _ _ _ xyz h₂, _, _⟩,
--   { sorry },
--   simp only [forall_eq_or_imp, list.mem_cons_iff _ x, list.mem_cons_iff _ y] at h₄ ⊢,
--   refine ⟨h₄.1, _, h₄.2⟩,
--   apply list.pairwise.imp_of_mem _ h₄.1,
--   intros P Q hP hQ,

--   -- apply list.pairwise.imp_of_mem h₄.1,

--   -- simp only [forall_eq_or_imp, list.mem_cons_iff],

--   -- intros,
--   -- tauto,

--   -- induction l₁,
--   -- { apply n_btw_middle_aux _ _ _ xyz },
--   -- rw [list.cons_append, list.cons_append, n_btw_cons, n_btw_cons],
--   -- rintro ⟨h₁, h₂⟩,
--   -- refine ⟨_, l₁_ih h₂⟩,
--   -- rw list.pairwise_append at h₁ ⊢,
--   -- rcases h₁ with ⟨h₁₁, h₁₂, h₁₃⟩,
--   -- refine ⟨h₁₁, _, _⟩,

-- end


end btw

section mem

variables {α} [tarski_neutral α]

open tarski tarski_neutral

def segment.mem (B : α) : segment α → Prop :=
sym2.from_rel (λ A C (h : btw A B C), h.symm)

instance segment_set_like : set_like (segment α) α :=
{ coe := λ h x, segment.mem x h,
  coe_injective' :=
  begin
    refine sym2.ind (λ A B, _),
    refine sym2.ind (λ C D, _),
    simp only [function.funext_iff, eq_iff_iff, quotient_mk_eq],
    exact segment_eq_of_btw_iff,
  end }

@[simp] lemma mem_right : B ∈ A-ₛB := btw_id_right _ _
@[simp] lemma mem_left : A ∈ A-ₛB := btw_id_left _ _

lemma mem_segment_iff_btw : B ∈ A-ₛC ↔ btw A B C := iff.rfl
lemma btw_iff_mem_segment : btw A B C ↔ B ∈ A-ₛC := iff.rfl

lemma has_mem.mem.eq_of_trivial (h : B ∈ A-ₛA) : A = B := h.eq

lemma diag_iff {α : Type*} {p : Π {l : sym2 α}, l.is_diag → Prop} :
  (∀ {l : sym2 α} (h : l.is_diag), p h) ↔ ∀ A, p (sym2.diag_is_diag A) :=
⟨λ h A, h _, λ i, quotient.ind (by { rintro ⟨_, _⟩ ⟨⟩, apply i })⟩

lemma trivial_iff {p : Π {l : segment α} (h : l.trivial), Prop} :
  (∀ {l : segment α} (h : l.trivial), p h) ↔ ∀ A, p (segment.mk.trivial A) :=
diag_iff

lemma segment.trivial.eq_of_mem :
  Π {l₁ : segment α} (h : l₁.trivial), A ∈ l₁ → A = h.point :=
begin
  rw trivial_iff,
  intros B hB,
  apply hB.eq_of_trivial.symm,
end

@[simp] lemma mem_trivial_iff : B ∈ A-ₛA ↔ A = B :=
⟨λ h, h.eq_of_trivial, by { rintro rfl, simp }⟩

end mem

-- -- instance : has_coe (segment α) (set α) := ⟨λ h x, h.mem x⟩

-- instance : has_mem α (segment α) := ⟨λ x h, h.mem x⟩

-- @[simp] lemma mem_right : B ∈ (A-ₛB : set α) := btw.id_right _ _
-- @[simp] lemma mem_left : A ∈ A-ₛB := by { rw segment.mk_symm, apply mem_right }

-- lemma mem_segment_iff_btw : B ∈ A-ₛC ↔ btw A B C := iff.rfl
-- lemma btw_iff_mem_segment : btw A B C ↔ B ∈ A-ₛC := iff.rfl

-- lemma _root_.has_mem.mem.eq_of_trivial (h : B ∈ A-ₛA) : A = B := h.eq

-- lemma segment.trivial.eq_of_mem :
--   Π {l₁ : segment α} (h : l₁.trivial), A ∈ l₁ → A = h.point :=
-- begin
--   rw trivial_iff,
--   intros B hB,
--   apply hB.eq_of_trivial.symm,
-- end

-- lemma mem_trivial_iff : B ∈ A-ₛA ↔ A = B :=
-- ⟨λ h, h.eq_of_trivial, by { rintro rfl, simp }⟩

def segment.cong.setoid : setoid (segment α) := { r := _, iseqv := segment.cong.equivalence }

def nonneg (α : Type*) [tarski_neutral α] := quotient (@segment.cong.setoid α _)

-- def pre_add : segment α → segment α → segment α :=
-- sym2.lift ⟨λ A B, sym2.lift ⟨λ C D, A-ₛsegment_construct A B C D, λ C D, _⟩, _⟩
-- quotient.map₂ (λ (AB CD : α × α), ⟨AB.1, segment_construct AB.1 AB.2 CD.1 CD.2⟩)
--   begin
--     rintro ⟨A₁, B₁⟩ ⟨A₂, B₂⟩,

--   end

def segment.length (l₁ : segment α) : nonneg α := quotient.mk' l₁

def dist (A B : α) : nonneg α := (A-ₛB).length
lemma dist.symm {A B : α} : dist A B = dist B A := congr_arg segment.length segment.mk_symm

-- quotient.lift_on l₁ (λ AC, btw AC.1 B AC.2)
-- begin

-- --   have := begin
-- --   obtain ⟨x, hx₁, hx₂⟩ := inner_pasch h (btw.id_right B C),
-- --   cases hx₁.identity,
-- --   apply hx₂
-- -- end,
-- end

end tarski

-- class tarski_neutral_2d extends tarski_neutral α :=
-- (upper_dim : ∀ A B C P Q, P ≠ Q → cong A P A Q → cong B P B Q → cong C P C Q →
--   btw A B C ∨ btw B C A ∨ btw C A B)

-- class tarski_euclidean_2d extends tarski_neutral_2d α :=
-- (euclid : ∀ A B C D T, btw A D T → btw B D C → A ≠ D →
--   ∃ X Y, btw A B X ∧ btw A C Y ∧ btw X T Y)

-- class tarski extends tarski_euclidean_2d α :=
-- (continuity : ∀ (f g : α → Prop) A, (∀ X Y, f X → g Y → btw A X Y) →
--   ∃ B, ∀ X Y, f X ∧ g Y ∧ btw X B Y)
