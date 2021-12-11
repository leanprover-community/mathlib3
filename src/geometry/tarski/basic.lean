import order.circular
import data.set_like.basic
import data.sym.sym2

variables (α : Type*) {A B C D E F A' B' C' D' E' P Q : α}

class has_cong :=
(cong : α → α → α → α → Prop)

class tarski_neutral extends has_btw α, has_cong α :=
(cong_pseudo_refl : ∀ {A B}, cong A B B A)
(cong_inner_trans : ∀ {A B C D E F}, cong A B C D → cong A B E F → cong C D E F)
(eq_of_cong_self : ∀ {A B C}, cong A B C C → A = B)
(segment_construct_trunc' : ∀ (A B C D), trunc {E // btw A B E ∧ cong B E C D})
(five_segment' : ∀ {A A' B B' C C' D D'},
  cong A B A' B' → cong B C B' C' → cong A D A' D' → cong B D B' D' →
  btw A B C → btw A' B' C' → A ≠ B → cong C D C' D')
(eq_of_btw : ∀ {A B}, btw A B A → A = B)
(inner_pasch_trunc : ∀ {A B C P Q}, btw A P C → btw B Q C → trunc {X // btw P X B ∧ btw Q X A})
(lower_dim {} : ∃ A B C, ¬btw A B C ∧ ¬btw B C A ∧ ¬btw C A B)

namespace tarski

open tarski_neutral

def cong {α : Type*} [has_cong α] : α → α → α → α → Prop := has_cong.cong

def segment := sym2 α

variables {α} [tarski_neutral α]

lemma cong_pseudo_refl : cong A B B A := cong_pseudo_refl
lemma cong.inner_trans : cong A B C D → cong A B E F → cong C D E F := cong_inner_trans
lemma inner_pasch (APC : btw A P C) (BQC : btw B Q C) : ∃ X, btw P X B ∧ btw Q X A :=
trunc.rec_on_subsingleton (inner_pasch_trunc APC BQC) subtype.exists_of_subtype

/-- A segment is trivial if the endpoints are equal. (Called Nullstrecken in [SST]) -/
def segment.trivial : sym2 α → Prop := sym2.is_diag

/-- (Implementation) before we define notation for `cong`. Lemma 2.1 of [SST] -/
lemma cong_refl {A B : α} : cong A B A B :=
cong_pseudo_refl.inner_trans cong_pseudo_refl

/-- (Implementation) before we define notation for `cong`. Lemma 2.2 of [SST] -/
lemma cong.symm (h : cong A B C D) : cong C D A B :=
h.inner_trans cong_refl

/-- (Implementation) before we define notation for `cong`. Lemma 2.3 of [SST] -/
lemma cong.trans (h₁ : cong A B C D) (h₂ : cong C D E F) : cong A B E F :=
h₁.symm.inner_trans h₂

/-- (Implementation) before we define notation for `cong`. Lemma 2.4 of [SST] -/
lemma cong.left_swap (h : cong A B C D) : cong B A C D :=
cong_pseudo_refl.symm.inner_trans h

/-- Construct the segment given two endpoints. Compare Definition 2.6 of [SST] -/
def segment.mk : α → α → segment α := λ x y, ⟦(x, y)⟧
infix `-ₛ`:99 := segment.mk

@[simp] lemma quotient_mk_eq : ⟦(A, B)⟧ = A-ₛB := rfl

@[simp] lemma segment.mk.trivial_iff : (A-ₛB).trivial ↔ A = B := sym2.is_diag_iff_eq
lemma segment.mk.trivial (A : α) : (A-ₛA).trivial := by simp

def segment.trivial.point : Π {l₁ : segment α}, l₁.trivial → α :=
quotient.rec (λ a _, a.1)
begin
  rintro _ _ ⟨⟩,
  { refl },
  { ext ⟨⟩, refl }
end

@[simp] lemma segment.trivial_mk_point {A : α} : (segment.mk.trivial A).point = A := rfl

lemma segment.mk_symm : A-ₛB = B-ₛA := sym2.eq_swap

def segment.cong : segment α → segment α → Prop :=
sym2.lift ⟨λ A B, sym2.from_rel (λ (C D : α) (h : cong A B C D), h.symm.left_swap.symm),
  λ A B,
  begin
    ext CD,
    apply quotient.induction_on CD,
    rintro ⟨C, D⟩,
    exact ⟨cong.left_swap, cong.left_swap⟩,
  end⟩

infix ` ≡ `:80 := segment.cong

lemma segment.cong.left_swap {l : segment α} (h : A-ₛB ≡ l) : B-ₛA ≡ l :=
by rwa segment.mk_symm

lemma segment.cong.right_swap {l : segment α} (h : l ≡ A-ₛB) : l ≡ B-ₛA :=
by rwa segment.mk_symm

lemma segment.cong.swap (h : A-ₛB ≡ C-ₛD) : B-ₛA ≡ D-ₛC :=
h.left_swap.right_swap

lemma segment_construct_trunc (A B C D : α) : trunc {E // btw A B E ∧ B-ₛE ≡ C-ₛD} :=
segment_construct_trunc' A B C D

lemma five_segment {A' B' C' D' : α} (AB : A-ₛB ≡ A'-ₛB') (BC : B-ₛC ≡ B'-ₛC') (AD : A-ₛD ≡ A'-ₛD')
  (BD : B-ₛD ≡ B'-ₛD') (ABC : btw A B C) (ABC' : btw A' B' C') (nAB : A ≠ B) :
  C-ₛD ≡ C'-ₛD' :=
five_segment' AB BC AD BD ABC ABC' nAB

@[refl] lemma segment.cong_refl (l₁ : segment α) : l₁ ≡ l₁ :=
quotient.induction_on l₁ (λ ⟨A, B⟩, cong_refl)

@[symm] lemma segment.cong.symm {l₁ l₂ : segment α} : l₁ ≡ l₂ → l₂ ≡ l₁ :=
quotient.induction_on₂ l₁ l₂ (λ ⟨A, B⟩ ⟨C, D⟩, cong.symm)

lemma segment.cong.comm {l₁ l₂ : segment α} : l₁ ≡ l₂ ↔ l₂ ≡ l₁ :=
⟨λ h, h.symm, λ h, h.symm⟩

@[trans] lemma segment.cong.trans {l₁ l₂ l₃ : segment α} : l₁ ≡ l₂ → l₂ ≡ l₃ → l₁ ≡ l₃ :=
quotient.induction_on₂ l₂ l₃ (quotient.induction_on l₁ (λ ⟨A, B⟩ ⟨C, D⟩ ⟨E, F⟩, cong.trans))

/-- Congruence of segments is an equivalence relation. Lemma 2.7 of [SST]. -/
lemma segment.cong.equivalence : equivalence (@segment.cong α _) :=
⟨λ x, x.cong_refl, λ x y, segment.cong.symm, λ x y z, segment.cong.trans⟩

instance : is_refl (segment α) (≡) := ⟨segment.cong_refl⟩
instance : is_symm (segment α) (≡) := ⟨λ _ _, segment.cong.symm⟩
instance : is_trans (segment α) (≡) := ⟨λ _ _ _, segment.cong.trans⟩

lemma exists_btw_cong (A B C D : α) : ∃ E, btw A B E ∧ B-ₛE ≡ C-ₛD :=
trunc.rec_on_subsingleton (segment_construct_trunc A B C D) subtype.exists_of_subtype

lemma segment.cong.eq_left : A-ₛB ≡ C-ₛC → A = B := eq_of_cong_self
lemma segment.cong.eq_right : A-ₛA ≡ B-ₛC → B = C := λ h, h.symm.eq_left

/-- Trivial segments are congruent. Lemma 2.8 of [SST]. -/
lemma trivial_cong_trivial : A-ₛA ≡ B-ₛB :=
begin
  obtain ⟨E, hE₁, hE₂⟩ := exists_btw_cong A B A A,
    -- This proof idea looks weird, but it's pretty common in Tarski's geometry. See Note 2.9
    -- of [SST].
  cases hE₂.eq_left,
  apply hE₂.symm
end

lemma segment.cong.eq_iff (h : A-ₛB ≡ C-ₛD) : A = B ↔ C = D :=
⟨λ t, segment.cong.eq_right (by simpa [t] using h),
 λ t, segment.cong.eq_left (by simpa [t] using h)⟩

lemma segment.cong.trivial_iff {l₁ l₂ : segment α} : l₁ ≡ l₂ → (l₁.trivial ↔ l₂.trivial) :=
quotient.induction_on₂ l₁ l₂
begin
  rintro ⟨A, B⟩ ⟨C, D⟩,
  apply segment.cong.eq_iff,
end

lemma segment.cong.ne_of_ne (h₁ : A-ₛB ≡ C-ₛD) (h₂ : A ≠ B) : C ≠ D :=
begin
  rintro rfl,
  apply h₂ h₁.eq_left,
end

lemma _root_.ne.ne_of_cong (h₁ : A ≠ B) (h₂ : A-ₛB ≡ C-ₛD) : C ≠ D :=
h₂.ne_of_ne h₁

/-- Part of Lemma 2.12 of [SST]. -/
lemma segment_construct_unique {E F : α} (nAB : A ≠ B) (hE₁ : btw A B E) (hE₂ : B-ₛE ≡ C-ₛD)
  (hF₁ : btw A B F) (hF₂ : B-ₛF ≡ C-ₛD) : E = F :=
(five_segment (refl _) (hE₂.trans hF₂.symm) (refl _) (refl _) hE₁ hF₁ nAB).eq_left

/--
If `A ≠ B`, there is a unique point `E` such that `A-B-E` are in a line and `BE = CD`.
Note that if `A = B` then uniqueness fails.
Lemma 2.12 of [SST].
-/
lemma exists_unique_btw_cong (nAB : A ≠ B) : ∃! E, btw A B E ∧ B-ₛE ≡ C-ₛD :=
exists_unique_of_exists_of_unique (exists_btw_cong _ _ _ _)
  (λ E F ⟨hE₁, hE₂⟩ ⟨hF₁, hF₂⟩, segment_construct_unique nAB hE₁ hE₂ hF₁ hF₂)

/-- Addition of segments on a line. A special case of showing addition of lengths is well-defined.
Lemma 2.11 of [SST]. -/
lemma cong_add_cong (h₁ : btw A B C) (h₂ : btw A' B' C') (h₃ : A-ₛB ≡ A'-ₛB') (h₄ : B-ₛC ≡ B'-ₛC') :
  A-ₛC ≡ A'-ₛC' :=
begin
  rcases eq_or_ne A B with rfl | nAB,
  { cases h₃.eq_right,
    apply h₄ },
  apply (five_segment h₃ h₄ trivial_cong_trivial h₃.swap h₁ h₂ nAB).swap,
end

/-- Betweenness is weak on the right. Lemma 3.1 of [SST]. -/
@[simp] lemma btw_id_right (A B : α) : btw A B B :=
begin
  obtain ⟨E, hE₁, hE₂⟩ := exists_btw_cong A B B B,
  cases hE₂.eq_left,
  apply hE₁
end

end tarski

section btw

variables {α} [tarski_neutral α]

open tarski tarski_neutral

/-- If B is between A and A, then `A = B`. Axiom A6 of [SST]. -/
lemma has_btw.btw.eq : btw A B A → A = B := eq_of_btw

/-- If B is between A and A, then `B = A`. Axiom A6 of [SST]. -/
lemma has_btw.btw.eq' (h : btw A B A) : B = A := h.eq.symm

/-- Betweenness is symmetric. Lemma 3.2 of [SST]. -/
@[symm] lemma has_btw.btw.symm (h : btw A B C) : btw C B A :=
by { obtain ⟨X, BXB, CXA⟩ := inner_pasch h (btw_id_right B C), cases BXB.eq, apply CXA }

lemma tarski.btw_comm : btw A B C ↔ btw C B A :=
⟨λ h, h.symm, λ h, h.symm⟩

/-- Betweenness is weak on the left. Lemma 3.3 of [SST]. -/
@[simp] lemma tarski.btw_id_left (A B : α) : btw A A B := (btw_id_right _ _).symm
lemma btw_id (A : α) : btw A A A := btw_id_right _ _

/-- Lemma 3.4 of [SST]. -/
lemma has_btw.btw.antisymm_left (h₁ : btw A B C) (h₂ : btw B A C) : A = B :=
by { obtain ⟨x, hx₁, hx₂⟩ := inner_pasch h₁ h₂, cases hx₁.eq, apply hx₂.eq }

lemma has_btw.btw.antisymm_right (h₁ : btw A B C) (h₂ : btw A C B) : B = C :=
(h₁.symm.antisymm_left h₂.symm).symm

/-- First part of Lemma 3.6 of [SST]. -/
lemma has_btw.btw.left_cancel (h₁ : btw A B C) (h₂ : btw A C D) : btw B C D :=
by { obtain ⟨x, hx₁, hx₂⟩ := inner_pasch h₂.symm h₁.symm, cases hx₁.eq, apply hx₂ }

/-- First part of Lemma 3.5 of [SST]. -/
lemma has_btw.btw.right_cancel (h₁ : btw A B D) (h₂ : btw B C D) : btw A B C :=
(h₂.symm.left_cancel h₁.symm).symm

/-- First part of Lemma 3.7 of [SST]. -/
lemma has_btw.btw.trans_right (h₁ : btw A B C) (h₂ : btw B C D) (h₃ : B ≠ C) : btw A C D :=
begin
  obtain ⟨E, hE₁, hE₂⟩ := exists_btw_cong A C C D,
  rwa ←segment_construct_unique h₃ (h₁.left_cancel hE₁) hE₂ h₂ (refl _),
end

/-- Second part of Lemma 3.5 of [SST]. -/
lemma has_btw.btw.right_trans (h₁ : btw A B D) (h₂ : btw B C D) : btw A C D :=
begin
  rcases eq_or_ne B C with rfl | nBC,
  { exact h₁ },
  exact (h₁.right_cancel h₂).trans_right h₂ nBC,
end

/-- Second part of Lemma 3.6 of [SST]. -/
lemma has_btw.btw.left_trans (h₁ : btw A B C) (h₂ : btw A C D) : btw A B D :=
(h₂.symm.right_trans h₁.symm).symm

/-- Second part of Lemma 3.7 of [SST]. -/
lemma has_btw.btw.trans_left (h₁ : btw A B C) (h₂ : btw B C D) (h₃ : B ≠ C) : btw A B D :=
(h₂.symm.trans_right h₁.symm h₃.symm).symm

lemma has_btw.btw.eq_left_of_eq (h : btw A B C) : A = C → A = B :=
by { rintro rfl, apply h.eq }

lemma has_btw.btw.eq_right_of_eq (h : btw A B C) : A = C → B = C :=
by { rintro rfl, apply h.eq' }

lemma has_btw.btw.ne_of_ne_left (h : btw A B C) : A ≠ B → A ≠ C :=
mt h.eq_left_of_eq

lemma has_btw.btw.ne_of_ne_right (h : btw A B C) : B ≠ C → A ≠ C :=
mt h.eq_right_of_eq

end btw

def name.add_suffix : name → string → name
| (name.mk_string n s) t := name.mk_string (n ++ t) s
| n _ := n

namespace tactic

meta def assertv_if_new (h : name) (t : expr) (v : expr) : tactic expr :=
find_assumption t <|> assertv h t v

meta def note_if_new (h : name) (t : option expr := none) (pr : expr) : tactic expr :=
let dv := λ t, assertv_if_new h t pr in
  option.cases_on t (infer_type pr >>= dv) dv

meta def note_anon_if_new (t : option expr := none) (pr : expr) : tactic expr :=
get_unused_name `h >>= λ h, note_if_new h t pr

meta def forward_btw_symm (e : expr) : tactic unit :=
do `(btw %%A %%B %%C) ← infer_type e,
   nm ← get_unused_name (e.local_pp_name.add_suffix "_symm"),
   pf ← to_expr ``(has_btw.btw.symm %%e),
   note_if_new nm none pf,
   skip

meta def forward_btw_symms : tactic unit :=
local_context >>= list.mmap' (try ∘ forward_btw_symm)

meta def is_trivial_btw : expr → bool
| `(btw %%A %%B %%C) := (A = B) || (B = C)
| _ := ff

meta def is_btw : expr → option (expr × expr × expr)
| `(btw %%A %%B %%C) := some (A, B, C)
| _ := none

meta def clear_trivial_btw : tactic unit :=
local_context >>= list.mmap' (λ e, mwhen (is_trivial_btw <$> infer_type e) (clear e))

meta def register_new (h : name) (args : list expr) : tactic unit :=
mk_app h args >>= note_anon_if_new none >> skip

meta def forward_btw : expr × expr → expr × expr → tactic unit
| (e₁, `(btw %%A %%B %%C)) (e₂, `(btw %%D %%E %%F)) :=
  monad.unlessb (A = D ∧ B = E ∧ C = F) $
    if A = D ∧ C = E
      then monad.unlessb (B = F) $
            register_new `has_btw.btw.left_trans [e₁, e₂] >>
            register_new `has_btw.btw.left_cancel [e₁, e₂]
      else
        if C = F ∧ B = D
          then monad.unlessb (A = C) $
                register_new `has_btw.btw.right_trans [e₁, e₂] >>
                register_new `has_btw.btw.right_cancel [e₁, e₂]
          else skip
| _ _ := fail "not given btw values"

meta def btw_core : tactic unit :=
do clear_trivial_btw,
   ctx ← local_context,
   ctx' ← list.mmap infer_type ctx,
   let ct : list (expr × expr) := list.filter (λ i, (is_btw i.2).is_some) (list.zip ctx ctx'),
   list.mmap' (function.uncurry forward_btw) (ct.product ct)

meta def btw_trivial : tactic unit :=
do `(btw %%A %%B %%C) ← target,
   if A = B
      then applyc `tarski.btw_id_left
      else if B = C
            then applyc `tarski.btw_id_right
            else failed

meta def btw (hyps : list pexpr) : tactic unit :=
btw_trivial <|>
do
  hyps.mmap' (λ e, to_expr e >>= note_anon_if_new none),
  btw_core,
  try assumption

setup_tactic_parser

meta def interactive.btw (hyps : parse pexpr_list?) : tactic unit :=
btw (hyps.get_or_else [])

end tactic

section btw

variables {α} [tarski_neutral α]

open tarski tarski_neutral

lemma segment_eq_of_btw_iff (h : ∀ X, btw A X B ↔ btw C X D) :
  A-ₛB = C-ₛD :=
begin
  rw [←quotient_mk_eq, ←quotient_mk_eq, sym2.eq_iff, or_iff_not_imp_right, not_and_distrib],
  rintro (nAD | nBC),
  { have := ((h A).1 (btw_id_left _ _)).trans_left ((h D).2 (btw_id_right _ _)) nAD,
    refine ⟨((h C).2 (btw_id_left _ _)).antisymm_left this, _⟩,
    btw [(h D).2 (by btw), (h B).1 (by btw)],
    exact h_5.antisymm_right h_1 },
  { have := ((h C).2 (btw_id_left _ _)).trans_left ((h B).1 (btw_id_right _ _)) (ne.symm nBC),
    refine ⟨this.antisymm_left ((h A).1 (btw_id_left _ _)), _⟩,
    have := this.right_trans ((h B).1 (btw_id_right _ _)),
    exact this.antisymm_right ((h _).2 (btw_id_right _ _)) }
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
  intros P Q hP hQ,
  exact (B.left_trans (list.rel_of_pairwise_cons h.1 hP)).left_cancel,
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
  refine ⟨segment_construct Y X X Y, X, Y :: l, by simp [llength], _, _⟩,
  { apply n_btw_cons_cons_cons (segment_construct_btw _ _ _ _).symm nXY lbtw },
  rw [list.nodup_cons, and_iff_left lnodup, list.mem_cons_iff, list.mem_cons_iff, not_or_distrib,
    not_or_distrib],
  refine ⟨nXY.segment_construct_ne_snd, nXY.symm.segment_construct_ne_fst, λ hl, _⟩,
  exact nXY ((btw_of_n_btw_cons_cons lbtw _ hl).antisymm_left (segment_construct_btw Y X X Y)),
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
