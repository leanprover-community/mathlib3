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
