import order.circular
import data.set_like.basic
import data.sym.sym2

variables (α : Type*) {A B C D E F P Q T X : α}

class has_cong :=
(cong : α → α → α → α → Prop)

class tarski_neutral extends has_btw α, has_cong α :=
(cong_pseudo_refl : ∀ {A B}, cong A B B A)
(cong_inner_trans : ∀ {A B C D E F}, cong A B C D → cong A B E F → cong C D E F)
(eq_of_cong_self : ∀ {A B C}, cong A B C C → A = B)
(segment_construction : ∀ A B C D, ∃ E, btw A B E ∧ cong B E C D)
(five_segment : ∀ {A A' B B' C C' D D'},
  cong A B A' B' → cong B C B' C' → cong A D A' D' → cong B D B' D' →
  btw A B C → btw A' B' C' → A ≠ B → cong C D C' D')
(eq_of_btw : ∀ {A B}, btw A B A → A = B)
(inner_pasch : ∀ {A B C P Q}, btw A P C → btw B Q C → ∃ X, btw P X B ∧ btw Q X A)
(lower_dim {} : ∃ A B C, ¬btw A B C ∧ ¬btw B C A ∧ ¬btw C A B)

namespace tarski

open tarski_neutral

def cong {α : Type*} [has_cong α] : α → α → α → α → Prop := has_cong.cong

def segment := sym2 α

variables {α} [tarski_neutral α]

lemma cong_pseudo_refl : cong A B B A := cong_pseudo_refl
lemma cong.inner_trans : cong A B C D → cong A B E F → cong C D E F := cong_inner_trans
lemma inner_pasch (APC : btw A P C) (BQC : btw B Q C) : ∃ X, btw P X B ∧ btw Q X A :=
inner_pasch APC BQC

def segment.trivial : sym2 α → Prop := sym2.is_diag

lemma cong_refl {A B : α} : cong A B A B :=
cong_pseudo_refl.inner_trans cong_pseudo_refl

lemma cong.symm (h : cong A B C D) : cong C D A B :=
h.inner_trans cong_refl

lemma cong.trans (h₁ : cong A B C D) (h₂ : cong C D E F) : cong A B E F :=
h₁.symm.inner_trans h₂

lemma cong.left_symm (h : cong A B C D) : cong B A C D :=
cong_pseudo_refl.symm.inner_trans h

def segment.mk : α → α → segment α := λ x y, quotient.mk (x, y)
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
sym2.lift ⟨λ A B, sym2.from_rel (λ (C D : α) (h : cong A B C D), h.symm.left_symm.symm),
  λ A B,
  begin
    ext CD,
    apply quotient.induction_on CD,
    rintro ⟨C, D⟩,
    exact ⟨cong.left_symm, cong.left_symm⟩,
  end⟩

infix ` ≡ `:80 := segment.cong

@[refl] lemma segment.cong.refl {l₁ : segment α} : l₁ ≡ l₁ :=
quotient.induction_on l₁ (λ ⟨A, B⟩, cong_refl)

@[symm] lemma segment.cong.symm {l₁ l₂ : segment α} : l₁ ≡ l₂ → l₂ ≡ l₁ :=
quotient.induction_on₂ l₁ l₂ (λ ⟨A, B⟩ ⟨C, D⟩, cong.symm)

lemma segment.cong.comm {l₁ l₂ : segment α} : l₁ ≡ l₂ ↔ l₂ ≡ l₁ :=
⟨λ h, h.symm, λ h, h.symm⟩

@[trans] lemma segment.cong.trans {l₁ l₂ l₃ : segment α} : l₁ ≡ l₂ → l₂ ≡ l₃ → l₁ ≡ l₃ :=
quotient.induction_on₂ l₂ l₃ (quotient.induction_on l₁ (λ ⟨A, B⟩ ⟨C, D⟩ ⟨E, F⟩, cong.trans))

lemma segment.cong.equivalence : equivalence (@segment.cong α _) :=
⟨λ x, segment.cong.refl, λ x y, segment.cong.symm, λ x y z, segment.cong.trans⟩

lemma exists_btw_cong (A B C D : α) : ∃ E, btw A B E ∧ B-ₛE ≡ C-ₛD :=
segment_construction A B C D

lemma segment.cong.eq_left : A-ₛB ≡ C-ₛC → A = B := eq_of_cong_self
lemma segment.cong.eq_right : A-ₛA ≡ B-ₛC → B = C := λ h, h.symm.eq_left
lemma segment.cong.empty_eq_empty : A-ₛA ≡ B-ₛB :=
begin
  obtain ⟨E, hE₁, hE₂⟩ := exists_btw_cong A B A A,
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

@[simp] lemma btw.id_right (A B : α) : btw A B B :=
begin
  obtain ⟨E, hE₁, hE₂⟩ := exists_btw_cong A B B B,
  cases hE₂.eq_left,
  apply hE₁
end

lemma _root_.has_btw.btw.eq : btw A B A → A = B := eq_of_btw

def segment.mem (B : α) : segment α → Prop :=
sym2.from_rel (λ A C (h : btw A B C),
  begin
    obtain ⟨X, BXB, CXA⟩ := inner_pasch h (btw.id_right B C),
    cases BXB.eq,
    apply CXA
  end)

instance : set_like (segment α) α := _
-- instance : has_coe (segment α) (set α) := ⟨λ h x, h.mem x⟩

@[simp] lemma mem_right : B ∈ (A-ₛB : set α) := btw.id_right _ _
@[simp] lemma mem_left : A ∈ A-ₛB := by { rw segment.mk_symm, apply mem_right }

lemma mem_segment_iff_btw : B ∈ A-ₛC ↔ btw A B C := iff.rfl
lemma btw_iff_mem_segment : btw A B C ↔ B ∈ A-ₛC := iff.rfl

lemma _root_.has_mem.mem.eq_of_trivial (h : B ∈ A-ₛA) : A = B := h.eq

lemma trivial_iff {p : Π {l : segment α} (h : l.trivial), Prop} :
  (∀ {l : segment α} (h : l.trivial), p h) ↔ ∀ A, p (segment.mk.trivial A) :=
begin
  split,
  { intros h A,
    apply h },
  intros h l,
  apply quotient.induction_on l,
  rintro ⟨_, _⟩ ⟨⟩,
  apply h,
end

lemma segment.trivial.eq_of_mem :
  Π {l₁ : segment α} (h : l₁.trivial), A ∈ l₁ → A = h.point :=
begin
  rw trivial_iff,
  intros B hB,
  apply hB.eq_of_trivial.symm,
end

lemma mem_trivial_iff : B ∈ A-ₛA ↔ A = B :=
⟨λ h, h.eq_of_trivial, by { rintro rfl, simp }⟩

def segment.cong.setoid : setoid (segment α) := { r := _, iseqv := segment.cong.equivalence }

def nonneg (α : Type*) [tarski_neutral α] := quotient (@segment.cong.setoid α _)

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
