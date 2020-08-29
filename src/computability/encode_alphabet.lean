import data.fintype.basic
import data.num.lemmas
import tactic

namespace encoding
structure encoding (α : Type) :=
(Γ : Type)
(encode : α → list Γ)
(decode : list Γ → option α)
(encodek : ∀ x, decode(encode x) = some x )

structure fin_encoding (α : Type) extends encoding α :=
(Γ_fin : fintype Γ)

@[derive [inhabited,decidable_eq,fintype]]
inductive Γ₀₁
| bit0 | bit1

@[derive [decidable_eq,fintype]]
inductive Γ'
| blank | bit0 | bit1 | bra | ket | comma

instance inhabited_Γ' : inhabited Γ' := ⟨Γ'.blank⟩

def inclusion_Γ₀₁_Γ' : Γ₀₁ → Γ'
| Γ₀₁.bit0 := Γ'.bit0
| Γ₀₁.bit1 := Γ'.bit1

def section_Γ'_Γ₀₁ : Γ' → Γ₀₁
| Γ'.bit0 := Γ₀₁.bit0
| Γ'.bit1 := Γ₀₁.bit1
| _ := arbitrary Γ₀₁

lemma left_inverse_section_inclusion : function.left_inverse section_Γ'_Γ₀₁ inclusion_Γ₀₁_Γ' := begin intros x, cases x; trivial, end

lemma inclusion_Γ₀₁_Γ'_injective : function.injective inclusion_Γ₀₁_Γ' := by tidy

def encode_pos_num : pos_num → list Γ₀₁
| pos_num.one := [Γ₀₁.bit1]
| (pos_num.bit0 n) := Γ₀₁.bit0 :: encode_pos_num n
| (pos_num.bit1 n) := Γ₀₁.bit1 :: encode_pos_num n

def encode_num : num → list Γ₀₁
| num.zero := []
| (num.pos n) := encode_pos_num n

def encode_nat (n : ℕ) : list Γ₀₁ := encode_num n

def decode_pos_num : list Γ₀₁ → pos_num
| [Γ₀₁.bit1] := pos_num.one
| (Γ₀₁.bit0 :: l) := (pos_num.bit0 (decode_pos_num l))
| (Γ₀₁.bit1 :: l) := (pos_num.bit1 (decode_pos_num l))
| _ := pos_num.one

def decode_num : list Γ₀₁ → num
| [] := num.zero
| l := decode_pos_num l

def decode_nat : list Γ₀₁ → nat := λ l, decode_num l

def encode_pos_num_nonempty (n : pos_num) : (encode_pos_num n) ≠ [] :=
begin
  cases n with m,
  exact list.cons_ne_nil Γ₀₁.bit1 list.nil,
  exact list.cons_ne_nil Γ₀₁.bit1 (encode_pos_num m),
  exact list.cons_ne_nil Γ₀₁.bit0 (encode_pos_num n),
end

def encodek_pos_num : ∀ n, (decode_pos_num(encode_pos_num n) ) = n := begin
  intros n,
  induction n with m hm m hm,
  trivial,
  change decode_pos_num ((Γ₀₁.bit1) :: encode_pos_num m) = m.bit1,
  have h := encode_pos_num_nonempty m,
  calc decode_pos_num (Γ₀₁.bit1 :: encode_pos_num m)
    = pos_num.bit1 (decode_pos_num (encode_pos_num m)) : begin cases (encode_pos_num m), exfalso, trivial,trivial, end
    ... = m.bit1 : by rw hm,
  calc decode_pos_num (Γ₀₁.bit0 :: encode_pos_num m)
    = pos_num.bit0 (decode_pos_num (encode_pos_num m)) :  by trivial
    ... = m.bit0 : by rw hm,
end

def encodek_num : ∀ n, (decode_num(encode_num n) ) = n := begin
  intros n,
  cases n,
  trivial,
  change decode_num (encode_pos_num n) = num.pos n,
  have h : encode_pos_num n ≠ [] := encode_pos_num_nonempty n,
  have h' : decode_num (encode_pos_num n) = decode_pos_num (encode_pos_num n) := begin
    cases encode_pos_num n; trivial,
  end,
  rw h',
  rw (encodek_pos_num n),
  simp only [pos_num.cast_to_num],
end

def encodek_nat : ∀ n, (decode_nat(encode_nat n) ) = n := begin
  intros n,
  conv_rhs {rw ← num.to_of_nat n},
  exact congr_arg coe (encodek_num ↑n),
end

def encoding_nat_Γ₀₁ : encoding ℕ :=
{ Γ := Γ₀₁,
  encode := encode_nat,
  decode := λ n, option.some (decode_nat n),
  encodek := begin funext, simp, exact encodek_nat x end }

def fin_encoding_nat_Γ₀₁ : fin_encoding ℕ := ⟨ encoding_nat_Γ₀₁, Γ₀₁.fintype ⟩

def encoding_nat_Γ' : encoding ℕ :=
{ Γ := Γ',
  encode := (list.map inclusion_Γ₀₁_Γ') ∘ encode_nat,
  decode :=  option.some ∘ decode_nat ∘ (list.map section_Γ'_Γ₀₁),
  encodek := begin --TODO: golf
    funext,
    simp,
     have h : section_Γ'_Γ₀₁ ∘ inclusion_Γ₀₁_Γ' = id := begin funext, simp, exact left_inverse_section_inclusion x end,
    simp [h],
    exact encodek_nat x,
  end }

def fin_encoding_nat_Γ' : fin_encoding ℕ := ⟨ encoding_nat_Γ', Γ'.fintype ⟩

def unary_encode_nat : nat → list Γ₀₁ :=
| 0 := []
| (n+1) := Γ₀₁.bit1 :: (unary_encode_nat n)

def unary_decode_nat : list Γ₀₁ → nat := list.length

def unary_encodek_nat : ∀ n, unary_decode_nat (unary_encode_nat n) = n :=
λ n, nat.rec rfl (λ (m : ℕ) (hm : unary_decode_nat (unary_encode_nat m) = m), (congr_arg nat.succ hm.symm).symm) n

def unary_encoding_nat : encoding ℕ :=
{ Γ := Γ₀₁,
  encode := unary_encode_nat,
  decode := λ n, some (unary_decode_nat n),
  encodek := λ n, congr_arg _ (unary_encodek_nat n)}

def encode_bool : bool → list Γ₀₁
| ff := [Γ₀₁.bit0]
| tt := [Γ₀₁.bit1]

def decode_bool : list Γ₀₁ → bool
| [Γ₀₁.bit0] := ff
| [Γ₀₁.bit1] := tt
| _ := arbitrary bool

def encodek_bool : ∀ b, (decode_bool(encode_bool b)) = b := λ b, bool.cases_on b rfl rfl

def encoding_bool_Γ₀₁ : fin_encoding bool :=
{ Γ := Γ₀₁,
  encode := encode_bool,
  decode := λ x, some(decode_bool x),
  encodek := λ x, congr_arg _ ( encodek_bool x ),
  Γ_fin := Γ₀₁.fintype }

end encoding
