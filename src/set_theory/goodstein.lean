import set_theory.ordinal_notation

namespace onote

/-- An `onote` represents a hereditary base-`b` expansion whenever all of its coefficients are less
    than `b`. -/
def is_hereditary : onote → ℕ → Prop
| 0 b            := tt
| (oadd e n a) b := is_hereditary e b ∧ n.1 < b

theorem zero_is_hereditary (b : ℕ) : is_hereditary 0 b :=
by exact rfl

/-- Replacing `ω` with a natural number `b`, computes the value of the notation. -/
def to_nat (b : ℕ) : onote → ℕ
| 0            := 0
| (oadd e n a) := b ^ (to_nat e) * n + (to_nat a)

end onote

/-- A hereditary base-`b` expansion is like a regular base-`b` expansion, but the exponents are
    recursively expanded as well. We represent this as an `nonote` whose coefficients are all less
    than `b`. This avoids a lot of code duplication, and makes the correspondence with ordinals
    immediate. -/
def hereditary (b : ℕ) : Type 0 :=
{e : nonote // e.1.is_hereditary b}

instance (b : ℕ) : has_zero (hereditary b) := ⟨⟨0, onote.zero_is_hereditary b⟩⟩
instance (b : ℕ) : inhabited (hereditary b) := ⟨0⟩

namespace hereditary

def oadd {b} (e : hereditary b) {n : ℕ+} (hn : n.1 < b) (a : hereditary b)
  (h : nonote.below a.1 e.1) : hereditary b :=
⟨nonote.oadd e.1 n a.1 h, e.2, hn⟩

def to_string {b : ℕ} (r : hereditary b) : string :=
r.1.1.to_string_with_base (to_string b)

/-- The ordinal represented by a hereditary base-`b` expansion, after changing all instances of `b`
    to `ω`. -/
noncomputable def repr {b : ℕ} (r : hereditary b) : ordinal :=
r.1.repr

theorem unique_hereditary_of_le_one {b : ℕ} (hb : b ≤ 1) : unique (hereditary b) :=
⟨by apply_instance, begin
  rintro ⟨(_ | ⟨e, n, a⟩), he⟩,
  { refl },
  { unfold onote.is_hereditary at he,
    exact ((pnat.one_le n).not_lt (he.2.trans_le hb)).elim }
end⟩

instance unique_hereditary_zero : unique (hereditary 0) :=
unique_hereditary_of_le_one zero_le_one

instance unique_hereditary_one : unique (hereditary 1) :=
unique_hereditary_of_le_one le_rfl

/-- Computes the value of the notation. -/
def to_nat {b : ℕ} (e : hereditary b) : ℕ :=
e.1.1.to_nat b

end hereditary
