import data.set.basic tactic.ring

universe u

namespace loc

variables (α : Type u) [comm_ring α] (S : set α)

class is_submonoid : Prop :=
(one_mem : (1:α) ∈ S)
(mul_mem : ∀ {s t}, s ∈ S → t ∈ S → s*t ∈ S)

variable [is_submonoid α S]

instance : setoid (α × S) :=
{ r     := λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, ∃ t ∈ S, t * (r₁ * s₂ - r₂ * s₁) = 0,
  iseqv := ⟨λ ⟨r₁, s₁, hs₁⟩, ⟨1, is_submonoid.one_mem S, by simp⟩,
    λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨t, hts, ht⟩,
    ⟨t, hts, calc
             t * (r₂ * s₁ - r₁ * s₂)
           = -(t * (r₁ * s₂ - r₂ * s₁)) : by ring
       ... = 0 : by rw ht; simp⟩,
    λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨r₃, s₃, hs₃⟩ ⟨t, hts, ht⟩ ⟨t', hts', ht'⟩,
    ⟨t * t' * s₂, is_submonoid.mul_mem (is_submonoid.mul_mem hts hts') hs₂, calc
             t * t' * s₂ * (r₁ * s₃ - r₃ * s₁)
           = t' * s₃ * (t * (r₁ * s₂ - r₂ * s₁)) + t * s₁ * (t' * (r₂ * s₃ - r₃ * s₂)) : by ring
       ... = 0 : by rw [ht, ht']; simp⟩⟩ }

def loc := quotient $ loc.setoid α S

def add_aux : α × S → α × S → loc α S :=
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, ⟦⟨r₁ * s₂ + r₂ * s₁, s₁ * s₂, is_submonoid.mul_mem hs₁ hs₂⟩⟧

def add : loc α S → loc α S → loc α S :=
quotient.lift₂ (add_aux α S) $
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨r₃, s₃, hs₃⟩ ⟨r₄, s₄, hs₄⟩ ⟨t₅, hts₅, ht₅⟩ ⟨t₆, hts₆, ht₆⟩,
quotient.sound ⟨t₅ * t₆, is_submonoid.mul_mem hts₅ hts₆, calc
        t₅ * t₆ * ((r₁ * s₂ + r₂ * s₁) * (s₃ * s₄) - (r₃ * s₄ + r₄ * s₃) * (s₁ * s₂))
      = t₆ * (t₅ * (r₁ * s₃ - r₃ * s₁)) * s₂ * s₄ + t₅ * (t₆ * (r₂ * s₄ - r₄ * s₂)) * s₁ * s₃ : by ring
  ... = 0 : by rw [ht₅, ht₆]; simp⟩

def neg_aux : α × S → loc α S :=
λ ⟨r, s, hs⟩, ⟦⟨-r, s, hs⟩⟧

def neg : loc α S → loc α S :=
quotient.lift (neg_aux α S) $
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨t, hts, ht⟩,
quotient.sound ⟨t, hts, calc
        t * (-r₁ * s₂ - -r₂ * s₁)
      = -(t * (r₁ * s₂ - r₂ * s₁)) : by ring
  ... = 0 : by rw ht; simp⟩

def mul_aux : α × S → α × S → loc α S :=
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, ⟦⟨r₁ * r₂, s₁ * s₂, is_submonoid.mul_mem hs₁ hs₂⟩⟧

def mul : loc α S → loc α S → loc α S :=
quotient.lift₂ (mul_aux α S) $
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨r₃, s₃, hs₃⟩ ⟨r₄, s₄, hs₄⟩ ⟨t₅, hts₅, ht₅⟩ ⟨t₆, hts₆, ht₆⟩,
quotient.sound ⟨t₅ * t₆, is_submonoid.mul_mem hts₅ hts₆, calc
        t₅ * t₆ * ((r₁ * r₂) * (s₃ * s₄) - (r₃ * r₄) * (s₁ * s₂))
      = t₆ * (t₅ * (r₁ * s₃ - r₃ * s₁)) * r₂ * s₄ + t₅ * (t₆ * (r₂ * s₄ - r₄ * s₂)) * r₃ * s₁ : by ring
  ... = 0 : by rw [ht₅, ht₆]; simp⟩

instance : comm_ring (loc α S) :=
by refine
{ add            := add α S,
  add_assoc      := λ m n k, quotient.induction_on₃ m n k _,
  zero           := ⟦⟨0, 1, is_submonoid.one_mem S⟩⟧,
  zero_add       := quotient.ind _,
  add_zero       := quotient.ind _,
  neg            := neg α S,
  add_left_neg   := quotient.ind _,
  add_comm       := quotient.ind₂ _,
  mul            := mul α S,
  mul_assoc      := λ m n k, quotient.induction_on₃ m n k _,
  one            := ⟦⟨1, 1, is_submonoid.one_mem S⟩⟧,
  one_mul        := quotient.ind _,
  mul_one        := quotient.ind _,
  left_distrib   := λ m n k, quotient.induction_on₃ m n k _,
  right_distrib  := λ m n k, quotient.induction_on₃ m n k _,
  mul_comm       := quotient.ind₂ _ };
{ intros,
  try {cases a with r₁ s₁, cases s₁ with s₁ hs₁},
  try {cases b with r₂ s₂, cases s₂ with s₂ hs₂},
  try {cases c with r₃ s₃, cases s₃ with s₃ hs₃},
  apply quotient.sound,
  existsi (1:α),
  existsi is_submonoid.one_mem S,
  ring }

end loc
