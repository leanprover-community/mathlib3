# Library Style Guidelines #
Author: [Jeremy Avigad](http://www.andrew.cmu.edu/user/avigad)

In addition to the [naming conventions](naming.md),
files in the Lean library generally adhere to the following guidelines
and conventions. Having a uniform style makes it easier to browse the
library and read the contents, but these are meant to be guidelines
rather than rigid rules.

### Variable conventions ###

- `u`, `v`, `w`, ... for universes
- `α`, `β`, `γ`, ... for types
- `a`, `b`, `c`, ... for propositions
- `x`, `y`, `z`, ... for elements of a generic type
- `h`, `h₁`, ...     for assumptions
- `p`, `q`, `r`, ... for predicates and relations
- `s`, `t`, ...      for lists
- `s`, `t`, ...      for sets
- `m`, `n`, `k`, ... for natural numbers
- `i`, `j`, `k`, ... for integers



### Line length ###

Lines should not be longer than 100 characters. This makes files
easier to read, especially on a small screen or in a small window.

### Header and imports ###

The file header should contain copyright information, a list of all
the authors who have worked on the file, and a description of the
contents. Do all `import`s right after the header, without a line
break. You can also open namespaces in the same block.

```lean
/-
Copyright (c) 2015 Joe Cool. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joe Cool.

A theory of everything.
-/
import data.nat algebra.group
open nat eq.ops
```

### Structuring definitions and theorems ###

Use spaces around ":", ":=" or infix operators. Put them before a line break rather
than at the beginning of the next line.

Use two spaces to indent. You can use an extra indent when a long line
forces a break to suggest the break is artificial rather than
structural, as in the statement of theorem:

```lean
open nat
theorem two_step_induction_on {P : nat → Prop} (a : nat) (H1 : P 0) (H2 : P (succ 0))
    (H3 : ∀ (n : nat) (IH1 : P n) (IH2 : P (succ n)), P (succ (succ n))) : P a :=
sorry
```

If you want to indent to make parameters line up, that is o.k. too:
```lean
open nat
theorem two_step_induction_on {P : nat → Prop} (a : nat) (H1 : P 0) (H2 : P (succ 0))
                              (H3 : ∀ (n : nat) (IH1 : P n) (IH2 : P (succ n)), P (succ (succ n))) :
  P a :=
sorry
```

After stating the theorem, we generally do not indent the first line
of a proof, so that the proof is "flush left" in the file.
```lean
open nat
theorem nat_case {P : nat → Prop} (n : nat) (H1: P 0) (H2 : ∀m, P (succ m)) : P n :=
nat.induction_on n H1 (assume m IH, H2 m)
```

When a proof rule takes multiple arguments, it is sometimes clearer, and often
necessary, to put some of the arguments on subsequent lines. In that case,
indent each argument.
```lean
open nat
axiom zero_or_succ (n : nat) : n = zero ∨ n = succ (pred n)
theorem nat_discriminate {B : Prop} {n : nat} (H1: n = 0 → B)
  (H2 : ∀m, n = succ m → B) : B :=
or.elim (zero_or_succ n)
  (assume H3 : n = zero, H1 H3)
  (assume H3 : n = succ (pred n), H2 (pred n) H3)
```
Don't orphan parentheses; keep them with their arguments.

Here is a longer example.
```lean
open list
variable {T : Type}

theorem mem_split {x : T} {l : list T} : x ∈ l → ∃s t : list T, l = s ++ (x::t) :=
list.rec_on l
  (assume H : x ∈ [], false.elim (iff.elim_left (mem_nil_iff _) H))
  (assume y l,
    assume IH : x ∈ l → ∃s t : list T, l = s ++ (x::t),
    assume H : x ∈ y::l,
    or.elim (eq_or_mem_of_mem_cons H)
      (assume H1 : x = y,
        exists.intro [] (exists.intro l (by rw H1; refl)))
      (assume H1 : x ∈ l,
        let ⟨s, (H2 : ∃t : list T, l = s ++ (x::t))⟩ := IH H1,
            ⟨t, (H3 : l = s ++ (x::t))⟩ := H2 in
        have H4 : y :: l = (y::s) ++ (x::t), by rw H3; refl,
        exists.intro (y::s) (exists.intro t H4)))

```

A short definition can be written on a single line:
```lean
open nat
definition square (x : nat) : nat := x * x
```
For longer definitions, use conventions like those for theorems.

A "have" / "from" pair can be put on the same line.
```lean
have H2 : n ≠ succ k, from subst (ne_symm (succ_ne_zero k)) (symm H),
[...]
```
You can also put it on the next line, if the justification is long.
```lean
have H2 : n ≠ succ k,
  from subst (ne_symm (succ_ne_zero k)) (symm H),
[...]
```
If the justification takes more than a single line, keep the "from" on the same
line as the "have", and then begin the justification indented on the next line.
```lean
have n ≠ succ k, from
  not_intro
    (assume H4 : n = succ k,
      have H5 : succ l = succ k, from trans (symm H) H4,
      have H6 : l = k, from succ_inj H5,
      absurd H6 H2)))),
[...]
```

When the arguments themselves are long enough to require line breaks, use
an additional indent for every line after the first, as in the following
example:
```lean
open nat eq algebra
theorem add_right_inj {n m k : nat} : n + m = n + k → m = k :=
nat.rec_on n
  (assume H : 0 + m = 0 + k,
    calc
        m = 0 + m : eq.symm (zero_add m)
      ... = 0 + k : H
      ... = k     : zero_add _)
  (assume (n : nat) (IH : n + m = n + k → m = k) (H : succ n + m = succ n + k),
    have H2 : succ (n + m) = succ (n + k), from
      calc
        succ (n + m) = succ n + m   : eq.symm (succ_add n m)
                 ... = succ n + k   : H
                 ... = succ (n + k) : succ_add n k,
    have H3 : n + m = n + k, from succ.inj H2,
    IH H3)
```

In a class or structure definition, we do not indent fields, as in:

```lean
structure principal_seg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends r ≼o s :=
(top : β)
(down : ∀ b, s b top ↔ ∃ a, to_order_embedding a = b)

class module (α : out_param $ Type u) (β : Type v) [out_param $ ring α]
  extends has_scalar α β, add_comm_group β :=
(smul_add : ∀r (x y : β), r • (x + y) = r • x + r • y)
(add_smul : ∀r s (x : β), (r + s) • x = r • x + s • x)
(mul_smul : ∀r s (x : β), (r * s) • x = r • s • x)
(one_smul : ∀x : β, (1 : α) • x = x)
```

When using a constructor taking several arguments in a definition,
arguments line up, as in:

```lean
theorem sub_eq_zero_iff_le {a b : ordinal} : a - b = 0 ↔ a ≤ b :=
⟨λ h, by simpa [h] using le_add_sub a b,
 λ h, by rwa [← le_zero, sub_le, add_zero]⟩
```

When defining instances, opening and closing braces are not alone on
their line. The content is indented by two spaces and `:=` line up, as
in:

```lean
instance : partial_order (topological_space α) :=
{ le          := λt s, t.is_open ≤ s.is_open,
  le_antisymm := assume t s h₁ h₂, topological_space_eq $ le_antisymm h₁ h₂,
  le_refl     := assume t, le_refl t.is_open,
  le_trans    := assume a b c h₁ h₂, @le_trans _ _ a.is_open b.is_open c.is_open h₁ h₂ }
```

### Binders ###

Use a space after binders:
```lean
example : ∀ α : Type, ∀ x : α, ∃ y, y = x :=
λ (α : Type) (x : α), exists.intro x rfl
```

### Calculations ###

There is some flexibility in how you write calculational proofs. In
general, it looks nice when the comparisons and justifications line up
neatly:
```lean
import data.list
open list
variable {α : Type}

theorem reverse_reverse : ∀ (l : list α), reverse (reverse l) = l
| []       := rfl
| (a :: l) := calc
    reverse (reverse (a :: l)) = reverse (concat a (reverse l))     : rfl
                           ... = reverse (reverse l ++ [a])         : concat_eq_append
                           ... = reverse [a] ++ reverse (reverse l) : reverse_append
                           ... = reverse [a] ++ l                   : reverse_reverse
                           ... = a :: l                             : rfl
```

To be more compact, for example, you may do this only after the first line:

```lean
import data.list
open list
variable {α : Type}

theorem reverse_reverse : ∀ (l : list α), reverse (reverse l) = l
| []       := rfl
| (a :: l) := calc
    reverse (reverse (a :: l))
          = reverse (concat a (reverse l))     : rfl
      ... = reverse (reverse l ++ [a])         : concat_eq_append
      ... = reverse [a] ++ reverse (reverse l) : reverse_append
      ... = reverse [a] ++ l                   : reverse_reverse
      ... = a :: l                             : rfl
```


### Tactic mode ###

When opening a tactic block, `begin` is not indented but everything
inside is indented, as in:

```lean
lemma div_self (a : α) : a ≠ 0 → a / a = (1:α) :=
begin
  intro hna,
  have wit_aa := quotient_mul_add_remainder_eq a a,
  have a_mod_a := mod_self a,
  dsimp [(%)] at a_mod_a,
  simp [a_mod_a] at wit_aa,
  have h1 : 1 * a = a, from one_mul a,
  conv at wit_aa {for a [4] {rw ←h1}},
  exact eq_of_mul_eq_mul_right hna wit_aa
end
```

A more complicated example, mixing term mode and tactic mode:
```lean
lemma nhds_supr {ι : Sort w} {t : ι → topological_space α} {a : α} :
  @nhds α (supr t) a = (⨅i, @nhds α (t i) a) :=
le_antisymm
  (le_infi $ assume i, nhds_mono $ le_supr _ _)
  begin
    rw [supr_eq_generate_from, nhds_generate_from],
    exact (le_infi $ assume s, le_infi $ assume ⟨hs, hi⟩,
      begin
        simp at hi, cases hi with i hi,
        exact (infi_le_of_le i $ le_principal_iff.mpr $ @mem_nhds_sets α (t i) _ _ hi hs)
      end)
  end
```

When new goals arise as side conditions or steps, they are enclosed in
focussing braces and indented. Braces are not alone on their line.

```lean
lemma mem_nhds_of_is_topological_basis {a : α} {s : set α} {b : set (set α)}
  (hb : is_topological_basis b) : s ∈ (𝓝 a).sets ↔ ∃t∈b, a ∈ t ∧ t ⊆ s :=
begin
  rw [hb.2.2, nhds_generate_from, infi_sets_eq'],
  { simpa [and_comm, and.left_comm] },
  { exact assume s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩,
      have a ∈ s ∩ t, from ⟨hs₁, ht₁⟩,
      let ⟨u, hu₁, hu₂, hu₃⟩ := hb.1 _ hs₂ _ ht₂ _ this in
      ⟨u, ⟨hu₂, hu₁⟩, by simpa using hu₃⟩ },
  { suffices : a ∈ (⋃₀ b), { simpa [and_comm] },
    { rw [hb.2.1], trivial } }
end
```

Often `t0 ; t1` is used to execute `t0` and then `t1` on all new goals. But `;` is not a `,` so
either write the tactics in one line, or indent the following tacic.

```lean
begin
  cases x;
    simp [a, b, c, d]
end
```


### Sections ###

Within a section, you can indent definitions and theorems to make the
scope salient:
```lean
section my_section
  variable α : Type
  variable P : Prop

  definition foo (x : α) : α := x

  theorem bar (H : P) : P := H
end my_section
```
If the section is long, however, you can omit the indents.

We generally use a blank line to separate theorems and definitions,
but this can be omitted, for example, to group together a number of
short definitions, or to group together a definition and notation.

## Comments

Use comment delimiters `/- -/` to provide section headers and
separators, and for long comments. Use `--` for short or in-line
comments.

Documentation strings for declarations are delimited with `/-- -/`.
Documentation strings for modules are delimited with `/-! -/`.

------
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
