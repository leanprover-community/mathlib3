/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton, Simon Hudon, Kenny Lau

Opposites.
-/

namespace opposite
universes v u -- declare the `v` first; see `category_theory.category` for an explanation
variable (α : Sort u)

/-- The type of objects of the opposite of `α`; used to defined opposite category/group/...

  In order to avoid confusion between `α` and its opposite type, we
  set up the type of objects `opposite α` using the following pattern,
  which will be repeated later for the morphisms.

  1. Define `opposite α := α`.
  2. Define the isomorphisms `op : α → opposite α`, `unop : opposite α → α`.
  3. Make the definition `opposite` irreducible.

  This has the following consequences.

  * `opposite α` and `α` are distinct types in the elaborator, so you
    must use `op` and `unop` explicitly to convert between them.
  * Both `unop (op X) = X` and `op (unop X) = X` are definitional
    equalities. Notably, every object of the opposite category is
    definitionally of the form `op X`, which greatly simplifies the
    definition of the structure of the opposite category, for example.

  (If Lean supported definitional eta equality for records, we could
  achieve the same goals using a structure with one field.)
-/
def opposite : Sort u := α

-- Use a high right binding power (like that of postfix ⁻¹) so that, for example,
-- `presheaf Cᵒᵖ` parses as `presheaf (Cᵒᵖ)` and not `(presheaf C)ᵒᵖ`.
notation α `ᵒᵖ`:std.prec.max_plus := opposite α

variables {α}

def op : α → αᵒᵖ := id
def unop : αᵒᵖ → α := id

lemma op_inj : function.injective (op : α → αᵒᵖ) := λ _ _, id
lemma unop_inj : function.injective (unop : αᵒᵖ → α) := λ _ _, id

@[simp] lemma op_unop (x : αᵒᵖ) : op (unop x) = x := rfl
@[simp] lemma unop_op (x : α) : unop (op x) = x := rfl

attribute [irreducible] opposite

def op_induction {F : Π (X : αᵒᵖ), Sort v} (h : Π X, F (op X)) : Π X, F X :=
λ X, h (unop X)
end opposite

namespace tactic.interactive

open interactive interactive.types lean.parser tactic

meta def op_induction (h : parse ident) : tactic unit :=
do h' ← tactic.get_local h,
   revert_lst [h'],
   applyc `opposite.op_induction,
   tactic.intro h,
   skip

end tactic.interactive


