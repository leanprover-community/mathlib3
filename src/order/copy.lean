/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import order.conditionally_complete_lattice.basic

/-!
# Tooling to make copies of lattice structures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Sometimes it is useful to make a copy of a lattice structure
where one replaces the data parts with provably equal definitions
that have better definitional properties.
-/

open order

universe u

variables {α : Type u}

/-- A function to create a provable equal copy of a bounded order
with possibly different definitional equalities. -/
def bounded_order.copy {h : has_le α} {h' : has_le α} (c : @bounded_order α h')
  (top : α) (eq_top : top = @bounded_order.top α _ c)
  (bot : α) (eq_bot : bot = @bounded_order.bot α _ c)
  (le_eq : ∀ (x y : α), ((@has_le.le α h) x y) ↔ x ≤ y) :
  @bounded_order α h :=
begin
  refine { top := top, bot := bot, .. },
  all_goals { abstract { subst_vars, casesI c, simp_rw le_eq, assumption } }
end

/-- A function to create a provable equal copy of a lattice
with possibly different definitional equalities. -/
def lattice.copy (c : lattice α)
  (le : α → α → Prop) (eq_le : le = @lattice.le α c)
  (sup : α → α → α) (eq_sup : sup = @lattice.sup α c)
  (inf : α → α → α) (eq_inf : inf = @lattice.inf α c) :
  lattice α :=
begin
  refine { le := le, sup := sup, inf := inf, .. },
  all_goals { abstract { subst_vars, casesI c, assumption } }
end

/-- A function to create a provable equal copy of a distributive lattice
with possibly different definitional equalities. -/
def distrib_lattice.copy (c : distrib_lattice α)
  (le : α → α → Prop) (eq_le : le = @distrib_lattice.le α c)
  (sup : α → α → α) (eq_sup : sup = @distrib_lattice.sup α c)
  (inf : α → α → α) (eq_inf : inf = @distrib_lattice.inf α c) :
  distrib_lattice α :=
begin
  refine { le := le, sup := sup, inf := inf, .. },
  all_goals { abstract { subst_vars, casesI c, assumption } }
end

/-- A function to create a provable equal copy of a complete lattice
with possibly different definitional equalities. -/
def complete_lattice.copy (c : complete_lattice α)
  (le : α → α → Prop) (eq_le : le = @complete_lattice.le α c)
  (top : α) (eq_top : top = @complete_lattice.top α c)
  (bot : α) (eq_bot : bot = @complete_lattice.bot α c)
  (sup : α → α → α) (eq_sup : sup = @complete_lattice.sup α c)
  (inf : α → α → α) (eq_inf : inf = @complete_lattice.inf α c)
  (Sup : set α → α) (eq_Sup : Sup = @complete_lattice.Sup α c)
  (Inf : set α → α) (eq_Inf : Inf = @complete_lattice.Inf α c) :
  complete_lattice α :=
begin
  refine { le := le, top := top, bot := bot, sup := sup, inf := inf, Sup := Sup, Inf := Inf,
    .. lattice.copy (@complete_lattice.to_lattice α c)
      le eq_le sup eq_sup inf eq_inf,
    .. },
  all_goals { abstract { subst_vars, casesI c, assumption } }
end

/-- A function to create a provable equal copy of a frame with possibly different definitional
equalities. -/
def frame.copy (c : frame α)
  (le : α → α → Prop) (eq_le : le = @frame.le α c)
  (top : α) (eq_top : top = @frame.top α c)
  (bot : α) (eq_bot : bot = @frame.bot α c)
  (sup : α → α → α) (eq_sup : sup = @frame.sup α c)
  (inf : α → α → α) (eq_inf : inf = @frame.inf α c)
  (Sup : set α → α) (eq_Sup : Sup = @frame.Sup α c)
  (Inf : set α → α) (eq_Inf : Inf = @frame.Inf α c) :
  frame α :=
begin
  refine { le := le, top := top, bot := bot, sup := sup, inf := inf, Sup := Sup, Inf := Inf,
    .. complete_lattice.copy (@frame.to_complete_lattice α c)
      le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf Sup eq_Sup Inf eq_Inf,
    .. },
  all_goals { abstract { subst_vars, casesI c, assumption } }
end

/-- A function to create a provable equal copy of a coframe with possibly different definitional
equalities. -/
def coframe.copy (c : coframe α)
  (le : α → α → Prop) (eq_le : le = @coframe.le α c)
  (top : α) (eq_top : top = @coframe.top α c)
  (bot : α) (eq_bot : bot = @coframe.bot α c)
  (sup : α → α → α) (eq_sup : sup = @coframe.sup α c)
  (inf : α → α → α) (eq_inf : inf = @coframe.inf α c)
  (Sup : set α → α) (eq_Sup : Sup = @coframe.Sup α c)
  (Inf : set α → α) (eq_Inf : Inf = @coframe.Inf α c) :
  coframe α :=
begin
  refine { le := le, top := top, bot := bot, sup := sup, inf := inf, Sup := Sup, Inf := Inf,
    .. complete_lattice.copy (@coframe.to_complete_lattice α c)
      le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf Sup eq_Sup Inf eq_Inf,
    .. },
  all_goals { abstract { subst_vars, casesI c, assumption } }
end

/-- A function to create a provable equal copy of a complete distributive lattice
with possibly different definitional equalities. -/
def complete_distrib_lattice.copy (c : complete_distrib_lattice α)
  (le : α → α → Prop) (eq_le : le = @complete_distrib_lattice.le α c)
  (top : α) (eq_top : top = @complete_distrib_lattice.top α c)
  (bot : α) (eq_bot : bot = @complete_distrib_lattice.bot α c)
  (sup : α → α → α) (eq_sup : sup = @complete_distrib_lattice.sup α c)
  (inf : α → α → α) (eq_inf : inf = @complete_distrib_lattice.inf α c)
  (Sup : set α → α) (eq_Sup : Sup = @complete_distrib_lattice.Sup α c)
  (Inf : set α → α) (eq_Inf : Inf = @complete_distrib_lattice.Inf α c) :
  complete_distrib_lattice α :=
{ .. frame.copy (@complete_distrib_lattice.to_frame α c)
      le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf Sup eq_Sup Inf eq_Inf,
  .. coframe.copy (@complete_distrib_lattice.to_coframe α c)
      le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf Sup eq_Sup Inf eq_Inf}

/-- A function to create a provable equal copy of a conditionally complete lattice
with possibly different definitional equalities. -/
def conditionally_complete_lattice.copy (c : conditionally_complete_lattice α)
  (le : α → α → Prop) (eq_le : le = @conditionally_complete_lattice.le α c)
  (sup : α → α → α) (eq_sup : sup = @conditionally_complete_lattice.sup α c)
  (inf : α → α → α) (eq_inf : inf = @conditionally_complete_lattice.inf α c)
  (Sup : set α → α) (eq_Sup : Sup = @conditionally_complete_lattice.Sup α c)
  (Inf : set α → α) (eq_Inf : Inf = @conditionally_complete_lattice.Inf α c) :
  conditionally_complete_lattice α :=
begin
  refine { le := le, sup := sup, inf := inf, Sup := Sup, Inf := Inf, ..},
  all_goals { abstract { subst_vars, casesI c, assumption } }
end
