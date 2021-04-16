/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import order.conditionally_complete_lattice

/-!
# Tooling to make copies of lattice structures

Sometimes it is useful to make a copy of a lattice structure
where one replaces the data parts with provably equal definitions
that have better definitional properties.
-/

universe variable u

variables {α : Type u}

/-- A function to create a provable equal copy of a bounded lattice
with possibly different definitional equalities. -/
def bounded_lattice.copy (c : bounded_lattice α)
  (le : α → α → Prop) (eq_le : le = @bounded_lattice.le α c)
  (top : α) (eq_top : top = @bounded_lattice.top α c)
  (bot : α) (eq_bot : bot = @bounded_lattice.bot α c)
  (sup : α → α → α) (eq_sup : sup = @bounded_lattice.sup α c)
  (inf : α → α → α) (eq_inf : inf = @bounded_lattice.inf α c) :
  bounded_lattice α :=
begin
  refine { le := le, top := top, bot := bot, sup := sup, inf := inf, .. },
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
    .. bounded_lattice.copy (@complete_lattice.to_bounded_lattice α c)
      le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf,
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
begin
  refine { le := le, top := top, bot := bot, sup := sup, inf := inf, Sup := Sup, Inf := Inf,
    .. complete_lattice.copy (@complete_distrib_lattice.to_complete_lattice α c)
      le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf Sup eq_Sup Inf eq_Inf,
    .. },
  all_goals { abstract { subst_vars, casesI c, assumption } }
end

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
