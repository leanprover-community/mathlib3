/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import topology.basic

/-!
# Bitopological spaces
-/

variables {α : Type*}

class bitopological_space (α : Type*) :=
(topology_fst topology_snd : topological_space α)