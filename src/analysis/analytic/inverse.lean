/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import analysis.analytic.composition

noncomputable theory

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{G : Type*} [normed_group G] [normed_space 𝕜 G]
{H : Type*} [normed_group H] [normed_space 𝕜 H]

open filter list
open_locale topological_space classical
