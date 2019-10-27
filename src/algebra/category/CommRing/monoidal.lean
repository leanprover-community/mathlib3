/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.CommRing.colimits
import category_theory.monoidal.of_has_finite_products

universe v

instance : monoidal_category CommRing.{v} :=
monoidal_of_has_finite_coproducts CommRing
