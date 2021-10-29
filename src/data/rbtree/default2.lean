/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.rbtree.basic

meta def rbtree.default_lt : tactic unit :=
`[apply has_lt.lt]
