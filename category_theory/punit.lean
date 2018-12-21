-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.const

universes u v w

namespace category_theory

instance punit_category : small_category punit :=
{ hom  := λ X Y, punit,
  id   := λ _, punit.star,
  comp := λ _ _ _ _ _, punit.star }

end category_theory
