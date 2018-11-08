-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.whiskering
import category_theory.limits.limits

open category_theory

namespace category_theory.limits

universes u₁ u₂ v

variables {C : Type u₁} [𝒞 : category.{u₁ v} C]
variables {D : Type u₂} [𝒟 : category.{u₂ v} D]
include 𝒞 𝒟

variables {J : Type v} [small_category J] {K : J ⥤ C}

-- FIXME Reid's suggestion using forall, also for all variants of has_limits

class preserves_limit (K : J ⥤ C) (F : C ⥤ D) :=
(preserves : Π {c : cone K}, is_limit c → is_limit (F.map_cone c))
class preserves_colimit (K : J ⥤ C) (F : C ⥤ D) :=
(preserves : Π {c : cocone K}, is_colimit c → is_colimit (F.map_cocone c))

class preserves_limits_of_shape (J : Type v) [small_category J] (F : C ⥤ D) :=
(preserves : Π {K : J ⥤ C} {c : cone K}, is_limit c → is_limit (F.map_cone c))
class preserves_colimits_of_shape (J : Type v) [small_category J] (F : C ⥤ D) :=
(preserves : Π {K : J ⥤ C} {c : cocone K}, is_colimit c → is_colimit (F.map_cocone c))

class preserves_limits (F : C ⥤ D) :=
(preserves : Π {J : Type v} [small_category J] {K : J ⥤ C} {c : cone K},
  is_limit c → is_limit (F.map_cone c))
class preserves_colimits (F : C ⥤ D) :=
(preserves : Π {J : Type v} [small_category J] {K : J ⥤ C} {c : cocone K},
  is_colimit c → is_colimit (F.map_cocone c))

instance preserves_limit_of_preserves_limits_of_shape
  (K : J ⥤ C) (F : C ⥤ D) [preserves_limits_of_shape J F] :
  preserves_limit K F :=
{ preserves := λ _, preserves_limits_of_shape.preserves F }

instance preserves_limits_of_shape_of_preserves_limit (F : C ⥤ D) [preserves_limits F] :
  preserves_limits_of_shape J F :=
{ preserves := λ _ _, preserves_limits.preserves F }

-- def preserves_limit.is_limit {F : C ⥤ D} [preserves_limit K F]
--   {c : cone K} (h : is_limit c) : is_limit (F.map_cone c) :=
-- preserves_limit.preserves F h

class reflects_limit (K : J ⥤ C) (F : C ⥤ D) :=
(reflects : Π {c : cone K}, is_limit (F.map_cone c) → is_limit c)

class reflects_limits_of_shape (J : Type v) [small_category J] (F : C ⥤ D) :=
(reflects : Π {K : J ⥤ C} {c : cone K}, is_limit (F.map_cone c) → is_limit c)

class reflects_limits (F : C ⥤ D) :=
(reflects : Π {J : Type v} [small_category J] {K : J ⥤ C} {c : cone K},
  is_limit (F.map_cone c) → is_limit c)

instance reflects_limit_of_reflects_limits_of_shape
  (K : J ⥤ C) (F : C ⥤ D) [reflects_limits_of_shape J F] :
  reflects_limit K F :=
{ reflects := λ _, reflects_limits_of_shape.reflects }

instance reflects_limits_of_shape_of_reflects_limit (F : C ⥤ D) [reflects_limits F] :
  reflects_limits_of_shape J F :=
{ reflects := λ _ _, reflects_limits.reflects }

class creates_limit (K : J ⥤ C) (F : C ⥤ D) extends reflects_limit K F :=
(creates : Π {c : cone (K ⋙ F)}, is_limit c → cone K)
(image_is_limit : Π {c : cone (K ⋙ F)} (h : is_limit c), is_limit (F.map_cone (creates h)))

class creates_limits_of_shape
  (J : Type v) [small_category J] (F : C ⥤ D) extends reflects_limits_of_shape J F :=
(creates : Π {K : J ⥤ C} {c : cone (K ⋙ F)}, is_limit c → cone K)
(image_is_limit : Π {K : J ⥤ C} {c : cone (K ⋙ F)} (h : is_limit c),
  is_limit (F.map_cone (creates h)))

class creates_limits (F : C ⥤ D) extends reflects_limits F :=
(creates : Π {J : Type v} [small_category J] {K : J ⥤ C} {c : cone (K ⋙ F)}, is_limit c → cone K)
(image_is_limit :
  Π {J : Type v} [small_category J] {K : J ⥤ C} {c : cone (K ⋙ F)} (h : is_limit c),
  is_limit (F.map_cone (creates h)))

instance creates_limit_of_creates_limits_of_shape
  (K : J ⥤ C) (F : C ⥤ D) [creates_limits_of_shape J F] :
  creates_limit K F :=
{ creates := λ _, creates_limits_of_shape.creates,
  image_is_limit := λ _, creates_limits_of_shape.image_is_limit }

instance creates_limits_of_shape_of_creates_limit (F : C ⥤ D) [creates_limits F] :
  creates_limits_of_shape J F :=
{ creates := λ _ _, creates_limits.creates,
  image_is_limit := λ _ _, creates_limits.image_is_limit }

def creates_limit.is_limit {F : C ⥤ D} [creates_limit K F]
  {c : cone (K ⋙ F)} (h : is_limit c) : is_limit (creates_limit.creates h) :=
reflects_limit.reflects (creates_limit.image_is_limit h)

-- Specific instances of this may be turned into instances.
def preserved_limit (F : C ⥤ D) [preserves_limit K F] [has_limit K] : has_limit (K ⋙ F) :=
{ cone := F.map_cone (limit.cone K),
  is_limit := preserves_limit.preserves F (limit.universal_property K) }

-- Specific instances of this may be turned into instances.
def created_limit (F : C ⥤ D) [creates_limit K F] [has_limit (K ⋙ F)] : has_limit K :=
{ cone := creates_limit.creates (limit.universal_property (K ⋙ F)),
  is_limit := creates_limit.is_limit (limit.universal_property (K ⋙ F)) }

def created_limits_of_shape
  (F : C ⥤ D) [creates_limits_of_shape J F] [has_limits_of_shape.{u₂ v} J D] :
  has_limits_of_shape.{u₁ v} J C :=
{ cone := λ G, creates_limit.creates (limit.universal_property (G ⋙ F)),
  is_limit := λ G, creates_limit.is_limit (limit.universal_property (G ⋙ F)) }

def created_limits (F : C ⥤ D) [creates_limits F] [has_limits.{u₂ v} D] : has_limits.{u₁ v} C :=
{ cone := λ J 𝒥 G,
  begin
    resetI,
    exact creates_limit.creates (limit.universal_property (G ⋙ F)),
  end,
  is_limit := λ J 𝒥 G,
  begin
    resetI,
    exact creates_limit.is_limit (limit.universal_property (G ⋙ F)),
  end }

-- TODO
-- instance preserves_created_limit
--   (F : C ⥤ D) [creates_limit K F] [has_limit (K ⋙ F)] : preserves_limit K F :=
-- { preserves := sorry } -- See second half of Proposition 3.3.3 of Category Theory in Context

/-
TODO: Any full and faithful functor reflects any limits and colimits that are present
in its codomain.

TODO: Any equivalence of categories preserves, reflects, and creates any limits and
colimits that are present in its domain or codomain.
-/

def preserves_limits_of_preserves_limits_of_all_shapes
  {F : C ⥤ D} [∀ (J : Type v) [small_category J], preserves_limits_of_shape J F] :
  preserves_limits F :=
{ preserves := λ J 𝒥, by resetI; exact λ K c, preserves_limits_of_shape.preserves F }
def preserves_colimits_of_preserves_colimits_of_all_shapes
  {F : C ⥤ D} [∀ (J : Type v) [small_category J], preserves_colimits_of_shape J F] :
  preserves_colimits F :=
{ preserves := λ J 𝒥, by resetI; exact λ K c, preserves_colimits_of_shape.preserves F }


end category_theory.limits