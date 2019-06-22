import tactic.rewrite_search.discovery.bundle

import category_theory.natural_isomorphism
import category_theory.products
import category_theory.types

namespace tactic.rewrite_search.discovery

@[bundle] meta def category_theory : bundle := {}

open category_theory

attribute [search category_theory] category.id_comp category.comp_id category.assoc
attribute [search category_theory] category_theory.functor.map_id category_theory.functor.map_comp
attribute [search category_theory] nat_trans.naturality nat_trans.vcomp_app nat_trans.hcomp_app nat_trans.exchange
attribute [search category_theory] prod_id prod_comp functor.prod_obj functor.prod_map nat_trans.prod_app
attribute [search category_theory] nat_trans.id_app nat_trans.comp_app nat_trans.app_naturality nat_trans.naturality_app
attribute [search category_theory] functor_to_types.map_comp functor_to_types.map_id functor_to_types.naturality
attribute [search category_theory] iso.hom_inv_id iso.inv_hom_id is_iso.hom_inv_id is_iso.inv_hom_id

attribute [search category_theory] nat_iso.naturality_1 nat_iso.naturality_2

attribute [search category_theory] full.witness functor.image_preimage

end tactic.rewrite_search.discovery