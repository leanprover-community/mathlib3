import tactic.rewrite_search.discovery.bundle

namespace tactic.rewrite_search.discovery

@[bundle] meta def logic : bundle := {}

attribute [search logic] not_not not_or_distrib not_not
attribute [search logic] and_assoc and_comm and_not_self_iff and_false
attribute [search logic] imp_iff_not_or

end tactic.rewrite_search.discovery