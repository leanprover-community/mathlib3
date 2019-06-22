import .bundle

namespace tactic.rewrite_search.discovery

-- I've resisted the urge to pick funny vague adjectives here even though it kills me
-- I can only dream: (resolute, determined, obstinate, unwavering, etc.)
--               vs. (idle, indolent, etc.)
@[derive decidable_eq]
inductive persistence
| speedy
| try_bundles
| try_everything

export persistence (speedy)
export persistence (try_bundles)
export persistence (try_everything)

def persistence.level : persistence → ℕ
| speedy         := 0
| try_bundles    := 1
| try_everything := 2

instance : has_lt persistence := ⟨λ a b, a.level < b.level⟩
instance : has_le persistence := ⟨λ a b, a.level ≤ b.level⟩

meta structure progress :=
(persistence  : persistence)
(seen_bundles : list bundle_ref)

end tactic.rewrite_search.discovery