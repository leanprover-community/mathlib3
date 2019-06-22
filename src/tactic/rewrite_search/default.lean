-- Provide the interactive tactics
import .interactive

-- We include the shipped library of strategies, metrics, and tracers
import .strategy
import .metric
import .tracer

-- Include the library of bundles
import .bundles
-- Include the `suggestion` command for convenient hint semantics
import tactic.rewrite_search.command.suggestion
