-- open native
open tactic

@[user_attribute]
meta def example_attribute : user_attribute unit unit := {
  name := `example,
  descr := "An example attribute",
  cache_cfg :=
   { mk_cache := λ ls, (do trace format!"names: {ls}"),
     dependencies := [] },
  after_set := some $ λ name priority persistent, (do trace format!"set {name}"),
  before_unset := some $ λ name persistent, (do trace format!"unset {name}")
}

def f := 3
def g := 4

section
local attribute [example] f
local attribute [-example] f
local attribute [example] f
end -- Notice no "unset" at the end of the section?

section
run_cmd success_if_fail (example_attribute.get_param `f >>= trace)

local attribute [example] f
run_cmd example_attribute.get_param `f >>= trace
end

set_option trace.user_attributes_cache true
attribute [example] f

run_cmd example_attribute.get_cache >>= trace

-- it seems non-deterministic whether this next line finds a cached value
run_cmd example_attribute.get_cache >>= trace

attribute [example] g

run_cmd example_attribute.get_cache >>= trace
run_cmd example_attribute.get_cache >>= trace

attribute [example] g

run_cmd example_attribute.get_cache >>= trace
run_cmd example_attribute.get_cache >>= trace
