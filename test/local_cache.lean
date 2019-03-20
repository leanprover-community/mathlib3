import tactic.local_cache

open tactic

section example_tactic

def TEST_NS : name := `my_tactic

-- Example "expensive" function
meta def generate_some_data : tactic (list ℕ) :=
do trace "cache regenerating",
   return [1, 2, 3, 4]

meta def my_tactic : tactic unit :=
do my_cached_data ← run_once TEST_NS generate_some_data,
   -- Do some stuff with `my_cached_data`
   skip

end example_tactic



section example_usage

-- Note only a single cache regeneration (only a single trace message),
-- even upon descent to a sub-tactic-block.
lemma my_lemma : true := begin
    my_tactic,
    my_tactic,
    my_tactic,

    have h : true,
    { my_tactic,
      trivial },

    trivial
end

end example_usage

section test

meta def fail_if_cache_miss : tactic unit :=
do p ← local_cache.present TEST_NS,
   if p then skip else fail "cache miss"

meta def clear_cache : tactic unit := local_cache.clear TEST_NS

lemma my_test : true := begin
    success_if_fail { fail_if_cache_miss },

    my_tactic,

    fail_if_cache_miss,
    fail_if_cache_miss,

    have h : true,
    { fail_if_cache_miss,
      trivial },

    clear_cache,
    success_if_fail { fail_if_cache_miss },

    trivial
end

end test
