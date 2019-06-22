import tactic.rewrite_search

open tactic.rewrite_search.discovery

namespace tactic.rewrite_search.testing

@[bundle] meta def algebraic_geometry : bundle := {}

private axiom foo : [0] = [1]
private axiom bar1 : [1] = [2]
private axiom bar2 : [3] = [2]
private axiom bar3 : [3] = [4]

private def my_example (a : unit) : [[0],[0]] = [[4],[4]] :=
begin
  -- These don't work (because they don't know about the lemmas):
  success_if_fail { rewrite_search },
  success_if_fail { rewrite_search_using [`search] },

  -- But manually specifying them does:
  rewrite_search_with [foo, bar1, ← bar2, bar2, ← bar3],
end

-- Let's add them to the `algebraic_geometry` bundle:
attribute [search algebraic_geometry] foo bar1 bar2 bar3

-- Now because they are under the `search xxx` namespace whatever,
-- the following "old" thing will succeed

private example : [[0],[0]] = [[4],[4]] :=
begin
  rewrite_search_using [`search],
end

-- And manually suggesting the `algebraic_geometry` bundle
-- will work too:

private example : [[0],[0]] = [[4],[4]] :=
begin
  rewrite_search {suggest := [`algebraic_geometry]}
end

-- Finally (and probably most commonly), you can suggest some number
-- of bundles via:

@[suggest] meta def my_suggestion := `algebraic_geometry

-- or:

@[suggest] meta def my_suggestion2 := [`algebraic_geometry, `default]

-- The discovery code will accept both a name, or a list of names,
-- as tagged with `[suggest]`.

-- This is pretty cool, because any number of suggestions will be
-- considered and are available to the `rewrite_search`er, not
-- just the last one to be tagged `[suggest]` or something.
--
-- Also, you can use `local attribute xxx` and imports to constrain
-- the scope of where your suggestions apply, just like you were
-- doing before with [search] in the category theory library.



-- In terms of using `[search xxx]`, the attribute will accept any
-- `xxx` which is a bundle which has already been declared as
-- `@[bundle]`. You can also leave the `xxx` off and just annotate
-- as `@[search]`, which will add the lemma to all of the default
-- bundles. At the moment, the list consists of only one bundle, and
-- it is called `default`.
--
-- Lemmas can be part of multiple bundles too simultanously, either
-- with annotations declared in separate places, or in the same place
-- via the list syntax:

@[search [algebraic_geometry, default]] private axiom bar4 : [3] = [4]

-- (Here we add `bar4` to both `algebraic_geometry` and `default`
-- at the same time.)





-- When `rewrite_search` goes to run, it does not do several ugly
-- attribute lookups over all bundles, and then all of their children.
-- Instead, all of the membership is cached at *parse* time via
-- some tricky (if I do say so myself ;)) hiding and updating of
-- mutable state in annotations. In fact, we even cache the
-- resolved names of which bundles you refer to when you annotate
-- with `@[suggest]` (and then forget this state when you go out
-- of scope).





-- The idea is to have builtin bundles under
--
--    tactic.rewrite_search.discovery.bundles
--
-- which are imported everytime you include
--
--    tactic.rewrite_search
--
-- but as you can see, anyone can create one or modify an existing one
-- on the fly.





-- One more thing: the bundle names ARE NOT the names of objects
-- declared of type bundle. They are anything you want, and can
-- choosen as you like:

@[bundle] meta def scotts_fave_bundle : bundle := {name := `the_real_name}

-- And so this will work:

@[search the_real_name] private axiom bar5 : [3] = [4]

-- but this will not:

-- UNCOMMENT ME
-- @[search scotts_fave_bundle] private axiom bar4 : [3] = [4]

-- This was intentional, because I didn't want the fully-scoped identifier
-- to have to be available and `open`ed, or fully-qualified, when
-- you go to write `@[search xxxx]`.
--
-- I used some autoparams tricks to default the name of a bundle
-- to its "lowest level" identifier (i.e. after the last dot).
-- So in practise this means it always gets the name you expect,
-- and you don't have to write it.





-- We also fail gracefully if you try to break the rules:

-- UNCOMMENT ME:
-- @[suggest] meta def my_suggestion_rebel : ℕ := 0

-- UNCOMMENT ME:
-- @[suggest] meta def my_suggestion_rebel2 : name := `fake_name

-- Everything else gracefully handles errors, too:

private example : tt :=
begin
-- UNCOMMENT ME:
  -- rewrite_search {suggest := [`algssebraic_geometry]},

  exact dec_trivial
end

end tactic.rewrite_search.testing
