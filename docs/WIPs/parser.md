# The Parser #

[Note that this file was written by someone (Kevin Buzzard) who knows absolutely nothing about what the parser and elaborator etc do, and has just cut and pasted off gitter and then added in some stuff which is probably hugely inaccurate.]

The parser is the piece of (C++ I think) code which analyses what you've typed in and figures out some basic stuff about it before feeding it to Lean itself. For example it unravels all notation (I think), including numbers: you type 13 but by the time the parser (more precisely the number literal parser) has finished with it looks like

```
@bit1.{0} nat nat.has_one nat.has_add
  (@bit0.{0} nat nat.has_add (@bit1.{0} nat nat.has_one nat.has_add (@has_one.one.{0} nat nat.has_one))) :
  nat
```

as you will be able to verify yourself if you type

```
set_option pp.all true
#check 13
```

The *elaborator* then goes through and replaces all occurrences of functions `f` with things like `@f _ _`, and then replaces all the `_`s with stuff like `?m_7`. The elaborator then invokes the unifier, which tries to unify metavariables.

After that, the *typechecker* tries to figure out the type of everything.

After that, the *kernel* has a go at what is left.


TODO : add standard common errors which each part of the procedure throws up when it fails, to help the user better understand which part of the procedure is failing.
