# Simp #

The `simp` tactic works by applying a conditional term rewriting system to try and prove, or at least simplify, your goal. What this basically means is that `simp` is equipped with a list of lemmas (those tagged with the `simp` attribute), many of which are of the form `X = Y` or `X iff Y`, and attempts to match subterms of the goal with the left hand side of a rule, and then replaces the subterm with the right hand side. The system is conditional in the sense that lemmas are allowed to have preconditions (`P -> (X = Y)`) and in these cases it will try and prove the precondition using its simp lemmas before applying `X = Y`.

You can watch simp in action by using `set_option trace.simplify true` in your code. For example

```lean
namespace hidden

definition cong (a b m : ℤ) : Prop := ∃ n : ℤ, b - a = m * n

notation a ` ≡ ` b ` mod ` m  := cong a b m 
set_option trace.simplify true
theorem cong_refl (m : ℤ) : ∀ a : ℤ, a ≡ a mod m :=
begin
intro a,
unfold cong,
existsi (0:ℤ),
simp
end

end hidden
```

If you do this exercise you will discover firstly that simp spends a lot of its time trying random lemmas and then giving up very shortly afterwards, and also that the `unfold` command is also underlined in green -- Lean seems to apply simp when you do an unfold as well (apparently unfold just asks simp to do its dirty work for it -- `unfold X` is close to `simp only [X]`).

If you only want to see what worked rather than all the things that didn't, you could try `set_option trace.simplify.rewrite true`.

### Simp lemmas

In case you want to train simp to use certain extra lemmas (for example because they're coming up again and again in your work) you can add new lemmas for yourself. For example in mathlib in `algebra/field.lean` we find the line

```lean
@[simp] theorem ne_zero (u : units α) : (u : α) ≠ 0
```

This lemma is then added to `simp`'s armoury. Note several things however.

1) It might not be wise to make a random theorem into a simp lemma. Ideally the result has to be of a certain kind, the most important kinds being those of the form `A=B` and `A↔B`. Note however that if you want to add `fact` to `simp`'s weaponry, you can prove

```lean
@[simp] lemma my_lemma : fact ↔ true
```

(and in fact more recent versions of Lean do this automatically when you try to add random theorems to the simp dataset).

2) If you are not careful you can add a bad simp lemma of the form `foo x y = [something mentioning foo]` and then `simp` will attempt to rewrite `foo` and then end up with another one, and attempt to rewrite that, and so on. This can be fixed by using `rw` instead of `simp`, or using the config option `{single_pass := tt}`.


### When it is unadvisable to use simp

Using `simp` in the middle of proofs is a `simp` anti-pattern, which will produce brittle code. In other words, don't use `simp` in the middle of proofs. Use it to finish proofs. If you really need to simplify a goal in the middle of a proof, then use `simp`, but afterwards cut and paste the goal into your code and write `suffices : (simplified thing), by simpa using this`. This is really important because the behaviour of `simp` changes sometimes, and if you put `simp` in the middle of proofs then your code might randomly stop compiling and it will be hard to figure out why if you didn't write down the exact thing which `simp` used to be reducing your goal to.

### How to use simp better.

Conversely, if you ever manage to close a goal with `simp`, then take a look at the line before you ran `simp`. Could you have run simp one line earlier? How far back did simp start working? Even for goals where you didn't use simp at all -- could you have used `simp` for your last line? What about the last-but one? And so on.

Recall that `simp` lemmas are almost all of the form `X = Y` or `X ↔ Y`. Hence `simp` might work well for such goals. However what about goals of the form `X → Y`? You could try assuming `h : X` and then running either `simpa using h` or `simp {contextual := tt}` to see if Lean can deduce `Y`.

### Simp options.

The behaviour of `simp` can be tweaked by simp variants and also by passing options to the algorithm. A good place to start is to look at the docstring for simp (write simp in VS Code and hover your mouse over it to see the docstring). Here are some examples, some of which are covered by the docstring and some of whichare not.

1) `simp only [H1, H2, H3]` uses only lemmas `H1`, `H2`, and `H3` rather than `simp`s full collection of lemmas. Whyever might one want to do this in practice? Because sometimes simp simplifies things too much -- it might unfold things that you wanted to keep folded, for example. 

2) `simp [-X]` stops `simp` from using lemma `X`. One could imagine using this as another solution when one finds `simp` doing more than you would like. Recall from above that `set_option trace.simplify.rewrite true` shows you exactly which lemmas `simp` is using.

3) `simp * at *`. This simplifies everything in sight. Use if life is getting complicated.

4) `simp {single_pass := tt}` -- this `single_pass` is a config option, one of around 16 at the time of writing. One can use `single_pass` to avoid loops which would otherwise occur; for example `nat.gcd_def` is an equality with `gcd` on both the left and right hand side, so `simp [nat.gcd_def]` is risky behaviour whereas `simp [nat.gcd_def] {single_pass := tt}` is not. As you can imagine, `simp only [h] {single_pass := tt}` here makes simp behave pretty much like `rw h`.

5) Search for `structure simp_config` in the file `init/meta/simp_tactic.lean` in core Lean to see the full list of config options. Others, many undocumented, are:
```
(max_steps : nat           := simp.default_max_steps)
(contextual : bool         := ff)
(lift_eq : bool            := tt)
(canonize_instances : bool := tt)
(canonize_proofs : bool    := ff)
(use_axioms : bool         := tt)
(zeta : bool               := tt)
(beta : bool               := tt)
(eta  : bool               := tt)
(proj : bool               := tt) -- reduce projections
(iota : bool               := tt)
(iota_eqn : bool           := ff) -- reduce using all equation lemmas generated by equation/pattern-matching compiler
(constructor_eq : bool     := tt)
(single_pass : bool        := ff)
(fail_if_unchanged         := tt)
(memoize                   := tt)
```

We see from the changelog that setting `constructor_eq` to true will reduce equations of the form `X a1 a2... = Y b1 b2...` to false if `X` and `Y` are distinct constructors for the same type, and to `a1 = b1 and a2 = b2 and...` if `X = Y` are the same constructor. Another interesting example is `iota_eqn` : `simp!` is shorthand for `simp {iota_eqn := tt}`. This adds non-trivial equation lemmas generated by the equation/pattern-matching compiler to simp's weaponry. See the changelog for more details. 

### Cutting edge simp facts

If you want to find out the most recent tweaks to simp, a very good place to look is [the changelog](https://github.com/leanprover/lean/blob/master/doc/changes.md).

### Something that could be added later on:

"Re: documentation. If you mention congruence, you could show off simp's support for congruence relations. If you show reflexivity and transitivity for cong, and have congruence lemmas for +, etc., then you can rewrite with congruences as if they were equations."
