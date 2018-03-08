# Creating structures #

Creating structures is full of gotchas.

Let's say we want to create a `partial_order`. We know we'll need some function `le` for less than or equal to, and then there will be some axioms. Running

```
#print partial_order
```

seems to indicate that to make a partial order we will need to make all the following fields:

```
partial_order.le
 partial_order.lt
 partial_order.le_refl
 partial_order.le_trans
 partial_order.lt_iff_le_not_le
 partial_order.le_antisymm
 ```

But when we type

```
variable α : Type
instance alpha_is_a_partial_order :  partial_order α := 
{
}
```

and click on the `{` we see that we are only missing four fields: `le`, `le_refl`, `le_trans` and `le_antisymm`. What happened?

The reasons that we do not need to supply the fields `lt` and `lt_iff_not_le` are actually different. The reason we do not need to supply `lt` is hidden in the source code. If you click on `partial_order` and then use `M-.` (in emacs) or F12 (or right click and then select Go To Definition) we see that `partial_order` extends `preorder` and in the definition of `preorder` we see that `lt` is followed not by a `:` but by a `:=`, which somehow means that it gets defined for you.

The reason we do not need to define `lt_iff_le_not_le` is different -- the definition of this field in `preorder` has a mysterious `. order_laws_tac` in it, and I think this means "if you don't define me, I will define myself using that tactic". This construction is [mentioned in the reference manual](https://leanprover.github.io/reference/expressions.html#implicit-arguments).

### That .. notation

Here's how it works.

```lean
variable G : Type
variable HG : group G

example : comm_group G :=
{ 
  mul_comm := sorry, -- apparently you can use things from HG in this
                     -- proof even though HG is at the end.
  ..HG -- this has to be at the end.
}
```

### Creating "big" structures

I had a very unwieldy object which took many lines to even display. I wanted to prove that it was a ring, right in the middle of something else, so I just launched in. But according to the CS guys this is a bad idea. They explained how to make things smaller and smaller, and ultimately I ended up with this:

```lean
definition thing_i_want_to_be_a_ring := [unwieldy thing]

definition thing_has_add : has_add (thing_i_want_to_be_a_ring) :=
⟨construction of addition here⟩
```
and so on and so on. When I finally want to give the ring structure I have


```lean
instance thing_is_ring : comm_ring (thing_i_want_to_be_a_ring) :=
{ add := thing_has_add.has_add,
...
```

### Too many axioms

I wanted to prove that something was a commutative ring and noticed
that I was being asked to prove too many things -- for example I was
asked for a proof of `add_comm` and also `zero_add`, which is fine,
but then I was also asked for a proof of `add_zero`, which is daft.
Mario suggested creating a new constructor `comm_ring.mk'` which only
asks for the things we need, and deduces the rest.
