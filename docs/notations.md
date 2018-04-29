Categories
---

We use the `⟶` (`\hom`) arrow to denote sets of morphisms, as in `X ⟶ Y`.
This leaves the actual category implicit; it is inferred from the type of X and Y but typeclass inference.

We use `𝟙` (`\b1`) to denote identity morphisms, as in `𝟙 X`.

We use `≫` (`\gg`) to denote composition of morphisms, as in `f ≫ g`, which means "`f` followed by `g`".
This is the opposite order than the usual convention (which is lame).  

Isomorphisms
---
We use `≅` for isomorphisms.

Functors
---
We use `↝` (`\leadsto` or `\lea` or `\r~`) to denote functors, as in `C ↝ D` for the type of functors from `C` to `D`.
Unfortunately Johannes reserved `⇒` (`\functor` or `\func`) in core: https://github.com/leanprover/lean/blob/master/library/init/relator.lean, so we can't use that here.
Perhaps this is unnecessary, and it's better to just write `Functor C D`.

Unfortunately, writing application of functors on objects and morphisms merely by function application is problematic.
To do either, we need to use a coercion to a function type, and we aren't allowed to do both this way.
Even doing one (probably application to objects) causes some serious problems to automation. I'll have one more go at this,
but in the meantime:

We use `+>` to denote the action of a functor on an object, as in `F +> X`.
We use `&>` to denote the action of a functor on a morphism, as in `F &> f`.

Natural transformations
---
We use `⟹` (`\nattrans` or `\==>`) to denote the type of natural transformations, e.g. `F ⟹ G`.
We use `⇔` (`\<=>`) to denote the type of natural isomorphisms.

Unfortunately, while we'd like to write components of natural transformations via function application (e.g. `τ X`),
this requires coercions to function types, which I don't like.

For now we just write out `τ.components X`.

For vertical and horiztonal composition of natural transformations we "cutely" use `⊟` (`\boxminus`) and `◫` (currently untypeable, but we could ask for `\boxbar`).


TODO:
* Do we need notation that allows specifying the category explicitly when talking about sets of morphisms?
* Unfortunately there is a bug in VS Code, so when you enter the 𝟙 character it switches to right-to-left typing, which is a bit confusing.
