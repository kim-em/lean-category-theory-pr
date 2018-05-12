Here is my attempt to decipher how levels should work.

Let's say we have a notion `category.{u v}`, with `Obj : Type u` and `Hom : Obj -> Obj -> Type v`. (This is not what I have at the moment: I insist `u = v + 1`.)

The category of types at level w (henceforth TYPES.{w}) must have u = w + 1, v = w.

I certainly want the category of types to have all products. If `f : Type a -> Type b`, then `\Pi x : a, f x` is in `Type (max a b)`. This means that we can take the product of a family `f : Type w -> Type w`. Thus for `C : category.{u v}`, the largest products allowed are over `f : X -> C.Obj`, for some `X : Type u` or else TYPES won't have products!

Next, I want it to be true that categories with equalizers and products have limits, and that this works by the "usual" construction: given some diagram `F : J \to C`, we form `X` and `Y`, both products, and two maps `f g : X -> Y`, all described in a moment, and show that the limit of `F` is given by the equalizer of `f` and `g`. The object `X` is the product of the function `F.onObjects : J.Obj -> C.Obj`. The object `Y` is the product of the function in `(Σ p : J.Obj × J.Obj, p.1 -> p.2) -> C.Obj`, given by the formula `λ t, t.1.2`. Now, if `J : category.{i j}`, we have `J.Obj : Type i` and `(Σ p : J.Obj × J.Obj, p.1 -> p.2) : Type (max i j)`, so these products only exist if `i, j \leq u`.

Putting all this together, we see that a category `C : category.{u v}` being complete means we have limits for functors `F : J -> C` for any `J : category.{i j}` with `i, j \leq u`.

Taking my specialisation `Category.{w} = category.{w+1,w}`, we can rephrase this as `C : Category.{w}` should have limits for all `J : Category.{k}` with k+1,k \leq w+1, i.e. everything up to `k=w`.

This agrees with what Reid says, not what I've done, so I better fix things!