Boat
====

This is the compiler for the boat programming language
*(it's a work in progress so don't expect too much just yet)*

## An example program

```boat
data Nat =
  Z
  S Nat

let (+) = fun
  Z     y -> x
  (S x) y -> x + S y

let (*) = fun
  Z     _ -> Z
  _     Z -> Z
  (S x) y -> y + x*y

let fac = fun
  Z     -> S Z
  (S x) ->
    S x * fac x
```
