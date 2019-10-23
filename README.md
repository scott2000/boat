Boat
====

This is the compiler for the boat programming language
*(it's a work in progress so don't expect too much just yet)*

## An example program

```boat
use Nat (S, Z, (*))

let fac = fun
  Z     -> S Z
  (S n) ->
    S n * fac n

data mod Nat =
  Z
  S Nat

mod Nat =
  operator type Add < Mul

  operator <left> (+) : Add
  operator <left> (*) : Add

  let (+) = fun
    Z     y -> y
    (S x) y -> x + S y

  let (*) = fun
    Z     _ -> Z
    (S x) y -> y + x * y
```
