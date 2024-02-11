Boat
====

See [the old repo](https://github.com/scott2000/boat-old) for compilation to
LLVM IR. I never finished this new implementation due to issues with
bidirectional type inference of effect variables with subtyping. I may resume
this project in the future, but it is currently not in active development.

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
  operator <left> (*) : Mul

  let (+) = fun
    Z     y -> y
    (S x) y -> x + S y

  let (*) = fun
    Z     _ -> Z
    (S x) y -> y + x * y
```
