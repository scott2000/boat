# TODO List

- Warn for unused (and maybe uninferrable) arguments
- Allow `(+)`, `(-)`, and `_` for unused arguments
- Minimize `MaybeT` short-circuiting in variance inference
- Make version of `reduceApply` that rejects infix and unary operators
- Make `Meta` take a parameter for what metadata to store. This could be used
  to get rid of the type field for things that don't have types and it could
  be used to ensure statically that inferred expressions have types.
- Type inference!
- Add support for detailed, multi-span errors
- Maybe lex the file first and then parse the token stream?
