# TODO List

- Add flag for `--explain-errors`
- Add warnings for invalid syntax that looks like Haskell, ML, Rust, etc.
  - Accept `val`/`var`/`const` instead of `let` and emit an error
  - Add error for `struct`/`enum`/`class` suggesting `data`
  - Add error for `fn`/`fun`/`func`/`function` suggesting `let` with `fun`
  - Add error for Haskell-style function declarations with `::`/`:`/`=`
- Type inference!
- Add support for detailed, multi-span errors
- Maybe lex the file first and then parse the token stream?
