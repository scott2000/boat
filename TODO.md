# TODO List

- Replace `StateT CompileState IO` with `ReaderT (IORef CompileState) IO`
- Type inference!
- Replace emptyDecls, defaultModule, emptyInferVariable, etc. with Monoid?
- Add warnings for invalid syntax that looks like Haskell, ML, Rust, etc.
  - Accept `val`/`var`/`const` instead of `let` and emit an error
  - Add error for `struct`/`enum`/`class` suggesting `data`
  - Add error for `fn`/`fun`/`func`/`function` suggesting `let` with `fun`
  - Add error for Haskell-style function declarations with `::`/`:`/`=`
- Add support for detailed, multi-span errors
- Maybe lex the file first and then parse the token stream?
