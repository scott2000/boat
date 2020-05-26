" Vim syntax file
" Language: Boat
" Maintainer: Scott Taylor
" Latest Revision: 26 May 2020

if exists("b:current_syntax")
  finish
endif

syn iskeyword a-z,A-Z,48-57,_

syn keyword boatUse         _ use
syn keyword boatKeywords    mod operator type effect data let with fun match if then else
syn keyword boatWrongKey    unary
syn match   boatNum         '\<[0-9]\+(_[0-9]\+)*\>'
syn match   boatType        '\<\([A-Z][A-Za-z0-9_]*\|_\+[A-Z][A-Za-z0-9_]*\)\>' contains=@NoSpell
syn match   boatOperators   '\([-+*/%^!=<>:?|&~$]\|[-+*/%^!=<>:?|&~$.]\{2,}\)'
syn match   boatSection     '(\(unary \+\)\=\([-+*/%^!=<>:?|&~$]\|[-+*/%^!=<>:?|&~$.]\{2,}\))'
syn match   boatWrongEscape contained '\\[^0ntr'"]'
syn match   boatEscape      contained '\\[0ntr'"]'
syn region  boatCharLit     start="'" end="'" contains=boatEscape,boatWrongEscape
syn region  boatStrLit      start='"' end='"' contains=boatEscape,boatWrongEscape
syn keyword boatTodo        contained TODO FIXME XXX NOTE
syn match   boatLineCmnt    "--.*$" contains=boatTodo,@Spell
syn region  boatBlockCmnt   start='{-' end='-}' contains=boatBlockCmnt,boatTodo,@Spell
syn match   boatLabel       '<\<[A-Za-z_][A-Za-z0-9_]*\>>'

let b:current_syntax = "boat"

hi def link boatUse         Include
hi def link boatKeywords    Keyword
hi def link boatWrongKey    Error
hi def link boatType        Type
hi def link boatOperators   Operator
hi def link boatSection     Function
hi def link boatNum         Number
hi def link boatWrongEscape Error
hi def link boatEscape      SpecialChar
hi def link boatCharLit     Character
hi def link boatStrLit      String
hi def link boatTodo        Todo
hi def link boatLineCmnt    Comment
hi def link boatBlockCmnt   Comment
hi def link boatLabel       Special
