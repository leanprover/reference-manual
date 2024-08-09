import Verso.Genre.Manual

import Manual.Meta
open Manual.FFIDocType

open Verso.Genre Manual

set_option pp.rawOnError true


#doc (Manual) "Syntax" =>
%%%
tag := "string-syntax"
%%%

Lean has two kinds of string literals: ordinary string literals and raw string literals.

# String Literals

String literals begin and end with a double-quote character `"`. {index subterm:="string"}[literal]
Between these characters, they may contain any other character, including newlines, which are included literally (with the caveat that all newlines in a Lean source file are interpreted as `'\n'`, regardless of file encoding and platform).
Special characters that cannot otherwise be written in string literals may be escaped with a backslash, so `"\"Quotes\""` is a string literal that begins and ends with double quotes.
The following forms of escape sequences are accepted:

: `\r`, `\n`, `\t`, `\\`, `\"`, `\'`

  These escape sequences have the usual meaning, mapping to `CR`, `LF`, tab, backslash, double quote, and single quote, respectively.

: `\xNN`

  When `NN` is a sequence of two hexadecimal digits, this escape denotes the character whose Unicode codepoint is indicated by the two-digit hexadecimal code.

: `\uNNNN`

  When `NN` is a sequence of two hexadecimal digits, this escape denotes the character whose Unicode codepoint is indicated by the four-digit hexadecimal code.


String literals may contain {deftech}[_gaps_].
A gap is indicated by an escaped newline, with no intervening characters between the escaping backslash and the newline.
In this case, the string denoted by the literal is missing the newline and all leading whitespace from the next line.
String gaps may not precede lines that contain only whitespace.

Here, `str1` and `str2` are the same string:
```lean
def str1 := "String with \
             a gap"
def str2 := "String with a gap"

example : str1 = str2 := rfl
```

This example is rejected, because the line following the gap is empty:

```syntaxError foo
def str3 := "String with \

             a gap"
```
The parser error is:
```leanOutput foo
<example>:2:0: unexpected additional newline in string gap
```


# Raw String Literals

In {deftech}[raw string literals], {index subterm:="raw string"}[literal] there are no escape sequences or gaps, and each character denotes itself exactly.
Raw string literals are preceded by `r`, followed by zero or more hash characters (`#`) and a double quote `"`.
The string literal is completed at a double quote that is followed by _the same number_ of hash characters.
For example, they can be used to avoid the need to double-escape certain characters:
```lean (name := evalStr)
example : r"\t" = "\\t" := rfl
#eval r"Write backslash in a string using '\\\\'"
```
The `#eval` yields:
```leanOutput evalStr
"Write backslash in a string using '\\\\\\\\'"
```

Including hash marks allows the strings to contain unescaped quotes:

```lean
example : r#"This is "literally" quoted"# = "This is \"literally\" quoted" := rfl
```

Adding sufficiently many hash marks allows any raw literal to be written literally:

```lean
example : r##"This is r#"literally"# quoted"## = "This is r#\"literally\"# quoted" := rfl
```


# Interpolated Strings

Preceding a string literal with `s!` causes it to be processed as an {deftech}[_interpolated string_], in which regions of the string surrounded by `{` and `}` characters are parsed and interpreted as Lean expressions.
Interpolated strings are interpreted by appending the string that precedes the interpolation, the expression (with an added call to {name ToString.toString}`toString` surrounding it), and the string that follows the interpolation.

For example:
```lean
example : s!"1 + 1 = {1 + 1}\n" = "1 + 1 = " ++ toString (1 + 1) ++ "\n" := rfl
```

Preceding a literal with `m!` causes the interpolation to result in an instance of {name Lean.MessageData}`MessageData`, the compiler's internal data structure for messages to be shown to users.
