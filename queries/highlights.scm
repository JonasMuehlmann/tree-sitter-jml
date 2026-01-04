; Highlights for JML (Java Modeling Language)

; ============================================================================
; Comments
; ============================================================================

(jml_line_comment) @comment
(jml_block_comment) @comment
(java_line_comment) @comment
(java_block_comment) @comment

; ============================================================================
; Keywords - JML Specific
; ============================================================================

; JML Keywords (backslash-prefixed)
(jml_keyword) @keyword.directive

; Quantifiers
(quantified_expression
  quantifier: [
    "\\forall"
    "\\exists"
    "\\sum"
    "\\product"
    "\\max"
    "\\min"
    "\\num_of"
  ] @keyword.operator)

; ============================================================================
; Contract Keywords
; ============================================================================

[
  "requires"
  "ensures"
  "signals"
  "signals_only"
  "diverges"
  "assignable"
  "modifiable"
  "modifies"
  "accessible"
  "measured_by"
  "determines"
  "declassifies"
  "erases"
  "new_objects"
] @keyword

; Behavior keywords
[
  "behavior"
  "behaviour"
  "normal_behavior"
  "normal_behaviour"
  "exceptional_behavior"
  "exceptional_behaviour"
  "break_behavior"
  "continue_behavior"
  "return_behavior"
] @keyword

; Loop keywords
[
  "loop_invariant"
  "decreases"
] @keyword

; Class-level keywords
[
  "invariant"
  "constraint"
  "initially"
  "axiom"
] @keyword

; Statement keywords
[
  "set"
  "assert"
  "assume"
] @keyword

; Control flow in model methods
[
  "return"
  "if"
  "else"
  "var"
] @keyword.control

; ============================================================================
; Modifiers
; ============================================================================

[
  "pure"
  "strictly_pure"
  "helper"
  "model"
  "ghost"
  "nullable_by_default"
  "non_null"
  "nullable"
] @keyword.modifier

[
  "public"
  "private"
  "protected"
  "package"
] @keyword.modifier

[
  "static"
  "instance"
] @keyword.modifier

; ============================================================================
; Special Keywords
; ============================================================================

[
  "also"
  "by"
] @keyword

[
  "this"
  "super"
] @variable.builtin

[
  "new"
] @keyword.operator

; ============================================================================
; Operators
; ============================================================================

; JML-specific operators
[
  "==>"   ; implies
  "<=="   ; implied by
  "<==>"  ; equivalence
  "<=!=>" ; antivalence/xor
  "<:"    ; subtype
] @operator

; Standard operators
[
  "+"
  "-"
  "*"
  "/"
  "%"
  "="
  "=="
  "!="
  "<"
  ">"
  "<="
  ">="
  "&&"
  "||"
  "!"
  "&"
  "|"
  "^"
  "~"
  "<<"
  ">>"
  ">>>"
  "?"
  ":"
  "instanceof"
] @operator

; ============================================================================
; Punctuation
; ============================================================================

[
  ";"
  ","
  "."
] @punctuation.delimiter

[
  "("
  ")"
  "["
  "]"
  "{"
  "}"
  "{|"
  "|}"
] @punctuation.bracket

; Special brackets
(heap_spec
  "<" @punctuation.bracket
  ">" @punctuation.bracket)

; ============================================================================
; Literals
; ============================================================================

(integer_literal) @number
(floating_point_literal) @number
(boolean_literal) @boolean
(null_literal) @constant.builtin
(character_literal) @character
(string_literal) @string

; ============================================================================
; Types
; ============================================================================

(primitive_type) @type.builtin

(class_type
  (identifier) @type)

(jml_builtin_type) @type.builtin

(type_class_expression
  "class" @keyword)

; ============================================================================
; Identifiers
; ============================================================================

; Entity names (labels)
(requires_clause
  (identifier) @label
  ":")

(ensures_clause
  (identifier) @label
  ":")

(signals_clause
  (identifier) @label
  ":")

(loop_invariant_clause
  (identifier) @label
  ":")

(variant_clause
  (identifier) @label
  ":")

(class_invariant_decl
  (identifier) @label
  ":")

(set_statement
  (identifier) @label
  ":")

(assert_statement
  (identifier) @label
  ":")

(assume_statement
  (identifier) @label
  ":")

; Labeled expressions
(labeled_expression
  [
    "\\lblpos"
    "\\lblneg"
    "\\lbl"
  ] @keyword.directive
  (identifier) @label)

; Method names
(model_method_decl
  (identifier) @function)

(method_invocation
  (identifier) @function.call)

; Field declarations
(ghost_field_declaration
  (identifier) @variable)

(model_field_declaration
  (identifier) @variable)

; Parameters
(parameter
  (identifier) @variable.parameter)

; General identifiers
(identifier) @variable

; ============================================================================
; Special Patterns
; ============================================================================

; Array wildcard
(array_access
  "*" @operator)

; Array ranges
(array_range_expression
  ".." @operator)

; Comment markers
"@" @punctuation.special

; ============================================================================
; Errors
; ============================================================================

(ERROR) @error
