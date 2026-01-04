; Tags queries for JML
; Used for code navigation and symbol extraction

; ============================================================================
; Definitions
; ============================================================================

; Model methods
(model_method_decl
  (identifier) @name) @definition.method

; Ghost fields
(ghost_field_declaration
  (identifier) @name) @definition.field

; Model fields
(model_field_declaration
  (identifier) @name) @definition.field

; Class invariants with labels
(class_invariant_decl
  (identifier) @name
  ":") @definition.constant

; ============================================================================
; References
; ============================================================================

; Method calls
(method_invocation
  (identifier) @name) @reference.call

; Field access
(field_access
  (identifier) @name) @reference.field
