; Locals queries for JML
; Used for scope tracking and variable references

; ============================================================================
; Scopes
; ============================================================================

; Model method creates a scope
(model_method_decl
  (model_method_body) @local.scope)

; Quantified expressions create scopes
(quantified_expression) @local.scope

; ============================================================================
; Definitions
; ============================================================================

; Parameters
(parameter
  (identifier) @local.definition.parameter)

; Ghost fields
(ghost_field_declaration
  (identifier) @local.definition.field)

; Model fields
(model_field_declaration
  (identifier) @local.definition.field)

; Model method parameters
(model_method_decl
  (parameter_list
    (parameter
      (identifier) @local.definition.parameter)))

; Variables in quantified expressions
(quantified_expression
  (identifier) @local.definition.variable)

; Local variables in model methods
(model_var_decl
  (identifier) @local.definition.variable)

; ============================================================================
; References
; ============================================================================

; Variable references
(expression
  (primary
    (identifier) @local.reference)
)
