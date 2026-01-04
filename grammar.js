/**
 * @file A parser for the Java Modeling Language (JML)
 * @author Jonas Mühlmann <49788305+JonasMuehlmann@users.noreply.github.com>
 * @license MIT
 */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

module.exports = grammar({
  name: "jml",

  extras: $ => [
    /\s/,
    $.java_line_comment,
    $.java_block_comment,
  ],

  conflicts: $ => [
    [$.expression, $.primary],
    [$.type_type, $.expression],
    [$.modifier, $.model_method_decl],
    [$.modifier, $.ghost_field_declaration],
    [$.modifier, $.model_field_declaration],
    [$.modifier, $.visibility],
    [$.modifier, $.class_invariant_decl],
    [$.modifier, $.ghost_field_declaration, $.model_field_declaration],
    [$.modifier, $.ghost_field_declaration, $.model_field_declaration, $.model_method_decl],
    [$.ghost_field_declaration, $.model_method_decl],
    [$.model_field_declaration, $.model_method_decl],
    [$.ghost_field_declaration, $.model_field_declaration],
    [$.contract_clause, $.loop_invariant_decl],
    [$.method_contract_decl, $.block_contract_decl],
    [$.primary, $.class_type],
    [$.nested_contract],
  ],

  word: $ => $.identifier,

  rules: {
    // Entry point for standalone .jml files
    source_file: $ => repeat($._top_level_item),

    // Entry point for injection into Java comments (without comment delimiters)
    _injection_content: $ => repeat($._jml_declaration),

    _top_level_item: $ => choice(
      $.jml_line_comment,
      $.jml_block_comment,
    ),

    // JML Comments - line comment
    jml_line_comment: $ => seq(
      '//@',
      repeat($._jml_declaration),
    ),

    // JML Comments - block comment  
    jml_block_comment: $ => seq(
      '/*@',
      repeat(choice(
        seq(optional('@'), $._jml_declaration),
        '@',
      )),
      '*/',
    ),

    _jml_declaration: $ => choice(
      $.method_contract_decl,
      $.class_invariant_decl,
      $.ghost_field_declaration,
      $.model_field_declaration,
      $.model_method_decl,
      $.loop_invariant_decl,
      $.block_contract_decl,
      $.set_statement,
      $.assert_statement,
      $.assume_statement,
      $.modifier_decl,
    ),

    // Modifier declarations
    modifier_decl: $ => prec.left(repeat1($.modifier)),

    modifier: $ => choice(
      'pure',
      'strictly_pure',
      'model',
      'helper',
      'nullable_by_default',
      'public',
      'private',
      'protected',
      'package',
      'non_null',
      'nullable',
      'static',
      'instance',
      'ghost',
    ),

    // Method Contracts
    method_contract_decl: $ => prec.left(seq(
      optional('also'),
      optional($.visibility),
      optional($.behavior_keyword),
      repeat1($.contract_clause),
    )),

    visibility: $ => choice('package', 'private', 'protected', 'public'),

    behavior_keyword: $ => choice(
      'behavior',
      'behaviour',
      'normal_behavior',
      'normal_behaviour',
      'exceptional_behavior',
      'exceptional_behaviour',
      'break_behavior',
      'continue_behavior',
      'return_behavior',
    ),

    contract_clause: $ => choice(
      $.requires_clause,
      $.ensures_clause,
      $.signals_clause,
      $.signals_only_clause,
      $.diverges_clause,
      $.determines_clause,
      $.assignable_clause,
      $.accessible_clause,
      $.measured_by_clause,
      $.breaks_clause,
      $.continues_clause,
      $.returns_clause,
      $.nested_contract,
    ),

    nested_contract: $ => prec.left(seq(
      '{|',
      repeat(choice(
        $.contract_clause,
        seq('also', repeat($.contract_clause)),
      )),
      '|}',
    )),

    requires_clause: $ => seq(
      optional(seq($.identifier, ':')),
      'requires',
      repeat($.heap_spec),
      $.expression,
      ';',
    ),

    ensures_clause: $ => seq(
      optional(seq($.identifier, ':')),
      'ensures',
      repeat($.heap_spec),
      $.expression,
      ';',
    ),

    signals_clause: $ => seq(
      optional(seq($.identifier, ':')),
      'signals',
      '(',
      $.type_type,
      optional($.identifier),
      ')',
      $.expression,
      ';',
    ),

    signals_only_clause: $ => seq(
      'signals_only',
      $.type_type,
      repeat(seq(',', $.type_type)),
      ';',
    ),

    diverges_clause: $ => seq(
      'diverges',
      $.expression,
      ';',
    ),

    determines_clause: $ => seq(
      'determines',
      $.expression_list,
      'by',
      $.expression_list,
      optional(choice(
        seq('declassifies', $.expression_list),
        seq('erases', $.expression_list),
      )),
      optional(seq('new_objects', $.expression_list)),
      ';',
    ),

    assignable_clause: $ => seq(
      choice('assignable', 'modifiable', 'modifies'),
      repeat($.heap_spec),
      $.expression,
      repeat(seq(',', $.expression)),
      ';',
    ),

    accessible_clause: $ => seq(
      'accessible',
      repeat($.heap_spec),
      $.expression,
      repeat(seq(',', $.expression)),
      optional($.measured_by_inline),
      ';',
    ),

    measured_by_clause: $ => seq(
      'measured_by',
      $.expression_list,
      ';',
    ),

    measured_by_inline: $ => seq(
      'measured_by',
      $.expression_list,
    ),

    breaks_clause: $ => seq(
      'breaks',
      '(',
      optional($.identifier),
      ')',
      $.expression,
      ';',
    ),

    continues_clause: $ => seq(
      'continues',
      '(',
      optional($.identifier),
      ')',
      $.expression,
      ';',
    ),

    returns_clause: $ => seq(
      'returns',
      $.expression,
      ';',
    ),

    heap_spec: $ => seq('<', $.identifier, '>'),

    // Class Elements
    class_invariant_decl: $ => seq(
      optional(choice('static', 'instance')),
      choice('invariant', 'constraint', 'initially', 'axiom'),
      optional(seq($.identifier, ':')),
      $.expression,
      ';',
    ),

    ghost_field_declaration: $ => prec(1, seq(
      repeat(choice('instance', 'static')),
      'ghost',
      repeat(choice('instance', 'static')),
      $.type_type,
      $.identifier,
      repeat(seq(',', $.identifier)),
      optional(seq('=', $.expression)),
      ';',
    )),

    model_field_declaration: $ => prec(1, seq(
      repeat(choice('instance', 'static')),
      'model',
      repeat(choice('instance', 'static')),
      $.type_type,
      $.identifier,
      repeat(seq(',', $.identifier)),
      optional(seq('=', $.expression)),
      ';',
    )),

    // Model Methods
    model_method_decl: $ => prec(1, seq(
      optional(seq(
        optional($.visibility),
        'model_behavior',
        repeat($.contract_clause),
      )),
      repeat(choice(
        $.visibility,
        'no_state',
        'two_state',
        'helper',
        'static',
      )),
      'model',
      repeat(choice(
        $.visibility,
        'no_state',
        'two_state',
        'helper',
        'static',
      )),
      $.type_type,
      $.identifier,
      '(',
      optional($.parameter_list),
      ')',
      choice(
        seq('{', $.model_method_body, '}'),
        ';',
      ),
    )),

    model_method_body: $ => seq(
      repeat($.model_var_decl),
      $.model_statement,
    ),

    model_var_decl: $ => seq(
      'var',
      $.identifier,
      '=',
      $.expression,
      ';',
    ),

    model_statement: $ => choice(
      seq('return', $.expression, ';'),
      seq(
        'if',
        '(',
        $.expression,
        ')',
        choice($.model_statement, seq('{', $.model_statement, '}')),
        'else',
        choice($.model_statement, seq('{', $.model_statement, '}')),
      ),
    ),

    parameter_list: $ => seq(
      $.parameter,
      repeat(seq(',', $.parameter)),
    ),

    parameter: $ => seq(
      $.type_type,
      $.identifier,
    ),

    // Loop Invariants
    loop_invariant_decl: $ => prec.left(repeat1(choice(
      $.loop_invariant_clause,
      $.variant_clause,
      $.assignable_clause,
      $.determines_clause,
    ))),

    loop_invariant_clause: $ => seq(
      optional(seq($.identifier, ':')),
      'loop_invariant',
      repeat($.heap_spec),
      $.expression,
      ';',
    ),

    variant_clause: $ => seq(
      optional(seq($.identifier, ':')),
      'decreases',
      $.expression_list,
      ';',
    ),

    // Block Contracts
    block_contract_decl: $ => seq(
      optional('also'),
      optional($.visibility),
      optional($.behavior_keyword),
      repeat1($.contract_clause),
    ),

    // JML Statements
    set_statement: $ => seq(
      optional(seq($.identifier, ':')),
      'set',
      $.expression,
      '=',
      $.expression,
      ';',
    ),

    assert_statement: $ => seq(
      optional(seq($.identifier, ':')),
      'assert',
      $.expression,
      ';',
    ),

    assume_statement: $ => seq(
      optional(seq($.identifier, ':')),
      'assume',
      $.expression,
      ';',
    ),

    // Expressions
    expression: $ => choice(
      $.primary,
      $.quantified_expression,
      $.labeled_expression,
      $.parenthesized_expression,
      $.array_access,
      $.array_range_expression,
      $.cast_expression,
      $.unary_expression,
      $.binary_expression,
      $.ternary_expression,
      $.field_access,
      $.method_invocation,
      $.new_expression,
    ),

    primary: $ => choice(
      $.literal,
      $.identifier,
      'this',
      'super',
      $.type_class_expression,
      $.jml_keyword,
    ),

    jml_keyword: $ => choice(
      '\\result',
      '\\nothing',
      '\\everything',
      '\\not_specified',
      '\\not_assigned',
      '\\old',
      '\\pre',
      '\\fresh',
      '\\reach',
      '\\duration',
      '\\space',
      '\\working_space',
      '\\nonnullelements',
      '\\typeof',
      '\\elemtype',
      '\\type',
      '\\lockset',
      '\\max',
      '\\infinite_union',
      '\\num_of',
      '\\product',
      '\\sum',
      '\\min',
      '\\is_initialized',
      '\\invariant_for',
      '\\lblneg',
      '\\lblpos',
      '\\lbl',
    ),

    type_class_expression: $ => seq(
      choice($.type_type, 'void'),
      '.',
      'class',
    ),

    quantified_expression: $ => seq(
      '(',
      field('quantifier', choice(
        '\\forall',
        '\\exists',
        '\\sum',
        '\\product',
        '\\max',
        '\\min',
        '\\num_of',
        $.identifier,
      )),
      $.type_type,
      $.identifier,
      repeat(seq(',', $.identifier)),
      ';',
      repeat(seq($.expression, ';')),
      $.expression,
      ')',
    ),

    labeled_expression: $ => seq(
      '(',
      choice('\\lblpos', '\\lblneg', '\\lbl'),
      $.identifier,
      optional(','),
      $.expression,
      ')',
    ),

    parenthesized_expression: $ => seq('(', $.expression, ')'),

    array_access: $ => prec(17, seq(
      $.expression,
      '[',
      choice($.expression, '*'),
      ']',
    )),

    array_range_expression: $ => prec(17, seq(
      $.expression,
      '[',
      $.expression,
      '..',
      $.expression,
      ']',
    )),

    cast_expression: $ => prec(15, seq(
      '(',
      $.type_type,
      ')',
      $.expression,
    )),

    unary_expression: $ => choice(
      prec(14, seq('-', $.expression)),
      prec(14, seq('!', $.expression)),
      prec(14, seq('~', $.expression)),
      prec(14, seq('+', $.expression)),
    ),

    binary_expression: $ => choice(
      prec.left(13, seq($.expression, '*', $.expression)),
      prec.right(12, seq($.expression, '%', $.expression)),
      prec.right(12, seq($.expression, '/', $.expression)),
      prec.left(11, seq($.expression, '+', $.expression)),
      prec.left(11, seq($.expression, '-', $.expression)),
      prec.left(10, seq($.expression, '<<', $.expression)),
      prec.left(10, seq($.expression, '>>', $.expression)),
      prec.left(10, seq($.expression, '>>>', $.expression)),
      prec.left(9, seq($.expression, '<=', $.expression)),
      prec.left(9, seq($.expression, '>=', $.expression)),
      prec.left(9, seq($.expression, '>', $.expression)),
      prec.left(9, seq($.expression, '<', $.expression)),
      prec.left(9, seq($.expression, 'instanceof', $.expression)),
      prec.left(9, seq($.expression, '<:', $.expression)),
      prec.left(8, seq($.expression, '==', $.expression)),
      prec.left(8, seq($.expression, '!=', $.expression)),
      prec.left(7, seq($.expression, '&', $.expression)),
      prec.left(6, seq($.expression, '^', $.expression)),
      prec.left(5, seq($.expression, '|', $.expression)),
      prec.left(4, seq($.expression, '&&', $.expression)),
      prec.left(3, seq($.expression, '||', $.expression)),
      prec.right(2, seq($.expression, '==>', $.expression)),
      prec.left(2, seq($.expression, '<==', $.expression)),
      prec.left(1, seq($.expression, '<==>', $.expression)),
      prec.left(1, seq($.expression, '<=!=>', $.expression)),
    ),

    ternary_expression: $ => prec.right(0, seq(
      $.expression,
      '?',
      $.expression,
      ':',
      $.expression,
    )),

    field_access: $ => prec(16, seq(
      $.expression,
      '.',
      choice($.identifier, '*'),
    )),

    method_invocation: $ => prec(16, seq(
      choice($.expression, $.identifier),
      '(',
      optional($.expression_list),
      ')',
    )),

    new_expression: $ => prec.right(seq(
      'new',
      repeat(seq($.identifier, '.')),
      $.identifier,
      optional(seq('(', optional($.expression_list), ')')),
    )),

    expression_list: $ => seq(
      $.expression,
      repeat(seq(',', $.expression)),
    ),

    // Types
    type_type: $ => seq(
      optional(choice('nullable', 'non_null')),
      $._base_type,
      repeat('[]'),
    ),

    _base_type: $ => choice(
      $.primitive_type,
      $.class_type,
      $.jml_builtin_type,
    ),

    primitive_type: $ => choice(
      'boolean',
      'byte',
      'char',
      'short',
      'int',
      'long',
      'float',
      'double',
    ),

    class_type: $ => prec.left(seq(
      $.identifier,
      repeat(seq('.', $.identifier)),
    )),

    jml_builtin_type: $ => choice(
      '\\bigint',
      '\\seq',
      '\\locset',
      '\\real',
    ),

    // Literals
    literal: $ => choice(
      $.integer_literal,
      $.floating_point_literal,
      $.boolean_literal,
      $.character_literal,
      $.string_literal,
      $.null_literal,
    ),

    integer_literal: $ => token(choice(
      /[0-9]+[lL]?/,
      /0[xX][0-9a-fA-F]+[lL]?/,
      /0[bB][01]+[lL]?/,
      /0[0-7]+[lL]?/,
    )),

    floating_point_literal: $ => token(choice(
      /[0-9]+\.[0-9]*([eE][+-]?[0-9]+)?[fFdD]?/,
      /\.[0-9]+([eE][+-]?[0-9]+)?[fFdD]?/,
      /[0-9]+[eE][+-]?[0-9]+[fFdD]?/,
      /[0-9]+[fFdD]/,
    )),

    boolean_literal: $ => choice('true', 'false'),

    character_literal: $ => token(seq(
      "'",
      choice(
        /[^'\\]/,
        /\\./,
      ),
      "'",
    )),

    string_literal: $ => token(seq(
      '"',
      repeat(choice(
        /[^"\\]/,
        /\\./,
      )),
      '"',
    )),

    null_literal: $ => 'null',

    // Identifiers
    identifier: $ => /[a-zA-Z_$][a-zA-Z0-9_$]*/,

    // Java Comments (not JML)
    java_line_comment: $ => token(seq('//', /[^@].*/, optional('\n'))),
    java_block_comment: $ => token(seq('/*', /[^@]/, /[^*]*\*+([^/*][^*]*\*+)*/, '/')),
  }
});
