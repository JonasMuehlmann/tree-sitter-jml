# JML Tree-Sitter Queries

This directory contains tree-sitter queries for syntax highlighting, code navigation, and editor integration.

## Query Files

### highlights.scm

Provides syntax highlighting for JML code. Highlights include:

**Keywords**
- Contract clauses: `requires`, `ensures`, `signals`, `assignable`, etc.
- Behavior modifiers: `normal_behavior`, `exceptional_behavior`, etc.
- Loop specifications: `loop_invariant`, `decreases`
- Class-level: `invariant`, `constraint`, `axiom`, `initially`
- Statements: `set`, `assert`, `assume`
- Control flow: `return`, `if`, `else`

**Operators**
- JML-specific: `==>`, `<==`, `<==>`, `<=!=>`, `<:`
- Standard: `+`, `-`, `*`, `/`, `==`, `!=`, `&&`, `||`, etc.

**Types**
- Java primitives: `int`, `boolean`, `char`, etc.
- JML types: `\bigint`, `\seq`, `\locset`, `\real`
- Class types

**JML Keywords**
- `\result`, `\old`, `\fresh`, `\nothing`, `\everything`
- Quantifiers: `\forall`, `\exists`, `\sum`, `\product`, `\max`, `\min`
- And many more...

**Modifiers**
- `pure`, `strictly_pure`, `model`, `helper`, `ghost`
- Visibility: `public`, `private`, `protected`, `package`
- `nullable`, `non_null`

**Entity Names/Labels**
- Labeled clauses and expressions
- Entity names with `:` separator

**Literals**
- Numbers, booleans, strings, characters, null

**Comments**
- Both JML comments (`//@`, `/*@ */`) and Java comments

### locals.scm

Provides scope tracking and variable reference information for:

**Scopes**
- Model method bodies
- Quantified expressions

**Definitions**
- Parameters in model methods
- Ghost and model field declarations
- Variables in quantified expressions
- Local variables in model methods

**References**
- Variable references in expressions

This is used by editors for features like:
- Go to definition
- Find references
- Rename refactoring
- Scope-aware completions

### tags.scm

Provides symbol extraction for code navigation:

**Definitions**
- Model methods
- Ghost fields
- Model fields
- Labeled class invariants

**References**
- Method calls
- Field access

This is used by:
- Symbol search
- Outline/document symbols view
- Breadcrumbs navigation
- Tags/ctags generation

## Usage in Editors

### Neovim (nvim-treesitter)

```lua
require'nvim-treesitter.configs'.setup {
  highlight = {
    enable = true,
    additional_vim_regex_highlighting = false,
  },
  indent = {
    enable = true
  }
}
```

### Emacs (tree-sitter-mode)

```elisp
(use-package tree-sitter
  :config
  (global-tree-sitter-mode)
  (add-hook 'tree-sitter-after-on-hook #'tree-sitter-hl-mode))

(use-package tree-sitter-langs)
```

### VS Code

Use with [vscode-tree-sitter](https://marketplace.visualstudio.com/items?itemName=georgewfraser.vscode-tree-sitter) extension.

### Helix

Helix has built-in tree-sitter support. The queries will be used automatically once the grammar is installed.

## Testing Highlights

To test the highlighting queries:

```bash
# View highlighted output
npx tree-sitter highlight test_examples.jml

# See all capture matches
npx tree-sitter query queries/highlights.scm test_examples.jml
```

## Customization

You can extend or customize these queries for your specific needs:

1. Copy the query file you want to modify
2. Add your custom patterns
3. Use in your editor configuration

Common customizations:
- Additional keyword highlighting
- Custom semantic highlighting
- Project-specific conventions
- Integration with other grammars

## Query Syntax

Tree-sitter queries use a Lisp-like syntax. Examples:

```scheme
; Match a node type
(identifier) @variable

; Match with field names
(parameter
  name: (identifier) @variable.parameter)

; Match with predicates
(identifier) @constant
  (#match? @constant "^[A-Z_]+$")

; Alternative nodes
[
  "public"
  "private"
  "protected"
] @keyword.modifier
```

See the [tree-sitter query documentation](https://tree-sitter.github.io/tree-sitter/using-parsers#pattern-matching-with-queries) for more details.

## Contributing

Improvements to the queries are welcome! When adding new patterns:

1. Test with example JML code
2. Ensure no conflicts with existing patterns
3. Follow the existing organization and naming conventions
4. Document any new capture names used
