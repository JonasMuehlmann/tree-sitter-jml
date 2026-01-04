# tree-sitter-jml

A Tree-Sitter grammar for the Java Modeling Language (JML), based on the JML* dialect supported by the KeY theorem prover.

## Overview

This grammar implements parsing for JML specifications as defined in the [KeY JML Grammar documentation](https://keyproject.github.io/key-docs/user/JMLGrammar/). JML is a behavioral interface specification language for Java that uses special comments to add formal specifications to Java code.

## Features

The grammar supports the following JML constructs:

### Method Contracts
- `requires` - preconditions
- `ensures` - postconditions  
- `signals` - exceptional postconditions
- `signals_only` - exceptions that may be thrown
- `diverges` - non-termination conditions
- `assignable` / `modifiable` / `modifies` - frame conditions
- `measured_by` - termination measures
- `determines` - information flow specifications

### Class-Level Specifications
- `invariant` - class invariants (static/instance)
- `constraint` - history constraints
- `initially` - initial state specifications
- `axiom` - axioms
- Ghost fields (`ghost`) and model fields (`model`)
- Model methods with restricted syntax

### Loop Specifications
- `loop_invariant` - loop invariants
- `decreases` - variant functions for termination

### Block Contracts
- Block-level specifications with `behavior`, `breaks`, `continues`, `returns`

### JML Statements
- `set` - ghost variable assignments
- `assert` - assertions
- `assume` - assumptions

### Expressions
- Quantified expressions: `\forall`, `\exists`, `\sum`, `\product`, `\max`, `\min`, `\num_of`
- JML keywords: `\result`, `\nothing`, `\everything`, `\old`, `\fresh`, etc.
- Java expressions with JML extensions
- Labeled expressions: `\lblpos`, `\lblneg`, `\lbl`

### JML Types
- Standard Java types
- JML-specific types: `\bigint`, `\seq`, `\locset`, `\real`
- Type modifiers: `nullable`, `non_null`

### Modifiers
- `pure`, `strictly_pure` - side-effect freedom
- `helper` - helper methods
- `model` - model elements
- Visibility modifiers: `public`, `private`, `protected`, `package`

## Comment Syntax

JML specifications are written in special comments:

```java
//@ single-line JML comment

/*@ 
  @ multi-line 
  @ JML comment
  */
```

## Installation

### Building from Source

```bash
npm install
npx tree-sitter generate
```

### Neovim Integration

#### Via Package Manager (Recommended)

Using [lazy.nvim](https://github.com/folke/lazy.nvim):

```lua
{
  "JMuhlmann/tree-sitter-jml",
  dependencies = { "nvim-treesitter/nvim-treesitter" },
  build = ":TSUpdate jml",
}
```

Using [packer.nvim](https://github.com/wbthomason/packer.nvim):

```lua
use {
  'JMuhlmann/tree-sitter-jml',
  requires = { 'nvim-treesitter/nvim-treesitter' },
  run = ':TSUpdate jml',
}
```

Using [vim-plug](https://github.com/junegunn/vim-plug):

```vim
Plug 'nvim-treesitter/nvim-treesitter'
Plug 'JMuhlmann/tree-sitter-jml'
```

After installation, run `:TSInstall jml` in Neovim.

#### Manual Setup

Add to your Neovim config (`~/.config/nvim/init.lua`):

```lua
local parser_config = require("nvim-treesitter.parsers").get_parser_configs()
parser_config.jml = {
  install_info = {
    url = "/path/to/tree-sitter-jml", -- Update this path
    files = {"src/parser.c"},
    generate_requires_npm = false,
    requires_generate_from_grammar = false,
  },
  filetype = "jml",
}

vim.filetype.add({ extension = { jml = "jml" } })
```

Then run `:TSInstall jml` in Neovim.

#### JML in Java Files

To get JML syntax highlighting inside Java files, add injection queries to your tree-sitter Java configuration. The grammar includes injection queries in `queries/java/injections.scm` that enable parsing of JML comments (`//@` and `/*@ */`) within Java source files.

## Usage

### Parsing JML Files

```bash
npx tree-sitter parse <file.jml>
```

### Example

```java
//@ public instance invariant x >= 0;

/*@
  @ requires x > 0;
  @ ensures \result == x * 2;
  @ assignable \nothing;
  */

//@ model int calculateSum(int a, int b) { return a + b; }

/*@
  @ loop_invariant i >= 0 && i <= n;
  @ decreases n - i;
  */

//@ ghost int counter = 0;
//@ set counter = counter + 1;
//@ assert counter > 0;
```

## Grammar Reference

The grammar is based on the JML* dialect as specified in the [KeY project documentation](https://keyproject.github.io/key-docs/user/JMLGrammar/), which extends and restricts the original [JML Reference Manual](http://www.eecs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman.html).

## Syntax Highlighting

The grammar includes comprehensive syntax highlighting queries in `queries/highlights.scm`. These queries provide semantic highlighting for:

- JML keywords and operators
- Contract clauses and behaviors
- Quantified expressions
- Type annotations
- Entity names and labels
- Literals and comments

The queries work with tree-sitter-aware editors like Neovim (nvim-treesitter), Emacs (tree-sitter-mode), Helix, and VS Code with tree-sitter extensions.

To test highlighting:

```bash
npx tree-sitter highlight examples/comprehensive.jml
```

## Development

To work on the grammar:

1. Edit `grammar.js`
2. Run `npx tree-sitter generate` to regenerate the parser
3. Run `npx tree-sitter test` to run tests
4. Use `npx tree-sitter parse <file>` to test parsing
5. Use `npx tree-sitter highlight <file>` to test syntax highlighting

## License

MIT

## Author

Jonas Mühlmann

