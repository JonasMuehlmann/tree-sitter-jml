/**
 * @file A parser for the Java Modeling Language (JML)
 * @author Jonas Mühlmann <49788305+JonasMuehlmann@users.noreply.github.com>
 * @license MIT
 */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

module.exports = grammar({
  name: "jml",

  rules: {
    // TODO: add the actual grammar rules
    source_file: $ => "hello"
  }
});
