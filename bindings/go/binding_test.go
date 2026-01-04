package tree_sitter_jml_test

import (
	"testing"

	tree_sitter "github.com/tree-sitter/go-tree-sitter"
	tree_sitter_jml "github.com/jonasmuehlmann/tree-sitter-jml/bindings/go"
)

func TestCanLoadGrammar(t *testing.T) {
	language := tree_sitter.NewLanguage(tree_sitter_jml.Language())
	if language == nil {
		t.Errorf("Error loading Java Modeling Language grammar")
	}
}
