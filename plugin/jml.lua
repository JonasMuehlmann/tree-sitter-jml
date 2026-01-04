-- Register the JML parser with nvim-treesitter
local parser_config = require("nvim-treesitter.parsers").get_parser_configs()

parser_config.jml = {
  install_info = {
    url = "https://github.com/JonasMuehlmann/tree-sitter-jml",
    files = {"src/parser.c"},
    branch = "main",
    generate_requires_npm = false,
    requires_generate_from_grammar = false,
  },
  filetype = "jml",
}

-- Register the .jml file extension
vim.filetype.add({
  extension = {
    jml = "jml",
  },
})
