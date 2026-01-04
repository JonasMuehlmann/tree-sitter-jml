vim.api.nvim_create_autocmd("User", {
	pattern = "TSUpdate",
	callback = function()
		require("nvim-treesitter.parsers").jml = {
			install_info = {
				url = "https://github.com/JonasMuehlmann/tree-sitter-jml",
			},
		}
	end,
})
