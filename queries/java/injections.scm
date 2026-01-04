; Tree-sitter injection query for JML in Java files
; Place this file in: ~/.config/nvim/queries/java/injections.scm

; Inject JML into line comments that start with //@
; Strip the //@ prefix using offset
((line_comment) @injection.content
 ;(#match? @injection.content "^//\\s*@")
 (#set! injection.language "jml")
 ;(#offset! @injection.content 0 3 0 0)
)

; Inject JML into block comments that start with /*@
; Strip the /*@ prefix and */ suffix using offset
((block_comment) @injection.content
 ;(#match? @injection.content "^/\\*\\s*@")
 (#set! injection.language "jml")
 ;(#offset! @injection.content 0 3 0 -2)
)

