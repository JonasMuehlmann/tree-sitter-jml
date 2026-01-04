import XCTest
import SwiftTreeSitter
import TreeSitterJml

final class TreeSitterJmlTests: XCTestCase {
    func testCanLoadGrammar() throws {
        let parser = Parser()
        let language = Language(language: tree_sitter_jml())
        XCTAssertNoThrow(try parser.setLanguage(language),
                         "Error loading Java Modeling Language grammar")
    }
}
