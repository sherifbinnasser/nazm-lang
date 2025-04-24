pub mod error;
mod lexing_methods;
mod token;

use documented::DocumentedVariants;
use error::{LexerError, LexerErrorKind};
use itertools::Itertools;
use nazmc_data_pool::{IdPoolBuilder, StrPoolBuilder};
use nazmc_diagnostics::span::{Span, SpanCursor};
use std::str::Chars;
use strum::IntoEnumIterator;
pub use token::*;

pub struct LexerIter<'a> {
    content: &'a str,
    cursor: CharsCursor<'a>,
    /// The byte index the cursor stopped at
    stopped_at_bidx: usize,
    /// The file lines to fill from lexing
    file_lines: Vec<String>,
    /// The start byte index of current line
    current_line_start_bidx: usize,
    /// Errors
    errs: Vec<LexerError>,
    current_token_idx: usize,
    id_pool: &'a mut IdPoolBuilder,
    str_pool: &'a mut StrPoolBuilder,
}

impl<'a> Iterator for LexerIter<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        let start = self.cursor.stopped_at.0;
        let start_byte = self.stopped_at_bidx;
        let kind = self.next_token_type();
        if let TokenKind::Eof = kind {
            return None;
        }
        let end = self.cursor.stopped_at.0;
        let end_byte = self.stopped_at_bidx;
        // let val = &self.content[start_byte..end_byte];
        let span = Span { start, end };
        self.current_token_idx += 1;
        Some(Token {
            span,
            kind,
            start_byte,
            end_byte,
        })
    }
}

impl<'a> LexerIter<'a> {
    pub fn new(
        content: &'a str,
        id_pool: &'a mut IdPoolBuilder,
        str_pool: &'a mut StrPoolBuilder,
    ) -> Self {
        let mut _self = Self {
            content,
            cursor: CharsCursor::new(content),
            stopped_at_bidx: 0,
            file_lines: vec![],
            current_line_start_bidx: 0,
            errs: vec![],
            current_token_idx: 0,
            id_pool,
            str_pool,
        };
        _self.cursor.next(); // Init cursor::stopped_at with first char
        _self
    }

    pub fn collect_all(mut self) -> (Vec<Token>, Vec<String>, Vec<LexerError>) {
        let tokens = self.by_ref().collect_vec();

        if self.file_lines.is_empty() {
            self.file_lines.push("".to_string());
        }

        (tokens, self.file_lines, self.errs)
    }

    fn next_token_type(&mut self) -> TokenKind {
        match self.cursor.stopped_at.1 {
            '/' => self.next_token_with_slash(),
            '،' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::Comma)
            }
            '؛' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::Semicolon)
            }
            '؟' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::QuestionMark)
            }
            '(' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::OpenParenthesis)
            }
            ')' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::CloseParenthesis)
            }
            '{' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::OpenCurlyBrace)
            }
            '}' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::CloseCurlyBrace)
            }
            '[' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::OpenSquareBracket)
            }
            ']' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::CloseSquareBracket)
            }
            '.' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::Dot)
            }
            '<' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::OpenAngleBracketOrLess)
            }
            '>' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::CloseAngleBracketOrGreater)
            }
            '*' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::Star)
            }
            '+' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::Plus)
            }
            '-' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::Minus)
            }
            '|' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::BitOr)
            }
            '&' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::BitAnd)
            }
            '%' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::Modulo)
            }
            '~' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::BitNot)
            }
            '^' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::Xor)
            }
            '!' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::ExclamationMark)
            }
            ':' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::Colon)
            }
            '=' => {
                self.next_cursor();
                TokenKind::Symbol(SymbolKind::Equal)
            }
            '\n' => {
                self.next_cursor();
                TokenKind::Eol
            }
            '0'..='9' => self.next_num_token(),
            '\'' => {
                let start = self.cursor.stopped_at.0;
                let start_byte = self.stopped_at_bidx;

                let mut last_is_backslash = false;

                loop {
                    let Some((_, ch)) = self.next_cursor_non_eol() else {
                        self.errs.push(LexerError {
                            token_idx: self.current_token_idx,
                            col: self.cursor.stopped_at.0.col,
                            len: 1,
                            kind: LexerErrorKind::UnclosedChar,
                        });
                        return TokenKind::Literal(LiteralKind::Char('\0'));
                    };

                    if ch == '\'' && !last_is_backslash {
                        self.next_cursor();
                        break;
                    }

                    last_is_backslash = ch == '\\';
                }

                let end = self.cursor.stopped_at.0;
                let end_byte = self.stopped_at_bidx;

                let chars = self.content[start_byte + 1..end_byte - 1].chars();
                let str = self.next_valid_nazm_rust_char_in_str(chars, start.col);
                let mut exact_chars = str.chars();

                let ch = match exact_chars.next() {
                    Some(ch) => {
                        if exact_chars.next().is_some() {
                            self.errs.push(LexerError {
                                token_idx: self.current_token_idx,
                                col: start.col + 1,
                                len: end.col - start.col - 2,
                                kind: LexerErrorKind::ManyChars,
                            });
                        }
                        ch
                    }
                    None => {
                        self.errs.push(LexerError {
                            token_idx: self.current_token_idx,
                            col: start.col,
                            len: 2,
                            kind: LexerErrorKind::ZeroChars,
                        });
                        '\0'
                    }
                };

                TokenKind::Literal(LiteralKind::Char(ch))
            }
            '\"' => {
                let start = self.cursor.stopped_at.0;
                let start_byte = self.stopped_at_bidx;

                let mut last_is_backslash = false;

                loop {
                    let Some((_, ch)) = self.next_cursor_non_eol() else {
                        self.errs.push(LexerError {
                            token_idx: self.current_token_idx,
                            col: self.cursor.stopped_at.0.col,
                            len: 1,
                            kind: LexerErrorKind::UnclosedStr,
                        });
                        let str_key = self.str_pool.get_key(&"".to_string());
                        return TokenKind::Literal(LiteralKind::Str(str_key));
                    };

                    if ch == '\"' && !last_is_backslash {
                        self.next_cursor();
                        break;
                    }

                    last_is_backslash = ch == '\\';
                }

                let end_byte = self.stopped_at_bidx;

                let chars = self.content[start_byte + 1..end_byte - 1].chars();

                let str = self.next_valid_nazm_rust_char_in_str(chars, start.col);

                let id_key = self.str_pool.get_key(&str);

                TokenKind::Literal(LiteralKind::Str(id_key))
            }
            '\t' | '\x0b' | '\x0C' | '\r' | ' ' => {
                while self
                    .next_cursor()
                    .is_some_and(|(_, ch)| (ch == '\x0b' || ch.is_ascii_whitespace()) && ch != '\n')
                {
                } // Skip whitespaces
                TokenKind::Space
            }
            _ => {
                if self.stopped_at_bidx == self.content.len() {
                    return TokenKind::Eof;
                }

                self.next_id_or_keyword()
            }
        }
    }

    fn next_cursor(&mut self) -> Option<(SpanCursor, char)> {
        let current_line = &self.content[self.current_line_start_bidx..self.stopped_at_bidx];

        let size = self.cursor.stopped_at.1.len_utf8();

        self.stopped_at_bidx += size;

        let stopped_at_eol = self.cursor.stopped_at.1 == '\n';

        if stopped_at_eol {
            self.file_lines.push(current_line.to_string());
            self.current_line_start_bidx = self.stopped_at_bidx;
        }

        let next = self.cursor.next();

        if next.is_none() {
            if stopped_at_eol {
                self.file_lines.push("".to_string());
            } else if self.current_line_start_bidx < self.content.len() {
                let current_line =
                    &self.content[self.current_line_start_bidx..self.stopped_at_bidx];
                self.file_lines.push(current_line.to_string());
                self.current_line_start_bidx = self.stopped_at_bidx;
            }
        }

        next
    }

    fn next_cursor_non_eol(&mut self) -> Option<(SpanCursor, char)> {
        match self.next_cursor() {
            Some((_, '\n')) => None,
            any => any,
        }
    }

    fn next_token_with_slash(&mut self) -> TokenKind {
        match self.next_cursor() {
            Some((_, '/')) => {
                while self.next_cursor_non_eol().is_some() {
                    // Skip all until first EOL
                    if let Err(err) = self.check_is_kufr_or_unsupported_char() {
                        self.errs.push(err);
                    }
                }

                TokenKind::LineComment
            }
            Some((_, '*')) => {
                let mut opened_delimted_comments = 1;

                while let Some((_, ch)) = self.next_cursor() {
                    if opened_delimted_comments == 0 {
                        break;
                    }

                    if ch == '/' && self.next_cursor().is_some_and(|(_, ch)| ch == '*') {
                        opened_delimted_comments += 1;
                    } else if ch == '*' && self.next_cursor().is_some_and(|(_, ch)| ch == '/') {
                        opened_delimted_comments -= 1;
                    }

                    if let Err(err) = self.check_is_kufr_or_unsupported_char() {
                        self.errs.push(err);
                    }
                }

                if opened_delimted_comments != 0 {
                    self.errs.push(LexerError {
                        token_idx: self.current_token_idx,
                        col: self.cursor.stopped_at.0.col,
                        len: 1,
                        kind: LexerErrorKind::UnclosedDelimitedComment,
                    });
                }

                TokenKind::DelimitedComment
            }
            _ => TokenKind::Symbol(SymbolKind::Slash),
        }
    }

    fn next_id_or_keyword(&mut self) -> TokenKind {
        let c = self.cursor.stopped_at.1;
        if !c.is_alphabetic() && c != '_' {
            let id_key = self.id_pool.get_key(&c.to_string());
            self.next_cursor();
            self.errs.push(LexerError {
                token_idx: self.current_token_idx,
                col: self.cursor.stopped_at.0.col - 1,
                len: 1,
                kind: LexerErrorKind::UnknownToken,
            });
            return TokenKind::Id(id_key);
        }

        let start = self.stopped_at_bidx;

        while self
            .next_cursor_non_eol()
            .is_some_and(|(_, ch)| ch.is_alphanumeric() || ch == '_')
        {}

        let end = self.stopped_at_bidx;

        let id = &self.content[start..end];

        if id == "صحيح" {
            return TokenKind::Literal(LiteralKind::Bool(true));
        } else if id == "فاسد" {
            return TokenKind::Literal(LiteralKind::Bool(false));
        }

        for keyword_typ in KeywordKind::iter() {
            if keyword_typ.get_variant_docs().is_ok_and(|val| id == val) {
                return TokenKind::Keyword(keyword_typ);
            }
        }

        let id_key = self.id_pool.get_key(&id.to_string());

        TokenKind::Id(id_key)
    }

    #[inline]
    fn check_is_kufr_or_unsupported_char(&self) -> Result<Option<char>, LexerError> {
        let (start, ch) = self.cursor.stopped_at;

        if is_kufr_or_unsupported_character(ch) {
            Err(LexerError {
                token_idx: self.current_token_idx,
                col: start.col,
                len: 1,
                kind: LexerErrorKind::KufrOrInvalidChar,
            })
        } else {
            Ok(Some(ch))
        }
    }
}

#[derive(Clone)]
struct CharsCursor<'a> {
    stopped_at: (SpanCursor, char),
    chars: Chars<'a>,
}

impl<'a> CharsCursor<'a> {
    fn new(text: &'a str) -> Self {
        Self {
            stopped_at: (SpanCursor { line: 0, col: 0 }, '\0'),
            chars: text.chars(),
        }
    }
}

impl<'a> Iterator for CharsCursor<'a> {
    type Item = (SpanCursor, char);

    fn next(&mut self) -> Option<Self::Item> {
        if self.stopped_at.1 != '\0' {
            // Not the first time to call the `next` method
            self.stopped_at.0.col += 1; // Update the column
        }
        if self.stopped_at.1 == '\n' {
            // Last was a new line character
            self.stopped_at.0.line += 1; // Update the line
            self.stopped_at.0.col = 0; // Reset the column
        }

        match self.chars.next() {
            Some(ch) => {
                self.stopped_at.1 = ch; // Update the character
                Some(self.stopped_at)
            }
            None => {
                self.stopped_at.1 = '\0'; // Update the character
                None
            }
        }
    }
}

fn is_kufr_or_unsupported_character(c: char) -> bool {
    let chars = [
        '\u{03EE}', '\u{03EF}', '\u{058d}', '\u{058e}', '\u{05EF}', // yod triangle
        '\u{07D9}', '\u{093B}', '\u{13D0}', '\u{16BE}', '\u{165C}', '\u{16ED}', '\u{17D2}',
        '\u{1D7B}', '\u{2020}', '\u{2021}', '\u{256A}', '\u{256B}', '\u{256C}', '\u{2616}',
        '\u{2617}', '\u{269C}', '\u{269E}', '\u{269F}', '\u{26AF}', '\u{26B0}', '\u{26B1}',
        '\u{26F3}', '\u{26F9}', '\u{26FB}', '\u{26FF}', '\u{27CA}', '\u{29FE}', '\u{2CFE}',
    ];

    if chars.contains(&c) {
        return true;
    }

    let ranges = [
        /*  from  ,    to  */
        ('\u{0900}', '\u{109F}'), //HinduEurope
        ('\u{1100}', '\u{1C7F}'), //HinduEurope
        ('\u{253C}', '\u{254B}'),
        ('\u{2624}', '\u{2638}'), //Kufr
        ('\u{263D}', '\u{2653}'), //Kufr
        ('\u{2654}', '\u{2667}'),
        ('\u{2669}', '\u{2671}'), //Music and kufr crosses
        ('\u{2680}', '\u{268F}'),
        ('\u{2680}', '\u{268F}'),
        ('\u{26A2}', '\u{26A9}'), // Pride
        ('\u{26B3}', '\u{26BC}'), // Kufr
        ('\u{26BF}', '\u{26EC}'),
        ('\u{2719}', '\u{2725}'), // Kufr crosses
        ('\u{2BF0}', '\u{2C5F}'), // Includes astrology
        ('\u{2D80}', '\u{AB2F}'),
        ('\u{AB70}', '\u{FAFF}'),
    ];

    for (r1, r2) in ranges {
        if c >= r1 && c <= r2 {
            return true;
        }
    }

    false
}

#[cfg(test)]

mod tests {
    use std::vec;

    use super::{KeywordKind, LexerIter, SymbolKind};
    use crate::{lexer::TokenKind, Token};
    use documented::DocumentedVariants;
    use itertools::Itertools;
    use nazmc_data_pool::DataPool;
    use nazmc_diagnostics::span::{Span, SpanCursor};
    use strum::IntoEnumIterator;

    #[test]
    fn test_lines() {
        let mut id_pool = DataPool::new();
        let mut str_pool = DataPool::new();
        assert_eq!(
            vec![""],
            LexerIter::new("", &mut id_pool, &mut str_pool)
                .collect_all()
                .1
        );

        let content = concat!(
            "\n",
            "/*\n",
            "multiline comment\n",
            "*/\n",
            "123456789\n",
            "\n",
            "احجز\n",
            "\n",
            "a\n",
        );

        let lexer: LexerIter = LexerIter::new(content, &mut id_pool, &mut str_pool);

        let (_, lines, _) = lexer.collect_all();
        let expected_lines = content.split('\n').collect_vec();

        assert_eq!(expected_lines, lines);

        // No new line at the end
        let content = concat!(
            "\n",
            "/*\n",
            "multiline comment\n",
            "*/\n",
            "123456789\n",
            "\n",
            "احجز\n",
            "\n",
            "a",
        );

        let lexer: LexerIter = LexerIter::new(content, &mut id_pool, &mut str_pool);

        let (_, lines, _) = lexer.collect_all();
        let expected_lines = content.split('\n').collect_vec();

        assert_eq!(expected_lines, lines);
    }

    #[test]
    fn test_symbols_lexing() {
        let mut id_pool = DataPool::new();
        let mut str_pool = DataPool::new();
        for symbol in SymbolKind::iter() {
            let symbol_val = symbol.get_variant_docs().unwrap();
            let Token {
                span,
                kind,
                start_byte,
                end_byte,
            } = LexerIter::new(symbol_val, &mut id_pool, &mut str_pool)
                .next()
                .unwrap();

            let val = &symbol_val[start_byte..end_byte];

            assert_eq!(
                span,
                Span {
                    start: SpanCursor { line: 0, col: 0 },
                    end: SpanCursor {
                        line: 0,
                        col: symbol_val.chars().count()
                    },
                }
            );
            assert_eq!(val, symbol_val);
            assert_eq!(kind, TokenKind::Symbol(symbol));
        }

        let mut symbols_line = String::new();
        for symbol in SymbolKind::iter() {
            let symbol_val = symbol.get_variant_docs().unwrap();
            symbols_line.push_str(symbol_val);
        }

        let tokens = LexerIter::new(&symbols_line, &mut id_pool, &mut str_pool);
        let mut symbols_iter = SymbolKind::iter();
        let mut columns = 0;

        for Token {
            span,
            kind,
            start_byte,
            end_byte,
        } in tokens
        {
            let val = &symbols_line[start_byte..end_byte];
            let symbol = symbols_iter.next().unwrap();
            let symbol_val = symbol.get_variant_docs().unwrap();

            assert_eq!(
                span,
                Span {
                    start: SpanCursor {
                        line: 0,
                        col: columns
                    },
                    end: SpanCursor {
                        line: 0,
                        col: columns + symbol_val.chars().count()
                    },
                },
                "Maybe the tokens are overlapping for left: `{}`, right: `{}`",
                val,
                symbol_val
            );

            columns += symbol_val.chars().count();

            assert_eq!(val, symbol_val);
            assert_eq!(kind, TokenKind::Symbol(symbol));
        }

        let mut symbols_line = String::new();
        for symbol in SymbolKind::iter() {
            let symbol_val = symbol.get_variant_docs().unwrap();
            symbols_line.push_str(symbol_val);
            symbols_line.push('\n');
        }

        let mut tokens = LexerIter::new(&symbols_line, &mut id_pool, &mut str_pool);
        let mut symbols_iter = SymbolKind::iter();
        let mut lines = 0;

        while let Some(Token {
            span,
            kind,
            start_byte,
            end_byte,
        }) = tokens.next()
        {
            let val = &symbols_line[start_byte..end_byte];
            let symbol = symbols_iter.next().unwrap();
            let symbol_val = symbol.get_variant_docs().unwrap();

            assert_eq!(
                span,
                Span {
                    start: SpanCursor {
                        line: lines,
                        col: 0
                    },
                    end: SpanCursor {
                        line: lines,
                        col: symbol_val.chars().count()
                    },
                },
                "Maybe the tokens are overlapping for left: `{}`, right: `{}`",
                val,
                symbol_val
            );

            assert_eq!(val, symbol_val);
            assert_eq!(kind, TokenKind::Symbol(symbol));

            let Token {
                span,
                kind,
                start_byte,
                end_byte,
            } = tokens.next().unwrap();

            assert_eq!(
                span,
                Span {
                    start: SpanCursor {
                        line: lines,
                        col: symbol_val.chars().count()
                    },
                    end: SpanCursor {
                        line: lines + 1,
                        col: 0
                    },
                },
                "On symbol `{}`",
                symbol_val
            );

            assert_eq!(val, "\n");
            assert_eq!(kind, TokenKind::Eol);
            lines += 1;
        }
    }

    #[test]
    fn test_keywords_lexing() {
        let mut id_pool = DataPool::new();
        let mut str_pool = DataPool::new();
        for keyword in KeywordKind::iter() {
            let keyword_val = keyword.get_variant_docs().unwrap();
            let Token {
                span,
                kind,
                start_byte,
                end_byte,
            } = LexerIter::new(keyword_val, &mut id_pool, &mut str_pool)
                .next()
                .unwrap();

            let val = &keyword_val[start_byte..end_byte];

            assert_eq!(
                span,
                Span {
                    start: SpanCursor { line: 0, col: 0 },
                    end: SpanCursor {
                        line: 0,
                        col: keyword_val.chars().count()
                    },
                }
            );
            assert_eq!(val, keyword_val);
            assert_eq!(kind, TokenKind::Keyword(keyword));
        }
    }
}
