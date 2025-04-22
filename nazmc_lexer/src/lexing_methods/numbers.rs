use crate::*;

impl<'a> LexerIter<'a> {
    pub(crate) fn next_num_token(&mut self) -> TokenKind {
        let result = self.next_num_kind();
        match result {
            Ok(num_kind) => TokenKind::Literal(LiteralKind::Num(num_kind)),
            Err(mut err) => {
                let num_kind = match err.kind.clone() {
                    LexerErrorKind::MissingDigitsAfterExponent
                    | LexerErrorKind::InvalidFloatSuffix => NumKind::UnspecifiedFloat(0.0),
                    LexerErrorKind::NumIsOutOfRange(num_kind) => num_kind,
                    _ => NumKind::UnspecifiedInt(0),
                };

                err.token_idx = self.current_token_idx;

                self.errs.push(err);
                TokenKind::Literal(LiteralKind::Num(num_kind))
            }
        }
    }

    fn next_num_kind(&mut self) -> Result<NumKind, LexerError> {
        let prefix = &self.content[self.stopped_at_bidx..];

        if prefix.starts_with("2#") {
            self.next_cursor();
            self.next_cursor();
            self.next_cursor(); // Skip "2#" and stop on next digit
            return self.next_num_sys_token(Base::Bin, |d| matches!(d, b'0' | b'1'));
        }

        if prefix.starts_with("8#") {
            self.next_cursor();
            self.next_cursor();
            self.next_cursor(); // Skip "8#" and stop on next digit
            return self.next_num_sys_token(Base::Oct, |d| matches!(d, b'0'..=b'7'));
        }

        if prefix.starts_with("16#") {
            self.next_cursor();
            self.next_cursor();
            self.next_cursor(); // Skip "16#" and stop on next digit
            return self.next_hex_num_token();
        }

        let start_col = self.cursor.stopped_at.0.col;

        let mut digits = self.next_digits_array();

        if self.cursor.stopped_at.1 == '#' {
            let digits_len = self.cursor.stopped_at.0.col - start_col;
            self.next_cursor(); // Skip "#" and stop on next digit
            let _ = self.next_hex_num_token(); // Fabricate and skip any hex digits and any suffixes
            return Err(LexerError {
                token_idx: self.current_token_idx,
                col: start_col,
                len: digits_len,
                kind: LexerErrorKind::InvalidIntBasePrefix,
            });
        }

        let dot_or_exp = &self.content[self.stopped_at_bidx..];

        if !dot_or_exp.starts_with("^^") && !dot_or_exp.starts_with(".") {
            let digits_len = self.cursor.stopped_at.0.col - start_col;

            let suffix_str = self.next_valid_num_suffix()?;

            // Maybe an int or maybe a float depending on the suffix
            let int_token = to_int_token(&digits, suffix_str, start_col, digits_len, Base::Dec);

            let Err(LexerError {
                kind: LexerErrorKind::InvalidIntSuffix,
                ..
            }) = int_token
            else {
                return int_token;
            };

            // Invalid int suffix, so try float suffixes

            let mut float_token = to_float_token(&digits, suffix_str, start_col, digits_len);

            if let Err(
                ref mut err @ LexerError {
                    kind: LexerErrorKind::InvalidFloatSuffix,
                    ..
                },
            ) = float_token
            {
                // Invalid suffix
                err.kind = LexerErrorKind::InvalidNumSuffix;
            }

            return float_token;
        }

        if dot_or_exp.starts_with(".") {
            let after_dot = &self.content[self.stopped_at_bidx + 1..];

            // Number before dot may be treated as an int object, so check if after the dot is a digit to build the float
            if !after_dot.starts_with(|ch: char| ch.is_ascii_digit()) {
                let digits_len = self.cursor.stopped_at.0.col - start_col;

                // After the dot is not a digit, so treat it as an int with no suffix
                return to_int_token(&digits, "", start_col, digits_len, Base::Dec);
            }

            digits.push('.');

            // Append digits after the dot
            self.skip_digits_and_commas(&mut digits);
        }

        let dot_or_exp = &self.content[self.stopped_at_bidx..];

        if dot_or_exp.starts_with("^^") {
            digits.push('E');

            self.next_cursor();
            self.next_cursor(); // Skip the "^^"

            if matches!(self.cursor.stopped_at.1, '+' | '-') {
                digits.push(self.cursor.stopped_at.1); // Append the sign
                self.next_cursor(); // Skip the sign
            }

            match self.cursor.stopped_at.1 {
                '0'..='9' => {
                    // Append the first digit
                    digits.push(self.cursor.stopped_at.1);
                    // Append digits after the exponent
                    self.skip_digits_and_commas(&mut digits);
                }
                _ => {
                    return Err(LexerError {
                        token_idx: self.current_token_idx,
                        col: start_col,
                        len: 0, // Mark the number instead
                        kind: LexerErrorKind::MissingDigitsAfterExponent,
                    });
                }
            }
        }

        let digits_len = self.cursor.stopped_at.0.col - start_col;

        let suffix_str = self.next_valid_num_suffix()?;

        to_float_token(&digits, suffix_str, start_col, digits_len)
    }

    fn skip_hexdigits_and_commas(&mut self, digits: &mut String) {
        let mut last_commas_len = 0;

        while let Some((_, ch)) = self.next_cursor_non_eol() {
            if ch.is_ascii_hexdigit() {
                digits.push(ch);
                last_commas_len = 0;
            }
            // Skip commas
            else if ch == ',' {
                last_commas_len += 1;
            } else {
                break;
            }
        }

        if last_commas_len > 0 {
            self.errs.push(LexerError {
                token_idx: self.current_token_idx,
                col: self.cursor.stopped_at.0.col - last_commas_len,
                len: last_commas_len,
                kind: LexerErrorKind::DigitsEndWithCommma,
            });
        }
    }

    fn skip_digits_and_commas(&mut self, digits: &mut String) {
        let mut last_commas_len = 0;

        while let Some((_, ch)) = self.next_cursor_non_eol() {
            if ch.is_ascii_digit() {
                digits.push(ch);
                last_commas_len = 0;
            }
            // Skip commas
            else if ch == ',' {
                last_commas_len += 1;
            } else {
                break;
            }
        }

        if last_commas_len > 0 {
            self.errs.push(LexerError {
                token_idx: self.current_token_idx,
                col: self.cursor.stopped_at.0.col - last_commas_len,
                len: last_commas_len,
                kind: LexerErrorKind::DigitsEndWithCommma,
            });
        }
    }

    fn next_digits_array(&mut self) -> String {
        let stopped_char = self.cursor.stopped_at.1;
        let mut digits = String::new();

        if !stopped_char.is_ascii_digit() {
            return digits;
        }

        digits.push(stopped_char);

        self.skip_digits_and_commas(&mut digits);

        digits
    }

    fn next_num_sys_token(
        &mut self,
        base: Base,
        match_digit: impl Fn(u8) -> bool,
    ) -> Result<NumKind, LexerError> {
        let prefix_end_col = self.cursor.stopped_at.0.col;

        let digits = self.next_digits_array();

        let digits_len = self.cursor.stopped_at.0.col - prefix_end_col;

        let suffix = self.next_valid_num_suffix();

        if digits.is_empty() {
            return missing_digits_after_base_prefix_bad_token(prefix_end_col);
        }

        for (i, digit) in digits.bytes().enumerate() {
            if !match_digit(digit) {
                return invalid_digit_for_base_prefix_bad_token(Base::Bin, prefix_end_col + i);
            }
        }

        match suffix {
            Ok(suffix_str) => to_int_token(&digits, suffix_str, prefix_end_col, digits_len, base),
            Err(mut err) => {
                err.kind = LexerErrorKind::InvalidIntSuffix;
                Err(err)
            }
        }
    }

    fn next_hex_num_token(&mut self) -> Result<NumKind, LexerError> {
        let prefix_end_col = self.cursor.stopped_at.0.col;
        let stopped_char = self.cursor.stopped_at.1;
        let mut digits = String::new();

        if !stopped_char.is_ascii_hexdigit() {
            let _ = self.next_valid_num_suffix(); // Skip any suffixes
            return missing_digits_after_base_prefix_bad_token(prefix_end_col);
        }

        digits.push(stopped_char);

        self.skip_hexdigits_and_commas(&mut digits);

        let digits_len = self.cursor.stopped_at.0.col - prefix_end_col;
        let suffix = self.next_valid_num_suffix();

        match suffix {
            Ok(suffix_str) => {
                to_int_token(&digits, suffix_str, prefix_end_col, digits_len, Base::Hex)
            }
            Err(mut err) => {
                err.kind = LexerErrorKind::InvalidIntSuffix;
                Err(err)
            }
        }
    }

    fn next_valid_num_suffix(&mut self) -> Result<&str, LexerError> {
        if !self.cursor.stopped_at.1.is_alphabetic() {
            return Ok("");
        }

        let start_col = self.cursor.stopped_at.0.col;
        let start = self.stopped_at_bidx;

        while self
            .next_cursor_non_eol()
            .is_some_and(|(_, ch)| ch.is_alphanumeric() || ch == '_')
        {}

        let end_col = self.cursor.stopped_at.0.col;
        let end = self.stopped_at_bidx;

        let id = &self.content[start..end];

        match id {
            "ص1" | "ص2" | "ص4" | "ص8" | "ص" | "ط1" | "ط2" | "ط4" | "ط8" | "ط" | "ع4" | "ع8" => {
                Ok(id)
            }
            _ => Err(LexerError {
                token_idx: self.current_token_idx,
                col: start_col,
                len: end_col - start_col,
                kind: LexerErrorKind::InvalidNumSuffix,
            }),
        }
    }
}

fn to_int_token(
    digits: &str,
    suffix_str: &str,
    start_col: usize,
    len: usize,
    base: Base,
) -> Result<NumKind, LexerError> {
    let radix = base.clone() as u32;

    if suffix_str.is_empty() {
        return match u64::from_str_radix(digits, radix) {
            Ok(num) => Ok(NumKind::UnspecifiedInt(num)),
            Err(_) => num_is_out_of_range_bad_token(start_col, len, NumKind::UnspecifiedInt(0)),
        };
    }

    if suffix_str == "ص" {
        return match isize::from_str_radix(digits, radix) {
            Ok(num) => Ok(NumKind::I(num)),
            Err(_) => num_is_out_of_range_bad_token(start_col, len, NumKind::I(0)),
        };
    }

    if suffix_str == "ص1" {
        return match i8::from_str_radix(digits, radix) {
            Ok(num) => Ok(NumKind::I1(num)),
            Err(_) => num_is_out_of_range_bad_token(start_col, len, NumKind::I1(0)),
        };
    }

    if suffix_str == "ص2" {
        return match i16::from_str_radix(digits, radix) {
            Ok(num) => Ok(NumKind::I2(num)),
            Err(_) => num_is_out_of_range_bad_token(start_col, len, NumKind::I2(0)),
        };
    }

    if suffix_str == "ص4" {
        return match i32::from_str_radix(digits, radix) {
            Ok(num) => Ok(NumKind::I4(num)),
            Err(_) => num_is_out_of_range_bad_token(start_col, len, NumKind::I4(0)),
        };
    }

    if suffix_str == "ص8" {
        return match i64::from_str_radix(digits, radix) {
            Ok(num) => Ok(NumKind::I8(num)),
            Err(_) => num_is_out_of_range_bad_token(start_col, len, NumKind::I8(0)),
        };
    }

    if suffix_str == "ط" {
        return match usize::from_str_radix(digits, radix) {
            Ok(num) => Ok(NumKind::U(num)),
            Err(_) => num_is_out_of_range_bad_token(start_col, len, NumKind::U(0)),
        };
    }

    if suffix_str == "ط1" {
        return match u8::from_str_radix(digits, radix) {
            Ok(num) => Ok(NumKind::U1(num)),
            Err(_) => num_is_out_of_range_bad_token(start_col, len, NumKind::U1(0)),
        };
    }

    if suffix_str == "ط2" {
        return match u16::from_str_radix(digits, radix) {
            Ok(num) => Ok(NumKind::U2(num)),
            Err(_) => num_is_out_of_range_bad_token(start_col, len, NumKind::U2(0)),
        };
    }

    if suffix_str == "ط4" {
        return match u32::from_str_radix(digits, radix) {
            Ok(num) => Ok(NumKind::U4(num)),
            Err(_) => num_is_out_of_range_bad_token(start_col, len, NumKind::U4(0)),
        };
    }

    if suffix_str == "ط8" {
        return match u64::from_str_radix(digits, radix) {
            Ok(num) => Ok(NumKind::U8(num)),
            Err(_) => num_is_out_of_range_bad_token(start_col, len, NumKind::U8(0)),
        };
    }

    Err(LexerError {
        token_idx: 0, // It will be changed later
        col: start_col + len,
        len: suffix_str.len(),
        kind: LexerErrorKind::InvalidIntSuffix,
    })
}

fn to_float_token(
    digits: &str,
    suffix_str: &str,
    start_col: usize,
    len: usize,
) -> Result<NumKind, LexerError> {
    if suffix_str.is_empty() {
        return match digits.parse() {
            Ok(num) => Ok(NumKind::UnspecifiedFloat(num)),
            Err(_) => num_is_out_of_range_bad_token(start_col, len, NumKind::UnspecifiedFloat(0.0)),
        };
    }

    if suffix_str == "ع4" {
        return match digits.parse() {
            Ok(num) => Ok(NumKind::F4(num)),
            Err(_) => num_is_out_of_range_bad_token(start_col, len, NumKind::F4(0.0)),
        };
    }

    if suffix_str == "ع8" {
        return match digits.parse() {
            Ok(num) => Ok(NumKind::F8(num)),
            Err(_) => num_is_out_of_range_bad_token(start_col, len, NumKind::F8(0.0)),
        };
    }

    Err(LexerError {
        token_idx: 0, // It will be changed later
        col: start_col + len,
        len: suffix_str.len(),
        kind: LexerErrorKind::InvalidFloatSuffix,
    })
}

#[inline]
fn missing_digits_after_base_prefix_bad_token(col: usize) -> Result<NumKind, LexerError> {
    Err(LexerError {
        token_idx: 0, // It will be changed later
        col,
        len: 0, // Mark the prefix instead
        kind: LexerErrorKind::MissingDigitsAfterBasePrefix,
    })
}

#[inline]
fn invalid_digit_for_base_prefix_bad_token(base: Base, col: usize) -> Result<NumKind, LexerError> {
    Err(LexerError {
        token_idx: 0, // It will be changed later
        col,
        len: 1, // The first digit
        kind: LexerErrorKind::InvalidDigitForBase(base),
    })
}

#[inline]
fn num_is_out_of_range_bad_token(
    col: usize,
    len: usize,
    num_kind: NumKind,
) -> Result<NumKind, LexerError> {
    Err(LexerError {
        token_idx: 0, // It will be changed later
        col,
        len,
        kind: LexerErrorKind::NumIsOutOfRange(num_kind),
    })
}
