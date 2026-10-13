//! Source views keep physical offsets while excluding comments from facts.

/// Apply the same proved-inactive ranges to syntax and evidence views.
pub(super) fn mask_ranges(source: &str, ranges: &[std::ops::Range<usize>]) -> Option<String> {
    if ranges.is_empty() {
        return None;
    }
    let mut masked = source.as_bytes().to_vec();
    let mut changed = false;
    for range in ranges {
        for byte in &mut masked[range.clone()] {
            if !matches!(*byte, b'\n' | b'\r' | b' ' | b'\t') {
                *byte = b' ';
                changed = true;
            }
        }
    }
    changed
        .then(|| String::from_utf8(masked).expect("whole inactive byte regions replaced by ASCII"))
}

/// Replace comments with spaces, preserving every byte offset and newline.
/// Literals are skipped lexically, including raw strings and digit separators.
pub(super) fn mask_comments(source: &str) -> String {
    let mut masked = source.as_bytes().to_vec();
    let mut offset = 0;
    while offset < source.len() {
        if let Some((end, comment)) = opaque_span(source, offset) {
            if comment {
                for byte in &mut masked[offset..end] {
                    if !matches!(*byte, b'\n' | b'\r') {
                        *byte = b' ';
                    }
                }
            }
            offset = end;
        } else {
            offset = token_end(source, offset);
        }
    }
    String::from_utf8(masked).expect("complete comment byte spans replaced with ASCII")
}

/// Tokens for bounded attribute recognition. Quoted text is never an attribute.
pub(in crate::cpp_detection) fn code_tokens(source: &str) -> Vec<&str> {
    let mut tokens = Vec::new();
    let mut offset = 0;
    while offset < source.len() {
        if let Some((end, _)) = opaque_span(source, offset) {
            offset = end;
        } else {
            let end = token_end(source, offset);
            if !source[offset..end].trim().is_empty() {
                tokens.push(&source[offset..end]);
            }
            offset = end;
        }
    }
    tokens
}

fn token_end(source: &str, start: usize) -> usize {
    let bytes = source.as_bytes();
    let numeric = bytes[start].is_ascii_digit();
    if bytes[start].is_ascii_alphanumeric() || bytes[start] == b'_' || bytes[start] >= 128 {
        let mut end = start + 1;
        while end < bytes.len()
            && (bytes[end].is_ascii_alphanumeric()
                || bytes[end] == b'_'
                || bytes[end] >= 128
                || (numeric && matches!(bytes[end], b'\'' | b'.')))
        {
            end += 1;
        }
        end
    } else {
        start + 1
    }
}

fn opaque_span(source: &str, start: usize) -> Option<(usize, bool)> {
    let rest = &source[start..];
    if rest.starts_with('<') {
        let line_start = source[..start].rfind('\n').map_or(0, |newline| newline + 1);
        let prefix = source[line_start..start].trim_start();
        if prefix.starts_with('#') && (prefix.contains("include") || prefix.contains("import")) {
            let directive = code_tokens(prefix);
            if matches!(
                directive.as_slice(),
                ["#", "include" | "include_next" | "import"]
            ) && let Some(close) = rest.find('>')
                && !rest[..close].contains(['\n', '\r'])
            {
                // A header-name preprocessing token can itself contain //.
                return Some((start + close + 1, false));
            }
        }
    }
    if rest.starts_with("//") {
        let bytes = source.as_bytes();
        let mut end = start + 2;
        while end < bytes.len() {
            if bytes[end] == b'\n' {
                let preceding = end - usize::from(end > 0 && bytes[end - 1] == b'\r');
                if preceding == 0 || bytes[preceding - 1] != b'\\' {
                    break;
                }
            }
            end += 1;
        }
        return Some((end, true));
    }
    if let Some(after_open) = rest.strip_prefix("/*") {
        // Keep malformed input visible to parser diagnostics.
        return Some(match after_open.find("*/") {
            Some(end) => (start + 2 + end + 2, true),
            None => (source.len(), false),
        });
    }
    for prefix in ["u8R\"", "uR\"", "UR\"", "LR\"", "R\""] {
        if let Some(after_prefix) = rest.strip_prefix(prefix)
            && let Some(open) = after_prefix.find('(')
            && open <= 16
            && !after_prefix[..open]
                .bytes()
                .any(|b| b.is_ascii_whitespace() || matches!(b, b')' | b'\\'))
        {
            let terminator = format!("){}\"", &after_prefix[..open]);
            let end = after_prefix[open + 1..]
                .find(&terminator)
                .map_or(source.len(), |close| {
                    start + prefix.len() + open + 1 + close + terminator.len()
                });
            return Some((end, false));
        }
    }
    let prefix = ["u8", "u", "U", "L", ""].into_iter().find(|prefix| {
        rest.strip_prefix(prefix)
            .is_some_and(|s| s.starts_with(['\"', '\'']))
    })?;
    let bytes = source.as_bytes();
    let quote = bytes[start + prefix.len()];
    let mut end = start + prefix.len() + 1;
    while end < bytes.len() {
        match bytes[end] {
            b'\\' => end = (end + 2).min(bytes.len()),
            byte if byte == quote => return Some((end + 1, false)),
            _ => end += 1,
        }
    }
    Some((source.len(), false))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn comments_are_masked_without_changing_positions_or_literals() {
        let source = concat!(
            "int first; /* 中文 alignas(64)\r\nsecond */ int second;\n",
            "// std::thread fake \\\n continued fake code\n",
            "const char* text = \"literal//literal/*literal*/\";\n",
            "const char* escaped = \"\\\" // literal\";\n",
            "const char* raw = u8R\"tag(/* // \" literal */)tag\";\n",
            "char slash = '/'; int count = 1'000; // real comment\n",
            "#include /* header comment */ <directory//header.hpp>\n",
        );
        let masked = mask_comments(source);
        assert_eq!(source.len(), masked.len());
        for (before, after) in source.bytes().zip(masked.bytes()) {
            if matches!(before, b'\n' | b'\r') {
                assert_eq!(before, after);
            }
        }
        for literal in [
            "\"literal//literal/*literal*/\"",
            "\"\\\" // literal\"",
            "u8R\"tag(/* // \" literal */)tag\"",
            "'/'",
            "1'000",
            "<directory//header.hpp>",
        ] {
            assert!(masked.contains(literal), "{masked}");
        }
        for comment in [
            "中文",
            "alignas(64)",
            "std::thread",
            "continued fake",
            "real comment",
        ] {
            assert!(!masked.contains(comment), "{masked}");
        }
        assert_eq!(source.find("int second"), masked.find("int second"));
    }

    #[test]
    fn attribute_tokens_exclude_literals_and_comments() {
        assert_eq!(
            code_tokens("alignas(64) /* aligned(128) */ const char* p = R\"x(aligned(256))x\";"),
            [
                "alignas", "(", "64", ")", "const", "char", "*", "p", "=", ";"
            ]
        );
    }

    #[test]
    fn unterminated_comments_remain_visible_to_parser_diagnostics() {
        let source = "int first; /* missing end";
        assert_eq!(mask_comments(source), source);
    }
}
