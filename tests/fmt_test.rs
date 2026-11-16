use move_command_line_common::files::FileHash;
use move_compiler::parser::lexer::Lexer;
use movefmt::{
    core::token_tree::{CommentExtrator, CommentExtratorErr, TokenTree},
    tools::movefmt_diff,
    tools::utils::*,
};
use std::path::Path;
use std::time::Instant;
use tracing_subscriber::EnvFilter;

fn scan_dir(dir: &str) -> usize {
    let mut num: usize = 0;
    for x in walkdir::WalkDir::new(dir) {
        let x = match x {
            Ok(x) => x,
            Err(_) => {
                return num;
            }
        };
        if x.file_type().is_file()
            && x.file_name().to_str().unwrap().ends_with(".move")
            && !x.file_name().to_str().unwrap().contains(".fmt")
            && !x.file_name().to_str().unwrap().contains(".out")
        {
            let p = x.clone().into_path();
            let result = test_on_file(p.as_path());
            if !result {
                continue;
            }
            num += 1;

            let index = p.to_str().unwrap().rfind(".").unwrap();
            let mut expected_filename = p.to_str().unwrap()[0..index].to_string();
            expected_filename.push_str(".fmt.move");

            let mut actual_filename = p.to_str().unwrap()[0..index].to_string();
            actual_filename.push_str(".fmt.out");

            movefmt_diff::assert_output(Path::new(&actual_filename), Path::new(&expected_filename));
        }
    }
    num
}

#[test]
fn test_single_file() {
    eprintln!("================== test_single_file ===================");
    if std::env::var("MOVEFMT_LOG").is_err() {
        unsafe { std::env::set_var("MOVEFMT_LOG", "movefmt=ERROR") };
        tracing_subscriber::fmt()
            .with_env_filter(EnvFilter::from_env("MOVEFMT_LOG"))
            .init();
    }

    test_on_file(Path::new("./tests/bug2/issue79/input1.move"));
}

fn test_on_file(p: impl AsRef<Path>) -> bool {
    let p = p.as_ref();
    eprintln!("try format:{:?}", p);
    let content_origin = std::fs::read_to_string(&p).unwrap();
    {
        match movefmt::core::weight::parse_defs(&content_origin) {
            Ok(_) => {}
            Err(_) => {
                eprintln!("file '{:?}' skipped because of parse not ok", p);
                return false;
            }
        }
    }
    let content_origin = std::fs::read_to_string(p).unwrap();
    test_content(content_origin.as_str(), p);
    true
}

fn test_content(content_origin: &str, p: impl AsRef<Path>) {
    let p = p.as_ref();
    let tokens_origin =
        extract_tokens(content_origin).expect("test file should be about to lexer,err:{:?}");

    let content_format =
        movefmt::core::fmt::format_entry(content_origin, commentfmt::Config::default()).unwrap();

    let tokens_format = match extract_tokens(content_format.as_str()) {
        Ok(x) => x,
        Err(err) => {
            unreachable!(
                "should be able to parse after format:err{:?},after format:\n\n################\n{}\n###############",
                err, content_format
            );
        }
    };
    for (t1, t2) in tokens_origin.iter().zip(tokens_format.iter()) {
        assert_eq!(
            t1.content,
            t2.content,
            "format not ok,file:{:?} line:{} col:{},after format line:{} col:{}",
            p,
            // +1 in vscode UI line and col start with 1
            t1.line + 1,
            t1.col + 1,
            t2.line + 1,
            t2.col + 1,
        );
    }
    assert_eq!(
        tokens_origin.len(),
        tokens_format.len(),
        "{:?} tokens count should equal",
        p
    );
    let comments_origin = extract_comments(&content_origin).unwrap();
    let comments_format = extract_comments(&content_format).unwrap();
    for (index, (c1, c2)) in comments_origin
        .iter()
        .zip(comments_format.iter())
        .enumerate()
    {
        let len1 = c1.trim_end_matches(&['\r', '\n'][..]).len();
        let len2 = c2.trim_end_matches(&['\r', '\n'][..]).len();
        assert_eq!(
            c1.clone().truncate(len1),
            c2.clone().truncate(len2),
            "comment {} not ok.",
            index
        );
    }
    assert_eq!(
        comments_origin.len(),
        comments_format.len(),
        "{:?} comments count should equal",
        p,
    );

    let result_file_path = mk_result_filepath(&p.to_path_buf());
    let _ = std::fs::write(result_file_path.clone(), content_format);
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct ExtractToken {
    content: String,
    line: u32,
    col: u32,
}

fn extract_comments(content: &str) -> Result<Vec<String>, CommentExtratorErr> {
    let c = CommentExtrator::new(content)?;
    let c: Vec<_> = c
        .comments
        .into_iter()
        .map(|x| x.content)
        .map(|x| x.replacen(" ", "", usize::MAX))
        .map(|x| x.replacen("\t", "", usize::MAX))
        .map(|x| x.replacen("\n", "", usize::MAX))
        .collect();
    Ok(c)
}

fn extract_tokens(content: &str) -> Result<Vec<ExtractToken>, Vec<String>> {
    let p = Path::new(".").to_path_buf();
    let mut line_mapping = FileLineMapping::default();
    line_mapping.update(p.clone(), &content);
    let filehash = FileHash::empty();
    let defs = match movefmt::core::weight::parse_defs(content) {
        Ok(x) => x,
        Err(d) => {
            let mut ret = Vec::with_capacity(d.len());
            for x in d.into_codespan_format() {
                let (_s, msg, (loc, m), _, _notes) = x;
                let loc = line_mapping.translate(&p, loc.start(), loc.end()).unwrap();
                ret.push(format!(
                    "{}:{} {}",
                    loc.line_start + 1,
                    loc.col_start + 1,
                    format_args!("{}\n{}", msg, m)
                ));
            }
            return Err(ret);
        }
    };
    let lexer = Lexer::new(content, filehash);
    let mut ret = Vec::new();
    let parse = movefmt::core::token_tree::Parser::new(lexer, &defs, content);
    let token_tree = parse.parse_tokens();
    let mut line_mapping = FileLineMapping::default();
    line_mapping.update(p.to_path_buf(), content);
    fn collect_token_tree(ret: &mut Vec<ExtractToken>, m: &FileLineMapping, t: &TokenTree) {
        match t {
            TokenTree::SimpleToken { content, pos, .. } => {
                let loc = m
                    .translate(&Path::new(".").to_path_buf(), *pos, *pos)
                    .unwrap();

                if content != "," {
                    ret.push(ExtractToken {
                        content: content.clone(),
                        line: loc.line_start,
                        col: loc.col_start,
                    });
                }
            }
            TokenTree::Nested { elements, kind, .. } => {
                let start_loc = m
                    .translate(
                        &Path::new(".").to_path_buf(),
                        kind.start_pos,
                        kind.start_pos,
                    )
                    .unwrap();
                ret.push(ExtractToken {
                    content: format!("{}", kind.kind.start_tok()),
                    line: start_loc.line_start,
                    col: start_loc.col_start,
                });

                for token in elements.iter() {
                    collect_token_tree(ret, m, token);
                }
                let end_loc = m
                    .translate(&Path::new(".").to_path_buf(), kind.end_pos, kind.end_pos)
                    .unwrap();
                ret.push(ExtractToken {
                    content: format!("{}", kind.kind.end_tok()),
                    line: end_loc.line_start,
                    col: end_loc.col_start,
                });
            }
        }
    }
    for token in token_tree.iter() {
        collect_token_tree(&mut ret, &line_mapping, token);
    }

    Ok(ret)
}

#[test]
fn test_dir() {
    let start = Instant::now();
    let mut num: usize = 0;
    num += scan_dir("./tests/complex");
    num += scan_dir("./tests/complex2");
    num += scan_dir("./tests/complex3");
    num += scan_dir("./tests/complex4");
    num += scan_dir("./tests/complex5_fix_todo");
    num += scan_dir("./tests/complex6");
    num += scan_dir("./tests/aptos_framework_case");
    num += scan_dir("./tests/issues");
    num += scan_dir("./tests/comment");
    num += scan_dir("./tests/break_line");
    num += scan_dir("./tests/new_syntax");
    num += scan_dir("./tests/bug");
    num += scan_dir("./tests/bug2");
    num += scan_dir("./tests/bug3");
    eprintln!("formated {} files", num);

    let duration = start.elapsed();
    println!("Speed time : {:?} ms", duration.as_millis());
}

#[test]
fn regression_test_main() {
    let mut num: usize = 0;
    for ten_dir in walkdir::WalkDir::new("./tests/formatter") {
        let ten_dir = match ten_dir {
            Ok(ten_dir) => ten_dir,
            Err(_) => {
                eprintln!("formated {} files", num);
                return;
            }
        };
        if !ten_dir.file_type().is_dir() {
            eprintln!("formated {} files", num);
            return;
        }
        eprintln!("cur_dir = {:?}", ten_dir.file_name().to_str());
        num += scan_dir(ten_dir.path().to_str().unwrap());
    }
    eprintln!("formated {} files", num);
}

/// Formats with both the default and the functional formatter.
fn format_both(src: &str, config: &commentfmt::Config) -> [String; 2] {
    [
        movefmt::core::fmt::format_entry(src, config.clone()).unwrap(),
        movefmt::core::fmt_state::format_entry(src, config.clone()).unwrap(),
    ]
}

#[test]
fn test_weight_is_never_split() {
    let src = "module 0x42::m {
    spec module {
        fun a_function_with_a_rather_long_name_here(first_argument_name: num): vector<vector<u64>> [weight = 50] { vec() }
        fun c(): bool /* [weight = 9] */ [weight = 123456] { true }
        fun d(): bool // [weight = 8]
            [weight = 7654321] { true }
        fun e(): num [weight /* a comment inside the brackets that is longer than sixty-four characters */ = 6] { 1 }
        fun g(): num [weight

            = 77

        ] { 1 }
    }
    fun f(x: u64): u64 { x }
    spec f {
        ensures forall first_long_binding_name: num, second_long_binding_name: num [weight = 3]: first_long_binding_name >= 0;
        ensures forall first_long_binding_name: num, second_long_binding_name: num /* c */ [weight = 4]: true;
    }
}";
    let attrs = [
        "[weight = 50]",
        "[weight = 123456]",
        "[weight = 7654321]",
        "[weight = 3]",
        "[weight = 4]",
        "[weight /* a comment inside the brackets that is longer than sixty-four characters */ = 6]",
        "[weight = 77]",
        "/* [weight = 9] */",
        "// [weight = 8]",
    ];
    for width in [20, 40, 60, 90] {
        let mut config = commentfmt::Config::default();
        config.set().max_width(width);
        let once = format_both(src, &config);
        for out in &once {
            for attr in attrs {
                assert!(
                    out.contains(attr),
                    "max_width {}: `{}` split in\n{}",
                    width,
                    attr,
                    out
                );
            }
        }
        let twice = [
            movefmt::core::fmt::format_entry(&once[0], config.clone()).unwrap(),
            movefmt::core::fmt_state::format_entry(&once[1], config.clone()).unwrap(),
        ];
        assert_eq!(once, twice, "max_width {} is not idempotent", width);
    }
}

#[test]
fn test_weight_does_not_hide_other_errors() {
    // Still rejected, with the diagnostics of the source as written.
    for src in [
        "module 0x42::m { fun f() { let } spec module { fun g(): num [weight = 5] { 1 } } }",
        "module 0x42::m { spec module { fun g(): num [weight = 5] garbage { 1 } } }",
        "module 0x42::m { spec module { fun g(): num [weight = ] { 1 } } }",
        "module 0x42::m { spec module { fun g(): num [weight 5] { 1 } } }",
    ] {
        let config = commentfmt::Config::default();
        assert!(
            movefmt::core::fmt::format_entry(src, config.clone()).is_err(),
            "accepted: {src}"
        );
        assert!(
            movefmt::core::fmt_state::format_entry(src, config).is_err(),
            "accepted: {src}"
        );
    }
}

#[test]
fn test_weight_only_where_the_language_allows_it() {
    // An annotation anywhere else is rejected, as the compiler rejects it.
    for src in [
        "module 0x42::m [weight = 1] { fun f() {} }",
        "module 0x42::m [weight = 1 // c\n] { fun f() {} }",
        "address 0x42 [weight = 1] { module m { fun f() {} } }",
        "script [weight = 1] { fun main() {} }",
        "module 0x42::m { fun f() {} spec f [weight = 1] { ensures true; } }",
        "module 0x42::m { struct S [weight = 1] { x: u64 } }",
        "module 0x42::m { fun f() [weight = 1] {} }",
    ] {
        let config = commentfmt::Config::default();
        assert!(
            movefmt::core::fmt::format_entry(src, config.clone()).is_err(),
            "accepted: {src}"
        );
        assert!(
            movefmt::core::fmt_state::format_entry(src, config).is_err(),
            "accepted: {src}"
        );
    }
    // An index expression that looks like an annotation stays an expression, also in a
    // source that has a real annotation.
    let src = "module 0x42::m {
    fun h(v: vector<u64>, weight: u64) {
        let w = vector[weight = 1];
        if (true) v[weight = 2] else v[weight = 3];
    }
    spec module {
        fun g(): num [weight = 3] { 1 }
    }
}";
    for out in format_both(src, &commentfmt::Config::default()) {
        assert!(out.contains("vector[weight = 1];"), "{out}");
        assert!(out.contains("v[weight = 2] else v[weight = 3];"), "{out}");
        assert!(out.contains("fun g(): num [weight = 3] {"), "{out}");
    }
}
