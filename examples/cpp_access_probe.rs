//! Inspect bound access evidence: cargo run --example cpp_access_probe -- RECORD FIELD FILE...
use false_sharing_detector::cpp_detection::{
    evidence::collect_cpp_evidence, layout::collect_cpp_structs, parser::parse_cpp_files,
    types::CppFile,
};
use std::{env, fs};

fn main() {
    let mut args = env::args().skip(1);
    let record_name = args.next().expect("record name");
    let field_name = args.next().expect("field name");
    let files = parse_cpp_files(
        args.map(|path| CppFile {
            source: fs::read_to_string(&path).expect("read source"),
            path,
        })
        .collect(),
    );
    let records = collect_cpp_structs(&files, "probe", 64);
    let evidence = collect_cpp_evidence(&files, &records);
    for (record, facts) in records.iter().zip(evidence.iter()) {
        if record.name == record_name || record.qualified_name == record_name {
            println!("{}: {:?}", record.qualified_name, record.fields);
            for item in &facts.items {
                if item.field_name.as_deref() == Some(&field_name) {
                    println!("{item:#?}");
                }
            }
        }
    }
}
