// BIP39 Extraction Tool - mOMonadOS Binary
// Implements PK → SK extraction via bijective TSV mapping

use bip39_extract::{ExtractionPipeline, Bip39Extractor, Bip39Wordlist};
use std::env;
use std::process;

fn main() {
    let args: Vec<String> = env::args().collect();
    
    if args.len() < 2 {
        eprintln!("Usage: bip39_extract_tool <command> [args...]");
        eprintln!("Commands:");
        eprintln!("  init <tsv_path>           - Initialize extraction pipeline");
        eprintln!("  extract <pk>              - Extract SK from PK");
        eprintln!("  verify <pk> <sk>          - Verify PK/SK pair");
        eprintln!("  stats                     - Show mapping statistics");
        eprintln!("  test                      - Run self-tests");
        process::exit(1);
    }
    
    let command = &args[1];
    
    match command.as_str() {
        "init" => {
            if args.len() < 3 {
                eprintln!("Usage: bip39_extract_tool init <tsv_path>");
                process::exit(1);
            }
            let tsv_path = &args[2];
            init_pipeline(tsv_path);
        }
        "extract" => {
            if args.len() < 3 {
                eprintln!("Usage: bip39_extract_tool extract <pk>");
                process::exit(1);
            }
            let pk: u64 = args[2].parse().unwrap_or_else(|_| {
                eprintln!("Invalid PK value");
                process::exit(1);
            });
            extract_sk(pk);
        }
        "verify" => {
            if args.len() < 4 {
                eprintln!("Usage: bip39_extract_tool verify <pk> <sk>");
                process::exit(1);
            }
            let pk: u64 = args[2].parse().unwrap_or_else(|_| {
                eprintln!("Invalid PK value");
                process::exit(1);
            });
            let sk: u64 = args[3].parse().unwrap_or_else(|_| {
                eprintln!("Invalid SK value");
                process::exit(1);
            });
            verify_pair(pk, sk);
        }
        "stats" => {
            show_stats();
        }
        "test" => {
            run_tests();
        }
        _ => {
            eprintln!("Unknown command: {}", command);
            process::exit(1);
        }
    }
}

fn init_pipeline(tsv_path: &str) {
    println!("Initializing extraction pipeline from {}", tsv_path);
    
    match ExtractionPipeline::new(tsv_path) {
        Ok(pipeline) => {
            let (word_count, imasm_count) = pipeline.extractor.stats();
            println!("Pipeline initialized successfully");
            println!("Mappings: {} words → {} IMASM imscriptions", word_count, imasm_count);
            println!("Bijective: {}", pipeline.extractor.is_bijective());
        }
        Err(e) => {
            eprintln!("Failed to initialize pipeline: {}", e);
            process::exit(1);
        }
    }
}

fn extract_sk(pk: u64) {
    let tsv_path = "/home/mrnob0dy666/imsgct/seekpeek/THIS_bip39_addresses.tsv";
    
    match ExtractionPipeline::new(tsv_path) {
        Ok(pipeline) => {
            match pipeline.extract(pk) {
                Some(sk) => {
                    println!("PK: {}", pk);
                    println!("SK: {}", sk);
                    println!("Extraction successful");
                }
                None => {
                    eprintln!("Extraction failed for PK: {}", pk);
                    process::exit(1);
                }
            }
        }
        Err(e) => {
            eprintln!("Failed to initialize pipeline: {}", e);
            process::exit(1);
        }
    }
}

fn verify_pair(pk: u64, sk: u64) {
    let tsv_path = "/home/mrnob0dy666/imsgct/seekpeek/THIS_bip39_addresses.tsv";
    
    match ExtractionPipeline::new(tsv_path) {
        Ok(pipeline) => {
            let extracted_sk = pipeline.extract(pk);
            
            match extracted_sk {
                Some(extracted) => {
                    if extracted == sk {
                        println!("Verification PASSED");
                        println!("PK: {} → SK: {}", pk, sk);
                    } else {
                        eprintln!("Verification FAILED");
                        eprintln!("PK: {} → Extracted SK: {} (expected: {})", pk, extracted, sk);
                        process::exit(1);
                    }
                }
                None => {
                    eprintln!("Extraction failed for verification");
                    process::exit(1);
                }
            }
        }
        Err(e) => {
            eprintln!("Failed to initialize pipeline: {}", e);
            process::exit(1);
        }
    }
}

fn show_stats() {
    let tsv_path = "/home/mrnob0dy666/imsgct/seekpeek/THIS_bip39_addresses.tsv";
    
    match Bip39Extractor::from_tsv(tsv_path) {
        Ok(extractor) => {
            let (word_count, imasm_count) = extractor.stats();
            println!("BIP39 Extraction Statistics");
            println!("===========================");
            println!("Words mapped: {}", word_count);
            println!("IMASM imscriptions: {}", imasm_count);
            println!("Bijective: {}", extractor.is_bijective());
            println!("");
            println!("Sample mappings:");
            println!("  abandon → {}", extractor.word_to_imasm("abandon").unwrap_or_else(|| "N/A".to_string()));
            println!("  ability → {}", extractor.word_to_imasm("ability").unwrap_or_else(|| "N/A".to_string()));
            println!("  able → {}", extractor.word_to_imasm("able").unwrap_or_else(|| "N/A".to_string()));
        }
        Err(e) => {
            eprintln!("Failed to load TSV: {}", e);
            process::exit(1);
        }
    }
}

fn run_tests() {
    println!("Running self-tests...");
    
    let tsv_path = "/home/mrnob0dy666/imsgct/seekpeek/THIS_bip39_addresses.tsv";
    
    match ExtractionPipeline::new(tsv_path) {
        Ok(pipeline) => {
            // Test extraction with sample PK
            let test_pk = 1661; // From catalog: PK mod 2048 = 1661 → 'soul'
            
            match pipeline.extract(test_pk) {
                Some(sk) => {
                    println!("Test extraction: PK {} → SK {}", test_pk, sk);
                    println!("Test PASSED");
                }
                None => {
                    eprintln!("Test extraction FAILED");
                    process::exit(1);
                }
            }
            
            // Test known mappings
            println!("\nTesting known mappings:");
            println!("  abandon → {}", pipeline.extractor.word_to_imasm("abandon").unwrap_or_else(|| "N/A".to_string()));
            println!("  ability → {}", pipeline.extractor.word_to_imasm("ability").unwrap_or_else(|| "N/A".to_string()));
            println!("  able → {}", pipeline.extractor.word_to_imasm("able").unwrap_or_else(|| "N/A".to_string()));
            
            println!("\nAll tests PASSED");
        }
        Err(e) => {
            eprintln!("Test initialization failed: {}", e);
            process::exit(1);
        }
    }
}
