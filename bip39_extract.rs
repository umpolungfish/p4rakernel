// BIP39-to-IMASM Extraction Module for mOMonadOS
// Implements SK extraction from PK via the bijective TSV mapping
// Each BIP39 word maps to a unique 12-glyph IMASM imscription

use std::collections::HashMap;
use std::fs::File;
use std::io::{BufRead, BufReader};

/// BIP39 word to IMASM imscription mapping
pub struct Bip39Extractor {
    word_to_imasm: HashMap<String, String>,
    imasm_to_word: HashMap<String, String>,
}

impl Bip39Extractor {
    /// Load the TSV mapping file
    pub fn from_tsv(path: &str) -> Result<Self, String> {
        let file = File::open(path)
            .map_err(|e| format!("Failed to open TSV file: {}", e))?;
        let reader = BufReader::new(file);
        
        let mut word_to_imasm = HashMap::new();
        let mut imasm_to_word = HashMap::new();
        
        let mut lines = reader.lines();
        
        // Skip header line
        if let Some(Ok(_)) = lines.next() {
            // Skip "word\taddress" header
        }
        
        for line_result in lines {
            let line = line_result.map_err(|e| format!("Read error: {}", e))?;
            let parts: Vec<&str> = line.split('\t').collect();
            
            if parts.len() >= 2 {
                let word = parts[0].trim().to_string();
                let imasm = parts[1].trim().to_string();
                
                word_to_imasm.insert(word.clone(), imasm.clone());
                imasm_to_word.insert(imasm.clone(), word);
            }
        }
        
        if word_to_imasm.is_empty() {
            return Err("No mappings loaded from TSV".to_string());
        }
        
        Ok(Self { word_to_imasm, imasm_to_word })
    }
    
    /// Extract IMASM imscription from BIP39 word
    pub fn word_to_imasm(&self, word: &str) -> Option<String> {
        self.word_to_imasm.get(word).cloned()
    }
    
    /// Extract BIP39 word from IMASM imscription
    pub fn imasm_to_word(&self, imasm: &str) -> Option<String> {
        self.imasm_to_word.get(imasm).cloned()
    }
    
    /// Extract SK from PK using the TSV mapping
    /// PK mod 2048 → BIP39 word → IMASM imscription → SK scalar
    pub fn extract_sk_from_pk(&self, pk: u64) -> Option<(String, String, u64)> {
        // Step 1: PK mod 2048 → BIP39 word index
        let word_index = (pk % 2048) as usize;
        
        // Step 2: Get the word at this index (need wordlist)
        // For now, we'd need the BIP39 wordlist to map index → word
        // This is a placeholder - in production, load the 2048-word list
        
        // Step 3: Word → IMASM imscription (from TSV)
        // Step 4: IMASM imscription → SK scalar (decode the 12 glyphs)
        
        None // Placeholder - requires BIP39 wordlist integration
    }
    
    /// Verify bijectivity of the mapping
    pub fn is_bijective(&self) -> bool {
        let word_count = self.word_to_imasm.len();
        let imasm_count = self.imasm_to_word.len();
        
        // Check for uniqueness
        word_count == imasm_count && word_count > 0
    }
    
    /// Get mapping statistics
    pub fn stats(&self) -> (usize, usize) {
        (self.word_to_imasm.len(), self.imasm_to_word.len())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_tsv_loading() {
        let extractor = Bip39Extractor::from_tsv(
            "/home/mrnob0dy666/imsgct/seekpeek/THIS_bip39_addresses.tsv"
        );
        
        assert!(extractor.is_ok(), "Should load TSV file");
        let ext = extractor.unwrap();
        
        let (word_count, imasm_count) = ext.stats();
        assert_eq!(word_count, imasm_count, "Mapping should be bijective");
        assert!(word_count >= 2048, "Should have all 2048 BIP39 words");
    }
    
    #[test]
    fn test_word_to_imasm() {
        let extractor = Bip39Extractor::from_tsv(
            "/home/mrnob0dy666/imsgct/seekpeek/THIS_bip39_addresses.tsv"
        ).unwrap();
        
        // Test known mappings from TSV
        assert_eq!(
            extractor.word_to_imasm("abandon"),
            Some("⊢⊢⊢⊢◻∋∋∈∈⊣⊥⊤".to_string())
        );
        
        assert_eq!(
            extractor.word_to_imasm("ability"),
            Some("⊢⊢⊢⊢◻⊥⊢⊤⊥◻≻⊞".to_string())
        );
        
        assert_eq!(
            extractor.word_to_imasm("able"),
            Some("⊢⊢⊢⊢⊢⊢⊢⊣⊢⊤⊣≻".to_string())
        );
    }
    
    #[test]
    fn test_imasm_to_word() {
        let extractor = Bip39Extractor::from_tsv(
            "/home/mrnob0dy666/imsgct/seekpeek/THIS_bip39_addresses.tsv"
        ).unwrap();
        
        // Test reverse mapping
        assert_eq!(
            extractor.imasm_to_word("⊢⊢⊢⊢◻∋∋∈∈⊣⊥⊤"),
            Some("abandon".to_string())
        );
    }
    
    #[test]
    fn test_bijectivity() {
        let extractor = Bip39Extractor::from_tsv(
            "/home/mrnob0dy666/imsgct/seekpeek/THIS_bip39_addresses.tsv"
        ).unwrap();
        
        assert!(extractor.is_bijective(), "Mapping should be bijective");
    }
}

// mOMonadOS kernel integration
mod kernel_integration {
    use super::*;
    
    /// Register the BIP39 extractor as a kernel tool
    pub fn register_bip39_extractor() -> Result<Bip39Extractor, String> {
        let extractor = Bip39Extractor::from_tsv(
            "/home/mrnob0dy666/imsgct/seekpeek/THIS_bip39_addresses.tsv"
        )?;
        
        // Verify the mapping is complete and bijective
        let (word_count, imasm_count) = extractor.stats();
        if word_count != imasm_count {
            return Err(format!(
                "Mapping not bijective: {} words, {} imasms",
                word_count, imasm_count
            ));
        }
        
        println!("BIP39 extractor registered: {} word→IMASM mappings", word_count);
        Ok(extractor)
    }
    
    /// Extract SK from PK (main extraction function)
    pub fn extract_sk(pk: u64, extractor: &Bip39Extractor) -> Option<u64> {
        // PK mod 2048 → BIP39 word index
        let word_index = (pk % 2048) as usize;
        
        // In production, this would:
        // 1. Load BIP39 wordlist and get word at word_index
        // 2. Look up word → IMASM imscription from TSV
        // 3. Decode IMASM imscription → SK scalar
        
        // For now, return None as placeholder
        None
    }
}

pub use kernel_integration::{register_bip39_extractor, extract_sk};
