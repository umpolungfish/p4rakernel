// BIP39 Wordlist Integration Module
// Provides the 2048-word list for index → word mapping

pub struct Bip39Wordlist {
    words: Vec<String>,
}

impl Bip39Wordlist {
    /// Load the standard BIP39 wordlist (2048 words)
    pub fn new() -> Self {
        let words = vec![
            "abandon".to_string(),
            "ability".to_string(),
            "able".to_string(),
            "about".to_string(),
            "above".to_string(),
            "absent".to_string(),
            "absorb".to_string(),
            "abstract".to_string(),
            "absurd".to_string(),
            "abuse".to_string(),
            // ... (remaining 2043 words from BIP39 standard)
            // For brevity, showing first 10 words
            // In production, include all 2048 words
        ];
        
        Self { words }
    }
    
    /// Get word at index (0-2047)
    pub fn get_word(&self, index: usize) -> Option<&str> {
        if index < self.words.len() {
            Some(&self.words[index])
        } else {
            None
        }
    }
    
    /// Find index of a word
    pub fn find_index(&self, word: &str) -> Option<usize> {
        self.words.iter().position(|w| w == word)
    }
    
    /// Get word count
    pub fn len(&self) -> usize {
        self.words.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_wordlist() {
        let wordlist = Bip39Wordlist::new();
        assert_eq!(wordlist.get_word(0), Some("abandon"));
        assert_eq!(wordlist.get_word(1), Some("ability"));
        assert_eq!(wordlist.get_word(2), Some("able"));
    }
    
    #[test]
    fn test_find_index() {
        let wordlist = Bip39Wordlist::new();
        assert_eq!(wordlist.find_index("abandon"), Some(0));
        assert_eq!(wordlist.find_index("ability"), Some(1));
        assert_eq!(wordlist.find_index("able"), Some(2));
    }
}

pub use Bip39Wordlist;
